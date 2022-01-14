open Syntax
open Type
open Exception

let acc_through pk1 pk2 =
  match pk1 with
  | PkOwn -> Ok pk2
  | PkRef (rk1, alpha) -> (
      match rk1 with
      | RkMut -> (
          match pk2 with
          | PkOwn -> Ok pk1
          | PkRef (rk2, _) -> Ok (PkRef (rk2, alpha))
          | PkRaw -> Ok PkRaw)
      | RkImmut -> (
          match pk2 with PkOwn | PkRef _ -> Ok pk1 | PkRaw -> Ok PkRaw))
  | PkRaw -> Error "Cannot get access through a raw pointer"

let check_lft_req fn_sign lft_args lft_leq =
  let gemsg = "Lifetime requirements check failed. " in
  match subs_lfts_rel fn_sign.lft_params lft_args fn_sign.lft_req with
  | Error msg ->
      Error
        (gemsg
       ^ "Lifetime substitution in the function lifetime requirements failed. "
       ^ msg)
  | Ok req ->
      if not (List.for_all (fun (l, r) -> LftCtx.is_included lft_leq l r) req)
      then
        Error
          (gemsg
         ^ "The lifetime context does not satisfy function lifetime \
            requirements")
      else Ok ()

let take_params_typs typ_defs var_ctx fn_sign lft_args args =
  let gemsg = "Argument Checks failed. " in
  if List.length fn_sign.params <> List.length args then
    Error
      (gemsg
     ^ "The number of the parameters of function is not the same as the number \
        of provided arguments")
  else
    let pas = List.combine fn_sign.params args in
    let take_param_typ var_ctx ((p, p_typ_syn), arg) =
      match subs_lfts_typ fn_sign.lft_params lft_args p_typ_syn with
      | Error msg ->
          Error
            (gemsg ^ "Lifetime substitution in type of parameter " ^ p
           ^ " failed. " ^ msg)
      | Ok arg_req_typ_syn -> (
          match resolve typ_defs arg_req_typ_syn with
          | Error msg ->
              Error
                (gemsg ^ "Cannot resolve the type of parameter " ^ p ^ ". "
               ^ msg)
          | Ok arg_req_typ -> (
              match VarCtx.take_active_ent var_ctx arg with
              | Error msg -> Error (gemsg ^ msg)
              | Ok (arg_typ, var_ctx_rest) ->
                  if not (arg_req_typ = arg_typ) then
                    Error
                      (gemsg ^ "The parameter " ^ p ^ " and argument " ^ arg
                     ^ " have different types")
                  else Ok var_ctx_rest))
    in
    match Aux.ListAux.try_fold_left take_param_typ var_ctx pas with
    | Error msg -> Error (gemsg ^ "Arguments type checking failed. " ^ msg)
    | Ok var_ctx1 -> Ok var_ctx1

let add_ret_typ typ_defs var_ctx lft_ctx_set fn_sign lft_args y =
  let gemsg = "Adding return type to context failed. " in
  match subs_lfts_typ fn_sign.lft_params lft_args fn_sign.ret with
  | Error msg ->
      Error (gemsg ^ "Lifetime substitution in the return type failed. " ^ msg)
  | Ok ret_typ_syn -> (
      match resolve typ_defs ret_typ_syn with
      | Error msg -> Error (gemsg ^ "Cannot resolve the return type. " ^ msg)
      | Ok ret_typ -> (
          let ent = VarCtx.VceActive (y, ret_typ) in
          match VarCtx.add_ent lft_ctx_set var_ctx ent with
          | Error msg -> Error (gemsg ^ msg)
          | Ok var_ctx1 -> Ok var_ctx1))

let ins_typ_chk ins (var_ctx, ((lfts, lft_leq) as lft_ctx), safety) fn_defs
    typ_defs =
  match ins with
  | InsMutBor (y, lft, x) -> (
      match VarCtx.take_active_ent var_ctx x with
      | Error msg -> Error ("Cannot borrow from " ^ x ^ ": " ^ msg)
      | Ok (t, rest) -> (
          let pk, st = VarCtx.ent_decons_typ t in
          match pk with
          | PkRef (RkImmut, _) ->
              Error ("Cannot reborrow exclusively from shared reference " ^ x)
          | PkRaw -> Error ("Cannot borrow exclusively from raw pointer " ^ x)
          | PkOwn | PkRef (RkMut, _) -> (
              let t_lfts = get_lfts t in
              let is_included = LftCtx.is_included lft_leq in
              if not (List.for_all (fun t_lft -> is_included lft t_lft) t_lfts)
              then
                Error
                  ("To borrow from " ^ x ^ " under lifetime " ^ lft
                 ^ ", it should be included in all the lifetimes which apear \
                    in the type of " ^ x)
              else
                let ents =
                  let open VarCtx in
                  [
                    VceActive (y, TypPtr (PkRef (RkMut, lft), st));
                    VceFrozen (x, lft, t);
                  ]
                in
                match VarCtx.add_ents lfts rest ents with
                | Error msg -> Error msg
                | Ok var_ctx1 -> Ok (var_ctx1, lft_ctx, safety))))
  | InsDrop x -> (
      match VarCtx.take_active_ent var_ctx x with
      | Error msg -> Error ("Cannot drop " ^ x ^ ": " ^ msg)
      | Ok (_, rest) -> Ok (rest, lft_ctx, safety))
  | InsImmut x -> (
      match VarCtx.take_active_ent var_ctx x with
      | Error msg -> Error ("Cannot weak " ^ x ^ ": " ^ msg)
      | Ok (t, rest) -> (
          let pk, st = VarCtx.ent_decons_typ t in
          (fun cont ->
            match pk with
            | PkRef (RkMut, b_lft) -> cont b_lft
            | _ ->
                Error
                  ("The variable " ^ x
                 ^ " is not a mutable reference and therefore cannot be \
                    changed to immutable"))
          @@ fun b_lft ->
          let ent_imm =
            VarCtx.VceActive (x, TypPtr (PkRef (RkImmut, b_lft), st))
          in
          (*** VarCtx.add_ent performs unnecessary checks here.
            But let it be for uniformity in maintenance *)
          match VarCtx.add_ent lfts rest ent_imm with
          | Error msg -> Error msg
          | Ok var_ctx1 -> Ok (var_ctx1, lft_ctx, safety)))
  | InsSwap (x, y) -> (
      let gmsg = "Cannot swap the contents of " ^ x ^ " and " ^ y ^ ": " in
      match VarCtx.take_active_ent var_ctx x with
      | Error msg -> Error (gmsg ^ msg)
      | Ok (xt, _) -> (
          let xpk, xst = VarCtx.ent_decons_typ xt in
          (fun cont ->
            match xpk with
            | PkRef (RkMut, _) -> cont ()
            | _ -> Error (gmsg ^ x ^ " should be a mutable reference"))
          @@ fun () ->
          match VarCtx.take_active_ent var_ctx y with
          | Error msg -> Error (gmsg ^ msg)
          | Ok (yt, _) ->
              let ypk, yst = VarCtx.ent_decons_typ yt in
              (fun cont ->
                match ypk with
                | PkOwn | PkRef (RkMut, _) -> cont ()
                | _ ->
                    Error
                      (gmsg ^ y ^ " should be an owner or a mutable reference"))
              @@ fun () ->
              if xst <> yst then
                Error
                  (gmsg ^ x ^ " and " ^ y
                 ^ " should be pointers to the same pointee type")
              else Ok (var_ctx, lft_ctx, safety)))
  | InsCreateRef (y, x) -> (
      let gmsg = "Cannot create a pointer from " ^ x ^ ": " in
      match VarCtx.take_active_ent var_ctx x with
      | Error msg -> Error (gmsg ^ msg)
      | Ok (t, rest) -> (
          let ent = VarCtx.VceActive (y, TypPtr (PkOwn, t)) in
          match VarCtx.add_ent lfts rest ent with
          | Error msg -> Error (gmsg ^ msg)
          | Ok var_ctx1 -> Ok (var_ctx1, lft_ctx, safety)))
  | InsDeref (y, x) -> (
      let gmsg = "Cannot dereference " ^ x ^ ": " in
      match VarCtx.take_active_ent var_ctx x with
      | Error msg -> Error (gmsg ^ msg)
      | Ok (t, rest) -> (
          let pk, st = VarCtx.ent_decons_typ t in
          (fun cont ->
            match st with
            | TypPtr (spk, sst) -> cont spk sst
            | _ -> Error (gmsg ^ x ^ " should be a pointer to a pointer"))
          @@ fun spk sst ->
          match acc_through pk spk with
          | Error msg -> Error (gmsg ^ msg)
          | Ok pk1 -> (
              let ent = VarCtx.VceActive (y, TypPtr (pk1, sst)) in
              match VarCtx.add_ent lfts rest ent with
              | Error msg -> Error (gmsg ^ msg)
              | Ok var_ctx1 -> Ok (var_ctx1, lft_ctx, safety))))
  | InsCopy (y, x) -> (
      let gmsg = "Cannot make a copy of " ^ x ^ ": " in
      match VarCtx.take_active_ent var_ctx x with
      | Error msg -> Error (gmsg ^ msg)
      | Ok (t, _) -> (
          let pk, st = VarCtx.ent_decons_typ t in
          if not (is_read_acc pk) then
            Error (gmsg ^ "Cannot read from " ^ x ^ " safely")
          else if not (is_copy st) then
            Error
              (gmsg ^ "The type of the pointee of " ^ x
             ^ " is not of Copy trait")
          else
            let ent = VarCtx.VceActive (y, TypPtr (PkOwn, st)) in
            match VarCtx.add_ent lfts var_ctx ent with
            | Error msg -> Error (gmsg ^ msg)
            | Ok var_ctx1 -> Ok (var_ctx1, lft_ctx, safety)))
  | InsTypWeak (x, usyn) -> (
      let gmsg = "Cannot weak the type of " ^ x ^ ": " in
      match VarCtx.take_active_ent var_ctx x with
      | Error msg -> Error (gmsg ^ msg)
      | Ok (t, rest) -> (
          match resolve typ_defs usyn with
          | Error msg -> Error (gmsg ^ msg)
          | Ok u -> (
              if not (is_subtype lft_leq t u) then
                Error
                  (gmsg ^ "The type of " ^ x ^ " is not subtype of "
                 ^ gen_typ_name u)
              else
                let ent = VarCtx.VceActive (x, u) in
                match VarCtx.add_ent lfts rest ent with
                | Error msg -> Error (gmsg ^ msg)
                | Ok var_ctx1 -> Ok (var_ctx1, lft_ctx, safety))))
  | InsFnCall (y, fn_id, lft_args, args) -> (
      let gemsg = "Cannot type check the function call to " ^ fn_id ^ ": " in
      match get_fn_def fn_defs fn_id with
      | Error msg -> Error (gemsg ^ msg)
      | Ok { sign = fn_sign; _ } -> (
          if safety = Safe && fn_sign.safety = Unsafe then
            Error (gemsg ^ "Cannot call an unsafe function in a safe context")
          else
            match check_lft_req fn_sign lft_args lft_leq with
            | Error msg -> Error (gemsg ^ msg)
            | Ok () -> (
                match
                  take_params_typs typ_defs var_ctx fn_sign lft_args args
                with
                | Error msg -> Error (gemsg ^ msg)
                | Ok var_ctx1 -> (
                    match
                      add_ret_typ typ_defs var_ctx1 lfts fn_sign lft_args y
                    with
                    | Error msg -> Error (gemsg ^ msg)
                    | Ok var_ctx2 -> Ok (var_ctx2, lft_ctx, safety)))))
  | _ -> raise exc_not_supported
(***
  | InsIntro of lft
  | InsLftLeq of lft * lft
  | InsNow of lft
  | InsConst of var * conc_vlu
  | InsOp of var * var * op * var
  | InsRand of var
  (* let *y = Tid<alpha_1,...,alpha_n>.i *x *)
  | InsCrEnum of var * typ_syn * inj * var
  (* let *y = Tid<alpha_1,...,alpha_n>{*x_1,...,*x_m} *)
  | InsCrStruct of var * typ_syn * var list
  (* let {*y_1,...,*y_n} = *x *)
  | InsFieldAcc of var list * var
  | InsCrRaw of var * var
  | InsSafe
  | InsUnsafe
  | InsAlloc of var
  | InsDealloc of var
*)

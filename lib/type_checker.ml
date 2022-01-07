open Syntax
open Type
open Exception

let ins_typ_chk ins (var_ctx, ((lfts, lft_leq) as lft_ctx), safety) =
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
  | _ -> raise exc_not_supported
(*
          | InsSwap (x, y) -> Error ""
     | InsCreateRef (lvar, rvar) -> ()
     | InsDeref (lvar, rvar) -> ()
     | InsCopy (lvar, rvar) -> ()
     | InsTypWeak (var, typ) -> ()
     | InsFnCall (var, fn_id, lfts, vars) -> ()
     | InsIntro lft -> ()
     | InsLftLeq (llft, rlft) -> ()
     | InsNow lft -> ()
     | InsConst (var, conc_vlu) -> ()
     | InsOp (lvar, r1var, op, r2var) -> ()
     | InsRand var -> ()
     (* let *y = T.i *x *)
     | InsCrEnum (lvar, typ, inj, rvar) -> ()
     (* let *y = T{*x_1,...,*x_n} *)
     | InsCrStruct (var, typ, vars) -> ()
     (* let {*y_1,...,*y_n} = *x *)
     | InsFieldAcc (vars, rvar) -> ()
     | InsCrRaw (lvar, rvar) -> ()
     | InsSafe -> ()
     | InsUnsafe -> ()
     | InsAlloc var -> ()
     | InsDealloc var -> () *)

(* module Checker = struct

     (**extracts the list of lifetime variables in a type*)
     let typ_lfts ty =
       let rec helper ty lfts =
         match ty with
         | TypUnit | TypInt -> lfts
         | TypPtr (pk, ty') ->
             let lfts' =
               match pk with PkRef (_, lft) -> lft :: lfts | _ -> lfts
             in
             helper ty' lfts'
       in
       helper ty []

     let ins_typ i ((varctx, lftctx) as wctx) =
       match i with
       (*for now we do not have functions so we do not check lftvar not being an external lft*)
       | InsMutBor (lvar, lftvar, rvar) -> (
           match List.assoc_opt rvar varctx with
           | None -> Error FailUndefinedVar
           | Some (ty_giver, lft_freezer) -> (
               match lft_freezer with
               | Some _ -> Error FailBorrowingFrozenVar
               | None -> (
                   (fun cont ->
                     match ty_giver with
                     | TypPtr (pk, ty_pointee) -> cont pk ty_pointee
                     | _ -> Error FailBorrowFromNonPtr)
                   @@ (fun cont pk ty_pointee ->
                        match pk with
                        | PkOwn | PkRef (RkMut, _) -> cont ty_pointee
                        | _ -> Error FailBorrowFromInvPtrKind)
                   @@ fun ty_pointee ->
                   let lftSet, lftPreOrd = lftctx in
                   let lftVar_le lft = List.mem (lftvar, lft) lftPreOrd in
                   let ty_giver_lfts = typ_lfts ty_giver in
                   if not (List.for_all lftVar_le ty_giver_lfts) then
                     Error FailBorrowFromNonCoveringLft
                   else
                     match List.assoc_opt rvar varctx with
                     | Some _ -> Error FailVarNameInUse
                     | None ->
                         let varCtx' =
                           List.map
                             (fun (id, (t, f)) ->
                               if id = rvar then (id, (t, Some lftvar))
                               else (id, (t, f)))
                             varctx
                         in
                         let varCtx'' =
                           ( lvar,
                             (TypPtr (PkRef (RkMut, lftvar), ty_pointee), None) )
                           :: varCtx'
                         in
                         Ok (varCtx'', lftctx))))
       | InsRaw (lvar, rvar) -> Error FailNotSupported
       | InsDrop var -> Error FailNotSupported
       | InsSwap (lvar, rvar) -> Error FailNotSupported
       | InsMkPtr (lvar, rvar) -> Error FailNotSupported
       | InsDeref (lvar, rvar) -> Error FailNotSupported
       | InsCopy (lvar, rvar) -> Error FailNotSupported
       | InsCnst (lvar, vlu) -> Error FailNotSupported
       | InsGhost gi -> (
           match gi with
           | GhImmute var -> Error FailNotSupported
           | GhIntro lft -> Error FailNotSupported
           | GhNow lft -> Error FailNotSupported
           | GhRealize var -> Error FailNotSupported
           | GhUrealize var -> Error FailNotSupported)
   end *)

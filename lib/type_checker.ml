open Syntax
open Type
open Exception
open Aux

let lifetimes_of_typ t =
  let rec helper extracted t =
    match t with
    | TypNat -> extracted
    | TypPtr (pk, t') ->
        let new_ex =
          match pk with
          | PkOwn | PkRaw -> extracted
          | PkRef (_, lft) -> lft :: extracted
        in
        helper new_ex t'
    | TypStruct (_, fts) | TypEnum (_, fts) ->
        List.fold_left helper extracted fts
        | TypRecur of typ_var * typ
    | _ -> raise exc_not_supported
    (*
| TypVar of typ_var
| TypId of typ_id *)
  in
  ()

let get_var_ctx_ent ent =
  match ent with VceActive (var, _) -> var | VceFrozen (var, _, _) -> var

let new_var_chk var var_ctx =
  let f ent = var = get_var_ctx_ent ent in
  if List.exists f var_ctx then
    Error ("The variable name " ^ var ^ " already exists in the context")
  else Ok ()

let ins_typ_chk ins
    ((var_ctx, ((lfts, lft_leq) as lft_ctx), safety) as whole_ctx) =
  match ins with
  | InsMutBor (lvar, lft, rvar) -> (
      match new_var_chk lvar var_ctx with
      | Error msg -> Error msg
      | Ok () -> (
          if not (List.exists (( = ) lft) lfts) then
            Error ("The lifetime " ^ lft ^ " is not going on")
          else
            let f ent = rvar = get_var_ctx_ent ent in
            match ListAux.partition_before_after f var_ctx with
            | _, None, _ ->
                Error ("The Variable " ^ " does not exist in the context")
            | before, Some ent, after -> (
                match ent with
                | VceFrozen (_, fzr_lft, _) ->
                    Error
                      ("The Variable " ^ rvar
                     ^ " is already frozen under lifetime " ^ fzr_lft
                     ^ " and cannot be borrowed")
                | VceActive (_, t) ->
                    let new_var_ctx =
                      VceActive (lvar, TypPtr (PkRef (RkMut, lft), t))
                      :: before
                      @ (VceFrozen (rvar, lft, t) :: after)
                    in
                    Ok (new_var_ctx, lft_ctx, safety))))
  | _ -> raise exc_not_supported
(* | InsDrop var -> ()
   | InsImmut var -> ()
   | InsSwap (lvar, rvar) -> ()
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

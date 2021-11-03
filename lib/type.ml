type ref_kind = RkMut | RkImmut

type ptr_kind =
  | PkOwn
  | PkRef of ref_kind * Id.t
  (*lifetime var*)
  | PkRaw

type typ = TypUnit | TypInt | TypPtr of ptr_kind * typ

type var_ctx = (Id.t * (typ * Id.t option)) (*possibly a borroting lft*) list

type lft_set = Id.t list

type lft_pre_ord = (Id.t * Id.t) list

type lft_ctx = lft_set * lft_pre_ord

type whole_ctx = var_ctx * lft_ctx

module Checker = struct
  module Sym_ins = Machine.Ins.Make (Symbol)
  module Sym_prog = Machine.Prog.Make (Sym_ins)
  open Sym_ins
  open Sym_prog

  type prog_ctx = (label * whole_ctx) list

  type fail =
    | FailNotSupported
    | FailUndefinedVar
    | FailBorrowingFrozenVar
    | FailBorrowFromNonPtr
    | FailBorrowFromInvPtrKind
    | FailUndefinedLft
    | FailBorrowFromNonCoveringLft
    | FailVarNameInUse

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
end

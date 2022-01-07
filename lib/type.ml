(* open Aux *)
open Exception

type var = Id.t

type lft = Id.t

type ref_kind = RkMut | RkImmut

type ptr_kind = PkOwn | PkRef of ref_kind * lft | PkRaw

type typ =
  | TypNat
  | TypPtr of ptr_kind * typ
  | TypStruct of Id.t * typ list
  | TypEnum of Id.t * typ list

let typ_unit = TypStruct ("unit", [])

let typ_empty = TypEnum ("empty", [])

let typ_bool = TypEnum ("bool", [ typ_unit; typ_unit ])

type typ_syn =
  | TypSynNat
  | TypSynPtr of ptr_kind * typ_syn
  | TypSynDef of Id.t * lft list

(*** struct id<lft_1,...,lft_n>{typ_1,...,typ_m} *)
(*** enum id<lft_1,...,lft_n>{typ_1,...,typ_m} *)
type typ_def_body =
  | TdbStruct of lft list * typ_syn list
  | TdbEnum of lft list * typ_syn list

type typ_def = Id.t * typ_def_body

let td_unit = ("unit", TdbStruct ([], []))

let td_empty = ("empty", TdbEnum ([], []))

let td_bool =
  ("bool", TdbEnum ([], [ TypSynDef ("unit", []); TypSynDef ("unit", []) ]))

let reserved_typ_defs = [ td_unit; td_empty; td_bool ]

let typ_syn_unit = TypSynDef ("unit", [])

let typ_syn_empty = TypSynDef ("empty", [])

let typ_syn_bool = TypSynDef ("bool", [])

type safety = Safe | Unsafe

let get_lfts t =
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
  in
  helper [] t

(*
   let gen_rk_name = function RkImmut -> "imm" | RkMut -> "mut"

   let gen_pk_name = function
     | PkOwn -> "own"
     | PkRef (rk, lft) -> gen_rk_name rk ^ "'" ^ lft
     | PkRaw -> "raw"

   let rec gen_typ_name_sep sopen sclose t =
     let gen_typ_name = gen_typ_name_sep sopen sclose in
     match t with
     | TypNat -> "nat"
     | TypPtr (pk, t') -> gen_pk_name pk ^ sopen ^ gen_typ_name t' ^ sclose
     | TypStruct (id, _) -> "struct " ^ id
     | TypEnum (id, _) -> "enum " ^ id

   let gen_typ_name = gen_typ_name_sep "(" ")"

   let get_td_id = function TdStruct (id, _, _) | TdEnum (id, _, _) -> id

   let find_td tdefs t =
     match t with
     | TypNat | TypPtr _ ->
         raise (Excp (SevBug, "Attemp to find definition for " ^ gen_typ_name t))
     | TypStruct (id, lft_args) -> (
         match List.find_opt (fun ent -> id = get_td_id ent) tdefs with
         | None -> Error ("Cannot find any type definition for " ^ id)
         | Some td -> (
             match td with
             | TdEnum _ ->
                 Error ("The type definition for " ^ id ^ " is not a struct")
             | TdStruct (_, lft_params, _) ->
                 if not (List.length lft_params = List.length lft_args) then
                   Error
                     "The number of lifetime parameters and lifetime arguments do \
                      not match"
                 else Ok td))
     | TypEnum (id, lft_args) -> (
         match List.find_opt (fun ent -> id = get_td_id ent) tdefs with
         | None -> Error ("Cannot find any type definition for " ^ id)
         | Some td -> (
             match td with
             | TdStruct _ ->
                 Error ("The type definition for " ^ id ^ " is not an emum")
             | TdEnum (_, lft_params, _) ->
                 if not (List.length lft_params = List.length lft_args) then
                   Error
                     "The number of lifetime parameters and lifetime arguments do \
                      not match"
                 else Ok td))

   let rec size_of tdefs t =
     match t with
     | TypNat | TypPtr _ -> Ok 1
     | TypStruct _ ->
         (fun cont ->
           match find_td tdefs t with
           | Error m -> Error m
           | Ok (TdStruct (_, _, fts)) -> cont fts
           | _ -> raise exc_should_not_happen)
         @@ fun fts ->
         let fsum s ent =
           match size_of tdefs ent with Error m -> Error m | Ok s' -> Ok (s + s')
         in
         ListAux.try_fold_left fsum 0 fts
     | TypEnum _ -> raise exc_not_supported*)

module LftCtx = struct
  type leq_rel = (lft * lft) list

  type t = lft list * leq_rel

  let is_alive lfts lft = List.exists (( = ) lft) lfts

  let is_included lft_leq lft1 lft2 = List.exists (( = ) (lft1, lft2)) lft_leq
end

module VarCtx = struct
  type entry = VceActive of var * typ | VceFrozen of var * lft * typ

  type t = entry list

  let ent_get_var ent =
    match ent with VceActive (var, _) | VceFrozen (var, _, _) -> var

  let take_ent var_ctx var =
    match List.partition (fun e -> var = ent_get_var e) var_ctx with
    | [], _ -> Error ("The variable " ^ var ^ " does not exist in the context")
    | [ ent ], rest -> Ok (ent, rest)
    | _ ->
        raise
          (Excp
             ( SevFatal,
               "Redundant entries in variable context for the same variable \
                name" ^ var ))

  let take_active_ent var_ctx var =
    match take_ent var_ctx var with
    | Error msg -> Error msg
    | Ok (ent, rest) -> (
        match ent with
        | VceFrozen (_, frz_lft, _) ->
            Error
              ("The variable " ^ var ^ " is frozen under lifetime " ^ frz_lft)
        | VceActive (_, t) -> Ok (t, rest))

  let ent_decons_typ t =
    match t with
    | TypPtr (pk, st) -> (pk, st)
    | _ -> raise (Excp (SevFatal, "Non-pointer type in variable context"))

  let add_ent lfts var_ctx ent =
    let var = ent_get_var ent in
    let f e = var = ent_get_var e in
    if List.exists f var_ctx then
      Error ("The variable name " ^ var ^ " already exists in the context")
    else
      match ent with
      | VceActive _ -> Ok (ent :: var_ctx)
      | VceFrozen (_, lft, _) ->
          if not (LftCtx.is_alive lfts lft) then
            Error ("The lifetime " ^ lft ^ " is not going on")
          else Ok (ent :: var_ctx)

  let add_ents lfts var_ctx ents =
    let add_ent = add_ent lfts in
    Aux.ListAux.try_fold_right add_ent var_ctx ents
end

type whole_ctx = VarCtx.t * LftCtx.t * safety

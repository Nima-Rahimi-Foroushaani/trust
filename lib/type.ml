open Aux
open Exception

type var = Id.t

type lft = Id.t

type ref_kind = RkMut | RkImmut

type ptr_kind = PkOwn | PkRef of ref_kind * lft | PkRaw

type typ =
  | TypNat
  | TypPtr of ptr_kind * typ
  | TypStruct of Id.t * lft list
  | TypEnum of Id.t * lft list

type typ_def =
  (*** struct id<lft_1,...,lft_n>{typ_1,...,typ_m} *)
  | TdStruct of Id.t * lft list * typ list
  (*** enum id<lft_1,...,lft_n>{typ_1,...,typ_m} *)
  | TdEnum of Id.t * lft list * typ list

let td_unit = TdStruct ("unit", [], [])

let td_empty = TdEnum ("empty", [], [])

let typ_unit = TypStruct ("unit", [])

let typ_empty = TypEnum ("empty", [])

let td_bool = TdEnum ("bool", [], [ typ_unit; typ_unit ])

let typ_bool = TypEnum ("bool", [])

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
  | TypEnum _ -> raise exc_not_supported

type var_ctx_entry = VceActive of var * typ | VceFrozen of var * lft * typ

type var_ctx = var_ctx_entry list

type lft_leq_rel = (lft * lft) list

type lft_ctx = lft list * lft_leq_rel

type safety = Safe | Unsafe

type whole_ctx = var_ctx * lft_ctx * safety

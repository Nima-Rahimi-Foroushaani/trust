type vlu = VluProd of Id.t * (Id.t * vlu) list | VluLoc of Symbol.t

let unit_v = VluProd (Id.make "unit", [])

type mutability = MtImm | MtMut

type st_type =
  | StTypProd of Id.t * (Id.t * st_type) list
  | StTypRef of mutability * st_type
  | StTypRawPtr of mutability * st_type

let unit_st = StTypProd (Id.make "unit", [])

type predicate = PrdTrue | PrdFalse

type ghlost_term = GtRealize of Id.t | GtUnRealize of Id.t

type term =
  | TmVal of vlu
  | TmVar of Id.t
  | TmDref of term
  | TmRef of mutability * term
  | TmLet of mutability * Id.t * st_type * term
  | TmSeq of term * term
  | TmGhost of ghlost_term

type fn_rep = { pre : predicate; post : predicate }

type st_ctx = (Id.t * st_type) list

type fn_def = { name : string; rep : fn_rep; params : st_ctx; body : term }

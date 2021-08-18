type vlu =
  | VluInt of Symbol.t
  | VluLoc of Symbol.t
  | VluProd of Id.t * (Id.t * vlu) list

let vlu_unit = VluProd (Id.make "unit", [])

type mutability = MtImm | MtMut

type st_type =
  | StTypInt
  | StTypRef of mutability * st_type
  | StTypRawPtr of mutability * st_type
  | StTypProd of Id.t * (Id.t * st_type) list

let stt_unit = StTypProd (Id.make "unit", [])

type proposition = PropTrue | PropFalse

type ghost_term = GtRealize of Id.t | GtUnRealize of Id.t

type term =
  | TmVal of vlu
  | TmVar of Id.t
  | TmLet of mutability * Id.t * st_type * term * term
  | TmInLet of Id.t * term
  | TmFin of term * term
  | TmDrop of term
  | TmAssign of term * term
  | TmRef of mutability * term
  | TmDref of term
  | TmProd of Id.t * (Id.t * term) list
  | TmSeq of term * term
  | TmGhost of ghost_term

type fn_rep = { pre : proposition; post : proposition }

type st_ctx = (Id.t * st_type) list

type fn_def = { name : Id.t; rep : fn_rep; params : st_ctx; body : term }

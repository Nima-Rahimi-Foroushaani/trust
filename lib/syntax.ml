open Type

type op_arith = Add | Sub

type op_bool = Eq | Neq | Geq

type op = OpArith of op_arith | OpBool of op_bool

type conc_nat = int

type conc_vlu = CvNat of conc_nat | CvPoison

type sym_nat_expr =
  | SneConc of conc_nat
  | SneSym of Symbol.t
  | SneArith of sym_nat_expr * op_arith * sym_nat_expr

type sym_vlu = SvNat of sym_nat_expr

type vlu = VSym of sym_vlu | VConc of conc_vlu

type label = Id.t

type var = Id.t

type lft = Type.lft

type fn_id = Id.t

type safety = Safe | Unsafe

type fn_sign = {
  safety : safety;
  lft_params : lft list;
  lft_req : (lft * lft) list;
  params : (var * typ) list;
  ret : typ;
}

type typ = Type.typ

type inj = conc_nat

type ins =
  | InsMutBor of var * lft * var
  | InsDrop of var
  | InsImmut of var
  | InsSwap of var * var
  | InsCreateRef of var * var
  | InsDeref of var * var
  | InsCopy of var * var
  | InsTypWeak of var * typ
  | InsFnCall of var * fn_id * lft list * var list
  | InsIntro of lft
  | InsLftLeq of lft * lft
  | InsNow of lft
  | InsConst of var * conc_vlu
  | InsOp of var * var * op * var
  | InsRand of var
  (* let *y = id.i *x *)
  | InsCrEnum of var * Id.t * inj * var
  (* let *y = id{*x_1,...,*x_n} *)
  | InsCrStruct of var * Id.t * var list
  (* let *y_1,...,*y_n = *x *)
  | InsFieldAcc of var list * var
  | InsCrRaw of var * var
  | InsSafe
  | InsUnsafe
  | InsAlloc of conc_nat
  | InsDealloc of var

type statement =
  | StIns of ins * label
  | StRet of var
  (* match *x {*y_0 => goto L_0,..., *y_n => goto L_n} *)
  | StMatch of var * (var * label) list

type fn_body = (label * statement) list

type fn_def = { id : fn_id; sign : fn_sign; body : fn_body }

type typ_defs = typ list

type fn_defs = fn_def list

type program = typ_defs * fn_defs

(**represents the simplest value, supported by our abstract machine.
  In a symbolic machine, of course it would be a symbol.
  In a concrete machine, it can be a simple integer for example*)

module type BASE_VALUE = sig
  type t

  val ( = ) : t -> t -> bool
end

module Ins = struct
  module type S = sig
    type vlu

    type ins
  end

  module Make =
  functor
    (BV : BASE_VALUE)
    ->
    struct
      type base_vlu = BV.t

      type vlu = VluUnit | VluInt of base_vlu

      type ghost_ins =
        | GhImmute of Id.t
        | GhIntro of Id.t
        | GhNow of Id.t
        | GhRealize of Id.t
        | GhUrealize of Id.t

      type ins =
        | InsMutBor of Id.t * Id.t * Id.t
        | InsRaw of Id.t * Id.t
        | InsDrop of Id.t
        | InsSwap of Id.t * Id.t
        | InsMkPtr of Id.t * Id.t
        | InsDeref of Id.t * Id.t
        | InsCopy of Id.t * Id.t
        | InsCnst of Id.t * vlu
        | InsGhost of ghost_ins
    end
end

module Prog = struct
  module type S = sig
    type label = int

    type ins

    type prog = ins list
  end

  module Make =
  functor
    (I : Ins.S)
    ->
    struct
      type label = int

      type ins = I.ins

      type prog = ins list
    end
end

module CodeInfo = struct
  type t = { f : string; l : int; cb : int; ce : int }
end

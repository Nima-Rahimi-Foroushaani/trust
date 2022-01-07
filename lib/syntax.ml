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

type fn_id = Id.t

type fn_sign = {
  safety : safety;
  lft_params : lft list;
  lft_req : (lft * lft) list;
  params : (var * typ_syn) list;
  ret : typ_syn;
}

type inj = conc_nat

type ins =
  | InsMutBor of var * lft * var
  | InsDrop of var
  | InsImmut of var
  | InsSwap of var * var
  | InsCreateRef of var * var
  | InsDeref of var * var
  | InsCopy of var * var
  | InsTypWeak of var * typ_syn
  | InsFnCall of var * fn_id * lft list * var list
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

type statement =
  | StIns of ins * label
  | StRet of var
  (* match *x {*y_0 => goto L_0,...,*y_n => goto L_n} *)
  | StMatch of var * (var * label) list

type fn_body = (label * statement) list

type fn_def = { id : fn_id; sign : fn_sign; body : fn_body }

type typ_defs = typ_def list

type fn_defs = fn_def list

type program = typ_defs * fn_defs

type id = string
type mem_loc = string

type mutability =
   MtImm
   |MtMut

   (* @todo add a data structure which prevents duplicate keys but similar to assoc list preserves the order *)
type typ =
   TypProd of id * (id * typ) list
   |TypLoc
let typ_unit = TypProd("Unit", [])

type vlu =
   VluProd of id * (id * vlu) list
   |VluLoc of mem_loc
let vlu_unit = VluProd("unit", [])

type term =
   TmVal of vlu
   |TmVar of id
   |TmDref of term
   |TmLet of mutability * id * typ * term
   |TmSeq of term * term

type mem_grd = {rd:int; wr:int}

type sym_store = (id * mem_loc) list
type sym_mem_stage = (mem_loc * vlu) list
type sym_exe_ctx = sym_store * sym_mem_stage

type stuck =
   StkUnboundVar
   | StkNpermAcs
   | StkUndefBeh
   | StkNotSupp

type exec_rsl =
   ExRslProgress
   |ExRslVlu
   |ExRslStuk of stuck

let rec sym_exec_step t ((sstore, smstage) as sctx:sym_exe_ctx) =
match t with
| TmVal(_) -> ExRslVlu, t, sctx
| TmVar(n) -> (
   match List.assoc_opt n sstore with
   | Some(l) -> ExRslProgress, TmDref(TmVal(VluLoc(l))), sctx
   | None -> ExRslStuk(StkUnboundVar), t, sctx
   )
| TmDref(t1) -> (
   match (t1) with
   | TmVal(VluLoc(l)) -> (
      match List.assoc_opt l smstage with
      | Some(v) -> ExRslProgress, TmVal(v), sctx
      | None -> ExRslStuk(StkNpermAcs), t, sctx
      )
   | TmVal(_) -> ExRslStuk(StkUndefBeh), t, sctx
   | _ -> let (rsl, t1', sctx') = sym_exec_step (t1) sctx in (rsl, TmDref(t1'), sctx')
   )
| TmLet(mty, n, ty, t1) -> (
   match t1 with
   (*todo: fresh symbol, check name for duplicate*)
   | TmVal(v) -> ExRslProgress, TmVal(vlu_unit), let l = "l" in ((n, l)::sstore, (l, v)::smstage)
   | _ -> let (rsl, t1', sctx') = sym_exec_step t1 sctx in (rsl, TmLet(mty, n, ty, t1'), sctx')
)
| TmSeq(t1, t2) -> (
   match t1 with
   | TmVal(_) -> ExRslProgress, t2, sctx
   | _ -> let (rsl, t1', sctx') = sym_exec_step t1 sctx in (rsl, TmSeq(t1', t2), sctx')
)
(*| _ -> ExRslStuk(StkNotSupp), t,sctx*)

(*let main() = 
Printf.printf "tRust 1.0.0\n";
Printf.printf "Powered By VeriFast\n";
*)
let simple_imm_ref_read =
   TmSeq(
      TmLet(MtImm, "x", typ_unit, TmVal(vlu_unit)),
      TmVar("x")
   )
;;

sym_exec_step simple_imm_ref_read ([], [])

(*exit 0;;
main();;*)
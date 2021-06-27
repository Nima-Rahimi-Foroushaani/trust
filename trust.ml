module type NAME = sig
   val create_name: string -> int -> string
end

module Name: NAME = struct
   (** Creates a name based on a provided base name, and an index*)
   let create_name bn idx =
      let idx_str = match idx with
                  | 0 -> ""
                  | _ when idx > 0 -> "_" ^ string_of_int idx
                  | _ -> raise (invalid_arg "Negative index")
      in bn ^ idx_str
end

module type SYMBOL = sig
   type t
   val make: string -> t
   val name: t -> string
end

module Symbol = struct
   type t = {
      (** symbol unique name *)
      name: string;
   }

   let make n = {name=n}
   let name s = s.name
end

module type ID = sig
   type t
   val make: string -> t
   val name: t -> string
end

module Id = struct
   type t = {
      name: string
   }

   let make n = {name= n}
   let name t = t.name
end

module Ast = struct
   type vlu =
   VluProd of Id.t * (Id.t * vlu) list
   | VluLoc of Symbol.t

let unit_v = VluProd(Id.make "unit", [])

type mutability = MtImm | MtMut

type st_type =
   StTypProd of Id.t * (Id.t * st_type) list
   | StTypRef of mutability * st_type
   | StTypRawPtr of mutability * st_type

let unit_st = StTypProd(Id.make "unit", [])

type predicate =
   PrdTrue
   | PrdFalse

type ghlost_term = 
   GtRealize of Id.t
   | GtUnRealize of Id.t

type term =
   TmVal of vlu
   | TmVar of Id.t
   | TmDref of term
   | TmRef of mutability * term
   | TmLet of mutability * Id.t * st_type * term
   | TmSeq of term * term
   | TmGhost of ghlost_term

type fn_rep = {
   pre: predicate;
   post: predicate;
}

type st_ctx = (Id.t * st_type) list

type fn_def = {
   name: string;
   rep: fn_rep;
   params: st_ctx;
   body: term;
}

end

module Exe = struct

   type rt_type =
      RtTypProd of Id.t * (Id.t * rt_type) list
      |RtTypPtr


   type perm = PermDel | PermWr | PermRd | PermDen

   let weight = function
   | PermDen ->   0
   | PermRd ->    1
   | PermWr ->    2
   | PermDel ->   3

   let (<) a b = weight a < weight b
   let (>=) a b = weight a >= weight b
   
   type sym_store = (Id.t * Symbol.t) list
   type sym_mem = (Symbol.t * (Ast.vlu * perm)) list
   type sym_ctx = sym_store * sym_mem

   let rec is_sym_used_vlu sym v =
      let open Ast in
      match v with
      | VluProd(id, elms) -> begin
         match elms with
         | [] -> false
         | (_, v1)::tail -> is_sym_used_vlu sym v1 || let v' = VluProd(id, tail) in is_sym_used_vlu sym v'
      end
      | VluLoc(l) -> sym = l
   let rec is_sym_used_smem sym smem =
      match smem with
      | [] -> false
      | (l, (v, _))::tail -> sym = l || is_sym_used_vlu sym v || is_sym_used_smem sym tail
   
   let rec is_sym_used_sstore sym sstore =
      match sstore with
      | [] -> false
      | (_, l)::tail -> sym = l || is_sym_used_sstore sym tail

   let fresh sctx bn =
      let rec fresh_h ((sstore, smem) as sctx) bn idx =
         let str = "_" ^ Name.create_name bn idx in
         let sym = Symbol.make str in
         if is_sym_used_sstore sym sstore || is_sym_used_smem sym smem then
            let idx' = idx+1 in fresh_h sctx bn idx'
         else
            sym
         in
         fresh_h sctx bn 0
   
   type stuck =
      StkUnboundVar
      | StkNpermAcs
      | StkUndefBeh
      | StkCtxMismatch
      | StkCtxCorrupt
      | StkNotSupp
   
   type exec_rsl =
      ExRslProgress
      | ExRslVlu
      | ExRslStuk of stuck

   let translate_mut_perm mt = 
      let open Ast in
      match mt with
      | MtImm -> PermRd
      | MtMut -> PermWr
   
   let rec produce_val_of_sttyp ((systore, symem) as syctx) sttyp =
      let open Ast in
      match sttyp with
      | StTypRef(_, _)
      | StTypRawPtr(_, _) -> VluLoc(fresh syctx "loc")
      | StTypProd(id, elm_sttyps) -> begin
         match elm_sttyps with
         | [] -> VluProd(id, [])
         | (eid, est)::tail -> begin
            let ev = produce_val_of_sttyp syctx est in
            let dummy_sym = Symbol.make "" in
            let symmem' = (dummy_sym, (ev, PermDen))::symem in
            match produce_val_of_sttyp (systore, symmem') (StTypProd(id, tail)) with
            | VluProd(_, evs) -> VluProd(id, (eid, ev)::evs)
            | _-> assert false
         end
      end

   let initial_symctx params =
      let rec initial_symctx_h params ((sstore, smem) as symctx) =
         match params with
         | [] -> symctx
         | (id, sttyp)::tail ->
            let bn = Id.name id in
            let l = fresh symctx bn in
            let sstore' = (id, l)::sstore in
            let v = produce_val_of_sttyp (sstore', smem) sttyp in
            let symctx' = (sstore', (l, (v, PermDel))::smem) in
         initial_symctx_h tail symctx'
         in
      initial_symctx_h params ([], [])

   let realize id (stctx:Ast.st_ctx) ((systore, symem) as syctx:sym_ctx) rl_hist =
      match List.assoc_opt id stctx with
      | None -> ExRslStuk(StkUnboundVar), syctx, rl_hist
      | Some(sttyp_id) -> begin
         let open Ast in
         match sttyp_id with
         | StTypProd(_, _)
         | StTypRawPtr(_) -> ExRslStuk(StkUndefBeh), syctx, rl_hist
         | StTypRef(mt, sttyp_pointee) -> begin
            let perm_pointee = translate_mut_perm mt in
            match List.assoc_opt id systore with
            | None -> ExRslStuk(StkCtxMismatch), syctx, rl_hist
            | Some(l) -> begin
               match List.assoc_opt l symem with
               | None -> ExRslStuk(StkCtxCorrupt), syctx, rl_hist
               | Some(v, ref_perm) ->
                  if ref_perm  < PermRd then
                     ExRslStuk(StkNpermAcs), syctx, rl_hist
                  else begin
                     match v with
                     | VluProd(_, _) -> ExRslStuk(StkCtxMismatch), syctx, rl_hist
                     | VluLoc(l_pointee) -> begin
                     let sym_mem' = (l_pointee, (produce_val_of_sttyp syctx sttyp_pointee, perm_pointee))::symem in
                     let rl_hist' = id::rl_hist in
                     ExRslProgress, (systore, sym_mem'), rl_hist'
                  end
               end
            end
         end
      end
   let unrealize (id, styp) ((sstore, smem) as sctx) =
      true

   let rec sym_exe_step t ((systore, symem) as syctx:sym_ctx) (stctx:Ast.st_ctx) rlhist =
      let open Ast in
      match t with
      | TmVal(_) -> ExRslVlu, t, syctx, stctx, rlhist
      | TmVar(id) -> begin
         match List.assoc_opt id systore with
         | None -> ExRslStuk(StkUnboundVar), t, syctx, stctx, rlhist
         | Some(l) -> ExRslProgress, TmDref(TmVal(VluLoc(l))), syctx, stctx, rlhist
      end
      | TmDref(t1) -> begin
         match t1 with
         | TmVal(v) -> begin
            match v with
               | VluLoc(l) -> begin
                  match List.assoc_opt l symem with
                  | Some(v', p) when p >= PermRd -> ExRslProgress, TmVal(v'), syctx, stctx, rlhist
                  | _ -> ExRslStuk(StkNpermAcs), t, syctx, stctx, rlhist
               end
               | _ -> ExRslStuk(StkUndefBeh), t, syctx, stctx, rlhist
         end
         | _ -> begin
            let (rsl, t1', syctx', stctx', rlhist') = sym_exe_step t1 syctx stctx rlhist in
            rsl, TmDref(t1'), syctx', stctx', rlhist'
         end
      end
      | TmRef(_, t1) -> begin
         (** @todo: study and represent the behavior of poly-referenced references*)
         match t1 with
         | TmVar(id) -> begin
            match List.assoc_opt id systore with
            | None -> ExRslStuk(StkUnboundVar), t, syctx, stctx, rlhist
            | Some(l) -> ExRslProgress, TmVal(VluLoc(l)), syctx, stctx, rlhist
         end
         | _ -> ExRslStuk(StkUndefBeh), t, syctx, stctx, rlhist
      end
      | TmLet(mt, id, sttyp, t1) -> begin
         match t1 with
         | TmVal(v) ->
            let n = Id.name id in
            let l = fresh syctx n in
            let systore' = (id, l)::systore in
            let symem' = (l, (v, PermDel))::symem in
            let stctx' = (id, sttyp)::stctx in
            ExRslProgress, TmVal(unit_v),  (systore', symem'), stctx', rlhist
         | _ -> begin
            let (rsl, t1', syctx', stctx', rlhist') = sym_exe_step t1 syctx stctx rlhist in
            rsl, TmLet(mt, id, sttyp, t1'), syctx', stctx', rlhist'
         end
      end
      | TmSeq(t1, t2) -> begin
         match t1 with
         (** @todo: handle values of Drop trait*)
         | TmVal(_) -> ExRslProgress, t2, syctx, stctx, rlhist
         | _ ->
            let (rsl, t1', syctx', stctx', rlhist') = sym_exe_step t1 syctx stctx rlhist in
            rsl, TmSeq(t1', t2), syctx', stctx', rlhist'
      end
      | TmGhost(gt) -> begin
         match(gt) with
         | GtRealize(id) ->
            let (rsl, syctx', rlhist') = realize id stctx syctx rlhist in
            let t' = if rsl = ExRslProgress then TmVal(unit_v) else t in
            rsl, t', syctx', stctx, rlhist'
         | GtUnRealize(_) -> ExRslStuk(StkNotSupp), t, syctx, stctx, rlhist
      end

      let rec sym_exe t syctx stctx rlhist = 
         let (rsl, t', syctx', stctx', rlhist') as ret = sym_exe_step t syctx stctx rlhist in
         match rsl with
         | ExRslProgress -> sym_exe t' syctx' stctx' rlhist'
         | ExRslVlu
         | ExRslStuk(_) -> ret
end

module Verification = struct
let verify f =
   let open Ast in
   let open Exe in
   let syctx = initial_symctx f.params in
   sym_exe f.body syctx f.params []
end

open Ast
open Exe
let var_read =
   TmSeq begin
      TmLet(MtImm, Id.make "x", unit_st, TmVal(unit_v)),
      TmVar(Id.make "x")
   end

let imm_ref =
   TmSeq begin
      TmLet(MtImm, Id.make "x", unit_st, TmVal(unit_v)),
      TmSeq begin
         TmLet(MtImm, Id.make "xr", StTypRef(MtImm, unit_st), TmRef(MtImm, TmVar(Id.make "x"))),
         TmDref(TmVar(Id.make "xr"))
      end
   end

let unsafe_deref_fn_fail = {
   name= "unsafe_deref_fn";
   rep= {pre=PrdTrue; post=PrdTrue};
   params = (Id.make "x", StTypRef(MtImm, unit_st))::[];
   body =
   TmSeq begin
      TmLet(MtImm, Id.make "ptr", StTypRawPtr(MtImm, unit_st), TmVar(Id.make "x")),
      TmDref(TmVar(Id.make "ptr"))
   end
}

let unsafe_deref_fn_pass = {
   name= "unsafe_deref_fn";
   rep= {pre=PrdTrue; post=PrdTrue};
   params = (Id.make "x", StTypRef(MtImm, unit_st))::[];
   body =
   TmSeq begin
      TmLet(MtImm, Id.make "ptr", StTypRawPtr(MtImm, unit_st), TmVar(Id.make "x")),
      TmSeq begin
         TmGhost(GtRealize(Id.make "x")),
         TmDref(TmVar(Id.make "ptr"))
      end
   end
}
;;
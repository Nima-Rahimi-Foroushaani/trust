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

let unit_st = StTypProd(Id.make "Unit", [])

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

type fn_rep = {
   pre: predicate;
   post: predicate;
}

type fn_param = Id.t * st_type

type fn_def = {
   name: string;
   rep: fn_rep;
   params: fn_param list;
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
      | StkCurrCtx
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
   
   let rec produce_val_of_sttyp sctx sttyp =
      let open Ast in
      match sttyp with
      | StTypProd(id, elm_sttyps) ->
         let (ids, typs) = List.split elm_sttyps in
         let vals = List.map (produce_val_of_sttyp sctx) typs in
         let elms = List.combine ids vals in
         VluProd(id, elms)
      | StTypRef(_, _)
      | StTypRawPtr(_, _) -> VluLoc(fresh sctx "loc")

   let initial_ctx params =
      let rec initial_ctx_h params ((sstore, smem) as sctx) =
         match params with
         | [] -> sctx
         | (id, sttyp)::tail ->
            let bn = Id.name id in
            let l = fresh sctx bn in
            let sstore' = (id, l)::sstore in
            let v = produce_val_of_sttyp (sstore', smem) sttyp in
            let sctx' = (sstore', (l, (v, PermDel))::smem) in
         initial_ctx_h tail sctx'
         in
      initial_ctx_h params ([], [])

   let realize (id, styp) ((sstore, smem) as sctx) rl_history =
      match List.find_opt ((=) id) rl_history with
      (*It has already been realized*)
      | Some(_) -> ExRslProgress, sctx, rl_history
      | None -> begin
         match List.assoc_opt id sstore with
         | Some(l) -> begin
            match List.assoc_opt l smem with
            | Some(v, perm) -> begin
               let open Ast in
               match v with
               | VluLoc(l1) when perm = PermDel -> begin
                  match styp with
                  | StTypRef(mt, styp1) -> let rl_perm = translate_mut_perm mt in
                  ExRslProgress, (sstore, (l1,(produce_val_of_sttyp sctx styp1,rl_perm))::smem), id::rl_history
                  | _ -> ExRslStuk(StkUndefBeh), sctx, rl_history
               end
               | _ -> ExRslStuk(StkCurrCtx) , sctx, rl_history
            end
            | None -> ExRslStuk(StkCurrCtx), sctx, rl_history
         end
         | None -> ExRslStuk(StkUnboundVar), sctx, rl_history
      end

   let unrealize (id, styp) ((sstore, smem) as sctx) =
      true
   
   let rec sym_exe_step t ((sstore, smem) as sctx:sym_ctx) =
      let open Ast in
      match t with
      | TmVal(_) -> ExRslVlu, t, sctx
      | TmVar(id) -> begin
         match List.assoc_opt id sstore with
         | Some(l) -> ExRslProgress, TmDref(TmVal(VluLoc(l))), sctx
         | None -> ExRslStuk(StkUnboundVar), t, sctx
      end
      | TmDref(t1) -> begin
         match t1 with
         | TmVal(v) -> begin
            match v with
               | VluLoc(l) -> begin
                  match List.assoc_opt l smem with
                  | Some(v', p) when p >= PermRd -> ExRslProgress, TmVal(v'), sctx
                  | _ -> ExRslStuk(StkNpermAcs), t, sctx
               end
               | _ -> ExRslStuk(StkUndefBeh), t, sctx
         end
         | _ -> let (rsl, t1',sctx') = sym_exe_step t1 sctx in rsl, TmDref(t1'), sctx'
      end
      | TmRef(_, t1) -> begin
         (** @todo: study and represent the behavior of poly-referenced references*)
         match t1 with
         | TmVar(id) -> begin
            match List.assoc_opt id sstore with
            | Some(l) -> ExRslProgress, TmVal(VluLoc(l)), sctx
            | None -> ExRslStuk(StkUnboundVar), t, sctx
         end
         | _ -> ExRslStuk(StkUndefBeh), t, sctx
      end
      | TmLet(mty, id, sty, t1) -> begin
         match t1 with
         | TmVal(v) ->
            let n = Id.name id in
            let l = fresh sctx n in
            ExRslProgress, TmVal(unit_v),  ((id, l)::sstore, (l, (v, PermDel))::smem)
         | _ -> let (rsl, t1', sctx') = sym_exe_step t1 sctx in (rsl, TmLet(mty, id, sty, t1'), sctx')
      end
      | TmSeq(t1, t2) -> begin
         match t1 with
         (** handle values of Drop trait*)
         | TmVal(_) -> ExRslProgress, t2, sctx
         | _ -> let (rsl, t1', sctx') = sym_exe_step t1 sctx in (rsl, TmSeq(t1', t2), sctx')
      end

      let rec sym_exe t sctx = 
         let (rsl_s, t', sctx') as res = sym_exe_step t sctx in
         match rsl_s with
         | ExRslProgress -> sym_exe t' sctx'
         | ExRslVlu
         | ExRslStuk(_) -> res
end

module Verification = struct
let verify f =
   let open Ast in
   let open Exe in
   let sctx = initial_ctx f.params in
   sym_exe f.body sctx
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

let unsafe_deref_fn = {
   name= "unsafe_deref_fn";
   rep= {pre=PrdTrue; post=PrdTrue};
   params = (Id.make "x", StTypRef(MtImm, unit_st))::[];
   body =
   TmSeq begin
      TmLet(MtImm, Id.make "ptr", StTypRawPtr(MtImm, unit_st), TmVar(Id.make "x")),
      TmDref(TmVar(Id.make "ptr"))
   end
}
;;
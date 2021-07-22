open Aux

type rt_type = RtTypProd of Id.t * (Id.t * rt_type) list | RtTypPtr

type perm = PermDel | PermWr | PermRd | PermDen

let weight = function PermDen -> 0 | PermRd -> 1 | PermWr -> 2 | PermDel -> 3

let ( < ) a b = weight a < weight b

let ( >= ) a b = weight a >= weight b

type sym_store = (Id.t * Symbol.t) list

type sym_mem = (Symbol.t * (Ast.vlu * perm)) list

type sym_ctx = sym_store * sym_mem

let rec rt_type_of_val v =
  let open Ast in
  match v with
  | VluLoc _ -> RtTypPtr
  | VluProd (id, v_elms) -> (
      match v_elms with
      | [] -> RtTypProd (id, [])
      | (ide, ve) :: tail -> (
          let te = rt_type_of_val ve in
          let rttyp = rt_type_of_val (VluProd (Id.dummy, tail)) in
          match rttyp with
          | RtTypProd (_, t_elms) -> RtTypProd (id, (ide, te) :: t_elms)
          | _ -> assert false))

let rec is_sym_used_vlu sym v =
  let open Ast in
  match v with
  | VluProd (id, elms) -> (
      match elms with
      | [] -> false
      | (_, v1) :: tail ->
          is_sym_used_vlu sym v1
          ||
          let v' = VluProd (id, tail) in
          is_sym_used_vlu sym v')
  | VluLoc l -> sym = l

let rec is_sym_used_smem sym smem =
  match smem with
  | [] -> false
  | (l, (v, _)) :: tail ->
      sym = l || is_sym_used_vlu sym v || is_sym_used_smem sym tail

let rec is_sym_used_sstore sym sstore =
  match sstore with
  | [] -> false
  | (_, l) :: tail -> sym = l || is_sym_used_sstore sym tail

let fresh sctx bn =
  let rec fresh_h ((sstore, smem) as sctx) bn idx =
    let str = "_" ^ Name.create_name bn idx in
    let sym = Symbol.make str in
    if is_sym_used_sstore sym sstore || is_sym_used_smem sym smem then
      let idx' = idx + 1 in
      fresh_h sctx bn idx'
    else sym
  in
  fresh_h sctx bn 0

type stuck =
  | StkUnboundVar
  | StkNpermAct
  | StkUndefBeh
  | StkCtxMismatch
  | StkCtxCorrupt
  | StkLocInOccu
  | StkChunkNtFound
  | StkMemLeak
  | StkNotSupp

type exec_rsl = ExRslProgress | ExRslVlu | ExRslStuk of stuck

let translate_mut_perm mt =
  let open Ast in
  match mt with MtImm -> PermRd | MtMut -> PermWr

let rec produce_val_of_sttyp ((systore, symem) as syctx) sttyp =
  let open Ast in
  match sttyp with
  | StTypRef (_, _) | StTypRawPtr (_, _) -> VluLoc (fresh syctx "loc")
  | StTypProd (id, elm_sttyps) -> (
      match elm_sttyps with
      | [] -> VluProd (id, [])
      | (eid, est) :: tail -> (
          let ev = produce_val_of_sttyp syctx est in
          let symmem' = (Symbol.dummy, (ev, PermDen)) :: symem in
          match
            produce_val_of_sttyp (systore, symmem') (StTypProd (id, tail))
          with
          | VluProd (_, evs) -> VluProd (id, (eid, ev) :: evs)
          | _ -> assert false))

let initial_symctx params =
  let rec initial_symctx_h params ((sstore, smem) as symctx) =
    match params with
    | [] -> symctx
    | (id, sttyp) :: tail ->
        let bn = Id.name id in
        let l = fresh symctx bn in
        let sstore' = (id, l) :: sstore in
        let v = produce_val_of_sttyp (sstore', smem) sttyp in
        let symctx' = (sstore', (l, (v, PermDel)) :: smem) in
        initial_symctx_h tail symctx'
  in
  initial_symctx_h params ([], [])

let val_perm_of_id id (systore, symem) =
  match List.assoc_opt id systore with
  | None -> Error StkUnboundVar
  | Some l -> (
      match List.assoc_opt l symem with
      | None -> Error StkCtxCorrupt
      | Some (v, perm) -> Ok (v, perm))

let rec is_consistent_rtt_stt rttyp sttyp =
  let open Ast in
  match rttyp with
  | RtTypPtr -> (
      match sttyp with
      | StTypRawPtr (_, _) | StTypRef (_, _) -> true
      | _ -> false)
  | RtTypProd (id_rtt, elms_rtt) -> (
      match sttyp with
      | StTypRawPtr (_, _) | StTypRef (_, _) -> false
      | StTypProd (id_stt, elms_stt) -> (
          if id_rtt <> id_stt then false
          else
            match elms_rtt with
            | [] -> elms_stt = []
            | (ide_rtt, te_rtt) :: tail_elms_rtt -> (
                match elms_stt with
                | [] -> false
                | (ide_stt, te_stt) :: tail_elms_stt ->
                    ide_rtt = ide_stt
                    && is_consistent_rtt_stt te_rtt te_stt
                    && is_consistent_rtt_stt
                         (RtTypProd (Id.dummy, tail_elms_rtt))
                         (StTypProd (Id.dummy, tail_elms_stt)))))

let realize id (stctx : Ast.st_ctx) ((systore, symem) as syctx : sym_ctx)
    rl_hist =
  let rsl = val_perm_of_id id syctx in
  match rsl with
  | Error stk -> (ExRslStuk stk, syctx, rl_hist)
  | Ok (idv, idv_p) -> (
      if idv_p < PermRd then (ExRslStuk StkNpermAct, syctx, rl_hist)
      else
        match idv with
        | VluProd (_, _) -> (ExRslStuk StkUndefBeh, syctx, rl_hist)
        | VluLoc l -> (
            match List.assoc_opt l symem with
            | Some _ -> (ExRslStuk StkLocInOccu, syctx, rl_hist)
            | None -> (
                let open Ast in
                match List.assoc_opt id stctx with
                | None -> (ExRslStuk StkCtxMismatch, syctx, rl_hist)
                | Some id_sttyp -> (
                    match id_sttyp with
                    | StTypProd (_, _) ->
                        (ExRslStuk StkCtxMismatch, syctx, rl_hist)
                    | StTypRawPtr (_, _) ->
                        (ExRslStuk StkUndefBeh, syctx, rl_hist)
                    | StTypRef (mt, pointee_sttyp) ->
                        let pointee_perm = translate_mut_perm mt in
                        let pointee_val =
                          produce_val_of_sttyp syctx pointee_sttyp
                        in
                        let symem' =
                          (l, (pointee_val, pointee_perm)) :: symem
                        in
                        (ExRslProgress, (systore, symem'), id :: rl_hist)))))

let unrealize id (stctx : Ast.st_ctx) ((systore, symem) as syctx : sym_ctx) =
  let rsl = val_perm_of_id id syctx in
  match rsl with
  | Error stk -> (ExRslStuk stk, syctx)
  | Ok (idv, idv_p) -> (
      if idv_p < PermRd then (ExRslStuk StkNpermAct, syctx)
      else
        match idv with
        | VluProd (_, _) -> (ExRslStuk StkUndefBeh, syctx)
        | VluLoc l -> (
            let open Ast in
            match List.assoc_opt l symem with
            | None -> (ExRslStuk StkChunkNtFound, syctx)
            | Some (pointee_val, pointee_perm) -> (
                match List.assoc_opt id stctx with
                | None -> (ExRslStuk StkCtxMismatch, syctx)
                | Some id_sttyp -> (
                    match id_sttyp with
                    | StTypProd (_, _) -> (ExRslStuk StkCtxMismatch, syctx)
                    | StTypRawPtr (_, _) -> (ExRslStuk StkUndefBeh, syctx)
                    | StTypRef (mt, pointee_sttyp) ->
                        let pointee_perm_req = translate_mut_perm mt in
                        if pointee_perm <> pointee_perm_req then
                          (ExRslStuk StkNpermAct, syctx)
                        else
                          let pointee_rttyp = rt_type_of_val pointee_val in
                          let incons =
                            not
                              (is_consistent_rtt_stt pointee_rttyp pointee_sttyp)
                          in
                          if incons then (ExRslStuk StkCtxMismatch, syctx)
                          else
                            let prd = ( <> ) (l, (pointee_val, pointee_perm)) in
                            let symem' = List.filter prd symem in
                            (ExRslProgress, (systore, symem'))))))

let rec sym_exe_step t ((systore, symem) as syctx : sym_ctx)
    (stctx : Ast.st_ctx) rlhist =
  let open Ast in
  match t with
  | TmVal _ -> (ExRslVlu, t, syctx, stctx, rlhist)
  | TmVar id -> (
      match List.assoc_opt id systore with
      | None -> (ExRslStuk StkUnboundVar, t, syctx, stctx, rlhist)
      | Some l ->
          (ExRslProgress, TmDref (TmVal (VluLoc l)), syctx, stctx, rlhist))
  | TmDref t1 -> (
      match t1 with
      | TmVal v -> (
          match v with
          | VluLoc l -> (
              match List.assoc_opt l symem with
              | Some (v', p) when p >= PermRd ->
                  (ExRslProgress, TmVal v', syctx, stctx, rlhist)
              | _ -> (ExRslStuk StkNpermAct, t, syctx, stctx, rlhist))
          | _ -> (ExRslStuk StkUndefBeh, t, syctx, stctx, rlhist))
      | _ ->
          let rsl, t1', syctx', stctx', rlhist' =
            sym_exe_step t1 syctx stctx rlhist
          in
          (rsl, TmDref t1', syctx', stctx', rlhist'))
  | TmRef (_, t1) -> (
      (***@todo: study and represent the behavior of poly-referenced references*)
      match t1 with
      | TmVar id -> (
          match List.assoc_opt id systore with
          | None -> (ExRslStuk StkUnboundVar, t, syctx, stctx, rlhist)
          | Some l -> (ExRslProgress, TmVal (VluLoc l), syctx, stctx, rlhist))
      | _ -> (ExRslStuk StkUndefBeh, t, syctx, stctx, rlhist))
  | TmLet (mt, id, sttyp, t1) -> (
      match t1 with
      | TmVal v ->
          let n = Id.name id in
          let l = fresh syctx n in
          let systore' = (id, l) :: systore in
          let symem' = (l, (v, PermDel)) :: symem in
          let stctx' = (id, sttyp) :: stctx in
          (ExRslProgress, TmVal unit_v, (systore', symem'), stctx', rlhist)
      | _ ->
          let rsl, t1', syctx', stctx', rlhist' =
            sym_exe_step t1 syctx stctx rlhist
          in
          (rsl, TmLet (mt, id, sttyp, t1'), syctx', stctx', rlhist'))
  | TmSeq (t1, t2) -> (
      match t1 with
      (***@todo: handle values of Drop trait*)
      | TmVal _ -> (ExRslProgress, t2, syctx, stctx, rlhist)
      | _ ->
          let rsl, t1', syctx', stctx', rlhist' =
            sym_exe_step t1 syctx stctx rlhist
          in
          (rsl, TmSeq (t1', t2), syctx', stctx', rlhist'))
  | TmGhost gt -> (
      match gt with
      | GtRealize id ->
          let rsl, syctx', rlhist' = realize id stctx syctx rlhist in
          let t' = if rsl = ExRslProgress then TmVal unit_v else t in
          (rsl, t', syctx', stctx, rlhist')
      | GtUnRealize _ -> (ExRslStuk StkNotSupp, t, syctx, stctx, rlhist))

let rec sym_exe t syctx stctx rlhist =
  let ((rsl, t', syctx', stctx', rlhist') as ret) =
    sym_exe_step t syctx stctx rlhist
  in
  match rsl with
  | ExRslProgress -> sym_exe t' syctx' stctx' rlhist'
  | ExRslVlu | ExRslStuk _ -> ret

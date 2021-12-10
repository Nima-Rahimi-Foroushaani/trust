(* open Sym_ast
open Aux

type stack_frame = (Id.t * Symbol.t) list
(**maps variable names to addresses*)

type heap = (Symbol.t * vlu) list
(**the heap is represented as a mapping between addresses and values*)

type conf = stack_frame * heap

type stk = StkInsNotSupported | StkVarNameInUse | StkUndefinedVarName

let syms_of_val v = match v with VluUnit -> [] | VluInt s -> [ s ]

let syms_of_frame f =
  let _, adds = List.split f in
  ListAux.uniq adds

let syms_of_heap_vals h =
  let syms = List.concat_map (fun (_, v) -> syms_of_val v) h in
  ListAux.uniq syms

let syms_of_conf (f, h) =
  let f_syms = syms_of_frame f in
  let v_syms = syms_of_heap_vals h in
  let syms = List.append f_syms v_syms in
  ListAux.uniq syms

let fresh_sym syms bn =
  let rec helper syms bn idx =
    let str = "_" ^ Name.create_name bn idx in
    let sym = Symbol.make str in
    if List.exists (( = ) sym) syms then
      let idx' = idx + 1 in
      helper syms bn idx'
    else sym
  in
  helper syms bn 0

let rec exe_step ins ((f, h) as cnf) =
  match ins with
  | InsMutBor (lid, _ (*lifetime id*), rid) | InsRaw (lid, rid) -> (
      match List.assoc_opt lid f with
      | Some _ -> Error StkVarNameInUse
      | None -> (
          match List.assoc_opt rid f with
          | None -> Error StkUndefinedVarName
          | Some loc -> Ok ((lid, loc) :: f, h)))
  (*| InsDrop id -> ()
    | InsImmute id -> ()
      | InsSwap (lid, rid) -> ()
      | InsMkPtr (lid, rid) -> ()
      | InsDeref (lid, rid) -> ()
      | InsCopy (lid, rid) -> ()*)
  | InsIntro _ | InsNow _ -> Ok cnf
  | InsCnst (id, v) ->
      if List.mem_assoc id f then Error StkVarNameInUse
      else
        let bn = "loc_" ^ Id.name id in
        let new_loc = fresh_sym (syms_of_conf cnf) bn in
        Ok ((id, new_loc) :: f, (new_loc, v) :: h)
  | _ -> Error StkInsNotSupported
(* open Aux
   open Exception

   type dy_type = DyTypInt | DyTypPtr | DyTypProd of Id.t * (Id.t * dy_type) list

   type perm = PermDel | PermWr | PermRd

   let weight = function PermDel -> 3 | PermWr -> 2 | PermRd -> 1

   let ( <. ) a b = weight a < weight b

   let ( >=. ) a b = weight a >= weight b

   type dy_ctx = (Id.t * Symbol.t) list

   type sym_mem = (Symbol.t * (Ast.vlu * perm)) list

   type path_cond = Ast.proposition list

   type rlz_vars = Id.t list

   type sym_ctx = dy_ctx * sym_mem * path_cond * rlz_vars

   type exe_state = Ast.term * Ast.st_ctx * sym_ctx

   type exe_tree = exe_state Tree.t

   let rec dy_type_of_val v =
     let open Ast in
     match v with
     | VluInt _ -> DyTypInt
     | VluLoc _ -> DyTypPtr
     | VluProd (id, elms) ->
         DyTypProd (id, List.map (fun (eid, ev) -> (eid, dy_type_of_val ev)) elms)

   let rec syms_of_val v =
     let open Ast in
     match v with
     | VluInt i -> [ i ]
     | VluLoc l -> [ l ]
     | VluProd (_, elms) -> List.concat_map (fun (_, ev) -> syms_of_val ev) elms

   let syms_of_smem smem =
     List.concat_map (fun (l, (v, _)) -> l :: syms_of_val v) smem

   let rec is_sym_in_val sym v =
     let open Ast in
     match v with
     | VluInt s | VluLoc s -> sym = s
     | VluProd (_, elms) -> List.exists (fun (_, ev) -> is_sym_in_val sym ev) elms

   let is_sym_in_symem sym smem =
     List.exists (fun (l, (v, _)) -> sym = l || is_sym_in_val sym v) smem

   let is_sym_in_dyctx sym dyctx = List.exists (fun (_, l) -> sym = l) dyctx

   type stk_un_auth =
     | UaChunkNotFound
     | UaInsufPerm
     | UaPermMismatch
     | UaCtxStructViol
     | UaDropRealizedVar

   type stk_ctx_corrupt = CcStDyInconsistent | CcRlzList

   type stk_undef =
     | UdefUnboundVar
     | UdefMemDup
     | UdefRlzNonRef
     | UdefUrlzNonRef
     | UdefUrlzNonRlzedId
     | UdefAssignToVal
     | UdefRefOfNonId
     | UdefDerefOfNonLoc

   type stuck =
     | StkUnAuth of stk_un_auth
     | StkUndef of stk_undef
     | StkCtxCorrupt of stk_ctx_corrupt
     | StkMemLeak
     | StkNotSupp
   (***@todo: remove unnecessary stk variants and check asserts*)

   (**Exceptions used commonly in this module*)
   let ctx_mismatch =
     Excp (SevBug, "Static context and dynamic context do not match")

   let dctx_smem_mismatch =
     Excp (SevBug, "Dynamic context and symbolic memory do not match")

   let dup_smem_chnk = Excp (SevBug, "Duplicate chunk in symbolic memory")

   let dup_rlz_lst id =
     Excp
       ( SevBug,
         "More than one occurance of Id \"" ^ Id.name id
         ^ "\" in the realized variables list" )

   let translate_mut_perm mt =
     let open Ast in
     match mt with MtImm -> PermRd | MtMut -> PermWr

   let rec fresh_val syms sttyp bn =
     let open Ast in
     match sttyp with
     | StTypInt -> VluInt (fresh_sym syms bn)
     | StTypRef (_, _) | StTypRawPtr (_, _) -> VluLoc (fresh_sym syms bn)
     | StTypProd (id, es) -> (
         match es with
         | [] -> VluProd (id, [])
         | (eid, et) :: tl -> (
             let ev = fresh_val syms et (bn ^ "_" ^ Id.name eid) in
             let syms' = syms_of_val ev @ syms in
             match fresh_val syms' (StTypProd (id, tl)) bn with
             | VluProd (_, tl_evs) -> VluProd (id, (eid, ev) :: tl_evs)
             | _ -> assert false))

   let val_perm_of_id id dctx smem =
     match List.assoc_opt id dctx with
     | None -> Error (StkUndef UdefUnboundVar)
     | Some l -> (
         match List.assoc_opt l smem with
         | None -> raise dctx_smem_mismatch
         | Some (v, perm) -> Ok (v, perm))

   let rec is_consistent_dyt_stt dytyp sttyp =
     let open Ast in
     match dytyp with
     | DyTypInt -> sttyp = StTypInt
     | DyTypPtr -> (
         (***@todo: should we also check for pointee type*)
         match sttyp with
         | StTypRef (_, _) | StTypRawPtr (_, _) -> true
         | _ -> false)
     | DyTypProd (did, des) -> (
         match sttyp with
         | StTypProd (sid, ses) ->
             did = sid
             && List.length des = List.length ses
             && List.for_all2
                  (fun (deid, dt) (seid, st) ->
                    deid = seid && is_consistent_dyt_stt dt st)
                  des ses
         | _ -> false)

   let realize id stctx dctx smem rll =
     let open Ast in
     match val_perm_of_id id dctx smem with
     | Error stk -> Error stk
     | Ok (val_ref, perm_ref) -> (
         if perm_ref <. PermRd then Error (StkUnAuth UaInsufPerm)
         else
           (fun cont ->
             match val_ref with
             | VluLoc l_pte -> cont l_pte
             | _ -> Error (StkUndef UdefRlzNonRef))
           @@ fun l_pte ->
           match List.assoc_opt l_pte smem with
           | Some _ -> Error (StkUndef UdefMemDup)
           | None -> (
               match List.assoc_opt id stctx with
               | None -> raise ctx_mismatch
               | Some sttyp -> (
                   match sttyp with
                   | StTypInt | StTypProd (_, _) -> raise ctx_mismatch
                   | StTypRawPtr (_, _) -> Error (StkUndef UdefRlzNonRef)
                   | StTypRef (mty, st_pte) ->
                       let perm_pte = translate_mut_perm mty in
                       let syms = syms_of_smem smem in
                       let bn = Symbol.name l_pte ^ "_pointee" in
                       let val_pte = fresh_val syms st_pte bn in
                       let smem' = (l_pte, (val_pte, perm_pte)) :: smem in
                       Ok (smem', id :: rll))))

   let unrealize id stctx dctx smem rll =
     let open Ast in
     (fun cont ->
       (***@todo: is it safe to allow unrealize a reference from everywhere in "rll"?
         In other words, we are treating this list as unstructured*)
       let ids, rll' = List.partition (( = ) id) rll in
       match ids with
       | [] -> Error (StkUndef UdefUrlzNonRlzedId)
       | [ _ ] -> (
           match cont () with
           | Error stk -> Error stk
           | Ok smem' -> Ok (smem', rll'))
       | _ -> raise (dup_rlz_lst id))
     @@ fun () ->
     match val_perm_of_id id dctx smem with
     | Error _ ->
         raise
           (Excp (SevBug, "Dynamic context does not match with realized vars list"))
     | Ok (v, perm) -> (
         if perm <. PermRd then Error (StkUnAuth UaInsufPerm)
         else
           match v with
           | VluInt _ | VluProd (_, _) ->
               raise
                 (Excp
                    ( SevBug,
                      "Variable with non-reference value in the realized list" ))
           | VluLoc l_pte -> (
               match List.assoc_opt l_pte smem with
               | None -> Error (StkUnAuth UaChunkNotFound)
               | Some (val_pte, perm_pte) -> (
                   match List.assoc_opt id stctx with
                   | None -> raise ctx_mismatch
                   | Some sttyp -> (
                       match sttyp with
                       | StTypInt | StTypProd (_, _) -> raise ctx_mismatch
                       | StTypRawPtr (_, _) ->
                           raise
                             (Excp (SevBug, "Raw pointer in realized vars list"))
                       | StTypRef (mty, st_pte) -> (
                           let perm_pte_req = translate_mut_perm mty in
                           if perm_pte <> perm_pte_req then
                             Error (StkUnAuth UaPermMismatch)
                           else
                             let dt_pte = dy_type_of_val val_pte in
                             if not @@ is_consistent_dyt_stt dt_pte st_pte then
                               raise ctx_mismatch
                             else
                               match
                                 List.partition
                                   (( = ) (l_pte, (val_pte, perm_pte)))
                                   smem
                               with
                               | [ _ ], smem' -> Ok smem'
                               | _ ->
                                   raise
                                     (Excp
                                        ( SevBug,
                                          "Duplicate memory block in symbolic \
                                           memory" )))))))

   let drop_var id stctx dctx smem rll =
     (fun cont ->
       match stctx with
       | (hd_id, hd_stt) :: stctx' when hd_id = id -> (
           match cont hd_stt with
           | Error stk -> Error stk
           | Ok (dctx', smem') -> Ok (stctx', dctx', smem'))
       | _ -> Error (StkUnAuth UaCtxStructViol))
     @@ (fun cont stt ->
          (*Dynamic and Static context should match*)
          match dctx with
          | (hd_id, hd_l) :: dctx' when hd_id = id -> (
              match cont stt hd_l with
              | Error stk -> Error stk
              | Ok smem' -> Ok (dctx', smem'))
          | _ -> raise ctx_mismatch)
     @@ fun stt l ->
     let chks, smem' = List.partition (fun (chk_l, _) -> chk_l = l) smem in
     match chks with
     | [] -> raise dctx_smem_mismatch
     | [ (_, (v, p)) ] ->
         let dyt = dy_type_of_val v in
         if not @@ is_consistent_dyt_stt dyt stt then raise ctx_mismatch
         else if p <> PermDel then Error (StkUnAuth UaInsufPerm)
         else if List.exists (( = ) id) rll then
           Error (StkUnAuth UaDropRealizedVar)
         else Ok smem'
     | _ -> raise dup_smem_chnk

   let drop_val v smem =
     (fun _ -> ()) v;
     Ok smem

   (***@todo: handle values of Drop trait*)
   let alloc_local_var id v dctx smem =
     let syms = syms_of_val v @ syms_of_smem smem in
     let bn = "loc_" ^ Id.name id in
     let l = fresh_sym syms bn in
     let dctx' = (id, l) :: dctx in
     let smem' = (l, (v, PermDel)) :: smem in
     (dctx', smem')

   let rec sym_exe_step t stctx ((dctx, smem, pcond, rll) as syctx) =
     let open Ast in
     match t with
     | TmVal _ -> Ok (t, stctx, syctx)
     | TmVar id -> (
         match List.assoc_opt id dctx with
         | None -> Error (StkUndef UdefUnboundVar)
         | Some l -> Ok (TmDref (TmVal (VluLoc l)), stctx, syctx))
     | TmLet (mty, id, sttyp, ta, tb) -> (
         match ta with
         | TmVal v ->
             let stctx' = (id, sttyp) :: stctx in
             let dctx', smem' = alloc_local_var id v dctx smem in
             Ok (TmInLet (id, tb), stctx', (dctx', smem', pcond, rll))
         | _ -> (
             match sym_exe_step ta stctx syctx with
             | Error stk -> Error stk
             | Ok (ta', stctx', syctx') ->
                 Ok (TmLet (mty, id, sttyp, ta', tb), stctx', syctx')))
     | TmInLet (id, tb) -> (
         match tb with
         | TmVal v -> (
             match drop_var id stctx dctx smem rll with
             | Error stk -> Error stk
             | Ok (stctx', dctx', smem') ->
                 Ok (TmVal v, stctx', (dctx', smem', pcond, rll)))
         | _ -> (
             match sym_exe_step tb stctx syctx with
             | Error stk -> Error stk
             | Ok (tb', stctx', syctx') -> Ok (TmInLet (id, tb'), stctx', syctx')))
     | TmFin (tb, tp) -> (
         match tb with
         | TmVal v1 -> (
             match tp with
             | TmVal _ -> Ok (TmVal v1, stctx, syctx)
             | _ -> (
                 match sym_exe_step tp stctx syctx with
                 | Error stk -> Error stk
                 | Ok (tp', stctx', syctx') ->
                     Ok (TmFin (TmVal v1, tp'), stctx', syctx')))
         | _ -> (
             match sym_exe_step tb stctx syctx with
             | Error stk -> Error stk
             | Ok (tb', stctx', syctx') -> Ok (TmFin (tb', tp), stctx', syctx')))
     | TmDrop t -> (
         match t with
         | TmVal v -> (
             match drop_val v smem with
             | Error stk -> Error stk
             | Ok smem' ->
                 let syctx' = (dctx, smem', pcond, rll) in
                 Ok (TmVal vlu_unit, stctx, syctx'))
         | _ -> (
             match sym_exe_step t stctx syctx with
             | Error stk -> Error stk
             | Ok (t', stctx', syctx') -> Ok (TmDrop t', stctx', syctx')))
     | TmAssign (tl, tr) -> (
         match tl with
         | TmVal _ -> Error (StkUndef UdefAssignToVal)
         | TmDref (TmVal (VluLoc l)) -> (
             match tr with
             | TmVal v -> (
                 match List.assoc_opt l smem with
                 | None -> Error (StkUnAuth UaChunkNotFound)
                 | Some (_, p) ->
                     if p <. PermWr then Error (StkUnAuth UaInsufPerm)
                     else
                       let smem' =
                         List.map
                           (fun ((lc, (_, pc)) as chk) ->
                             if lc = l then (lc, (v, pc)) else chk)
                           smem
                       in
                       Ok (TmVal vlu_unit, stctx, (dctx, smem', pcond, rll)))
             | _ -> (
                 match sym_exe_step tr stctx syctx with
                 | Error stk -> Error stk
                 | Ok (tr', stctx', syctx') ->
                     Ok (TmAssign (tl, tr'), stctx', syctx')))
         | _ -> (
             match sym_exe_step tl stctx syctx with
             | Error stk -> Error stk
             | Ok (tl', stctx', syctx') -> Ok (TmAssign (tl', tr), stctx', syctx'))
         )
     | TmRef (_, t1) -> (
         (***@todo: study and represent the behavior of poly-referenced references*)
         (***@todo: add paths to get references of record elements*)
         match t1 with
         | TmVar id -> (
             match List.assoc_opt id dctx with
             | None -> Error (StkUndef UdefUnboundVar)
             | Some l -> Ok (TmVal (VluLoc l), stctx, syctx))
         | _ -> Error (StkUndef UdefRefOfNonId))
     | TmDref t1 -> (
         match t1 with
         | TmVal v -> (
             match v with
             | VluLoc l -> (
                 match List.assoc_opt l smem with
                 | None -> Error (StkUnAuth UaChunkNotFound)
                 | Some (v, p) ->
                     if p <. PermRd then Error (StkUnAuth UaInsufPerm)
                     else Ok (TmVal v, stctx, syctx))
             | _ -> Error (StkUndef UdefDerefOfNonLoc))
         | _ -> (
             match sym_exe_step t1 stctx syctx with
             | Error stk -> Error stk
             | Ok (t1', stctx', syctx') -> Ok (TmDref t1', stctx', syctx')))
     | TmProd (id, elms) ->
         let rec f vlu_es es =
           match es with
           | (ide, te) :: tail -> (
               match te with
               | TmVal _ -> f (vlu_es @ [ (ide, te) ]) tail
               | _ -> (
                   match sym_exe_step te stctx syctx with
                   | Error stk -> Error stk
                   | Ok (te', stctx', syctx') ->
                       let elms' = vlu_es @ ((ide, te') :: tail) in
                       Ok (TmProd (id, elms'), stctx', syctx')))
           | [] ->
               let vs =
                 List.map
                   (fun (eid, et) ->
                     match et with TmVal v -> (eid, v) | _ -> assert false)
                   elms
               in
               Ok (TmVal (VluProd (id, vs)), stctx, syctx)
         in
         f [] elms
     | TmSeq (t1, t2) -> (
         match t1 with
         | TmVal _ -> Ok (t2, stctx, syctx)
         | _ -> (
             match sym_exe_step t1 stctx syctx with
             | Error stk -> Error stk
             | Ok (t1', stctx', syctx') -> Ok (TmSeq (t1', t2), stctx', syctx')))
     | TmGhost gt -> (
         match gt with
         | GtRealize id -> (
             match realize id stctx dctx smem rll with
             | Error stk -> Error stk
             | Ok (smem', rll') ->
                 let syctx' = (dctx, smem', pcond, rll') in
                 Ok (TmVal vlu_unit, stctx, syctx'))
         | GtUnRealize id -> (
             match unrealize id stctx dctx smem rll with
             | Error stk -> Error stk
             | Ok (smem', rll') ->
                 let syctx' = (dctx, smem', pcond, rll') in
                 Ok (TmVal vlu_unit, stctx, syctx')))

   let rec sym_exe t stctx syctx print_state =
     print_state (t, stctx, syctx);
     let res = sym_exe_step t stctx syctx in
     match res with
     | Error stk -> Error stk
     | Ok (t', stctx', syctx') -> (
         match t' with TmVal _ -> res | _ -> sym_exe t' stctx' syctx' print_state) *) *)

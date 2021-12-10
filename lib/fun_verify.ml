(* open Exe

let init_sym_ctx params =
  let rec init_sym_ctx_h params dctx smem =
    match params with
    | [] -> (dctx, smem)
    | (id, stt) :: tail ->
        let syms = syms_of_smem smem in
        let bn = Id.name id in
        let v = fresh_val syms stt bn in
        let dctx', smem' = alloc_local_var id v dctx smem in
        init_sym_ctx_h tail dctx' smem'
  in
  let stctx = List.rev params in
  (*The parameter in the left is defined sooner, so the order of static context
    is the reverse of parameters*)
  let dctx, smem = init_sym_ctx_h params [] [] in
  (stctx, dctx, smem)

let rec unrealize_all stctx dctx smem rll =
  match rll with
  | [] -> Ok smem
  | id :: _ -> (
      match unrealize id stctx dctx smem rll with
      | Error stk -> Error stk
      | Ok (smem', rll') -> unrealize_all stctx dctx smem' rll')

let rec drop_local_vars stctx dctx smem rll =
  match stctx with
  | [] -> ( match dctx with [] -> Ok smem | _ -> raise ctx_mismatch)
  | (id, _) :: _ -> (
      match drop_var id stctx dctx smem rll with
      | Error stk -> Error stk
      | Ok (stctx', dctx', smem') -> drop_local_vars stctx' dctx' smem' rll)

let clean_up stctx (dctx, smem, _, rll) =
  match unrealize_all stctx dctx smem rll with
  | Error stk -> Error stk
  | Ok smem' -> (
      match drop_local_vars stctx dctx smem' [] with
      | Error stk -> Error stk
      | Ok smem' -> if smem' <> [] then Error StkMemLeak else Ok ())

let verify f print_state =
  let open Ast in
  let stctx, dctx, smem = init_sym_ctx f.params in
  match sym_exe f.body stctx (dctx, smem, [], []) print_state with
  | Error stk -> Error stk
  | Ok (TmVal _, stctx', syctx') -> clean_up stctx' syctx'
  | _ -> assert false
sym_exe fails or returns value *)

let rec unrealize_all stctx syctx rl_hist =
  let open Exe in
  match rl_hist with
  | [] -> Ok syctx
  | id :: tail -> (
      let rsl, syctx' = unrealize id stctx syctx in
      match rsl with
      | ExRslVlu -> assert false
      | ExRslStuk stk -> Error stk
      | ExRslProgress -> unrealize_all stctx syctx' tail)

let drop_val v symem =
  (***@todo: handle values of Drop trait*)
  let open Ast in
  match v with VluLoc _ -> symem | VluProd (_, _) -> symem

let rec drop_sym_store (systore, symem) =
  match systore with
  | [] -> Ok symem
  | (_, l) :: tail -> (
      let open Exe in
      match List.assoc_opt l symem with
      | None -> Error StkCtxCorrupt
      | Some (v, p) ->
          let prd = ( <> ) (l, (v, p)) in
          let symem' = List.filter prd symem in
          let symem' = drop_val v symem' in
          drop_sym_store (tail, symem'))

let clean_up stctx syctx rl_hist =
  let rsl = unrealize_all stctx syctx rl_hist in
  match rsl with
  | Error stk -> Error stk
  | Ok syctx' -> (
      let rsl = drop_sym_store syctx' in
      match rsl with
      | Error stk -> Error stk
      | Ok symem' ->
          let open Exe in
          if symem' <> [] then Error StkMemLeak else Ok ())

let verify f =
  let open Ast in
  let open Exe in
  let syctx = initial_symctx f.params in
  let ((rsl, t, syctx, stctx, rlhist) as ret) =
    sym_exe f.body syctx f.params []
  in
  match rsl with
  | ExRslProgress -> assert false
  | ExRslStuk _ -> Error ret
  | ExRslVlu -> (
      let rsl = clean_up stctx syctx rlhist in
      match rsl with
      | Error stk -> Error (ExRslStuk stk, t, syctx, stctx, rlhist)
      | Ok () -> Ok ())

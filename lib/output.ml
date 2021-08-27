open Aux
open Ast
open Format

type print_tbox = {
  stt_o : unit -> unit;
  stt_c : unit -> unit;
  val_o : unit -> unit;
  val_c : unit -> unit;
  kwd_o : unit -> unit;
  kwd_c : unit -> unit;
  id_o : unit -> unit;
  id_c : unit -> unit;
  perm_o : unit -> unit;
  perm_c : unit -> unit;
  print_string : string -> unit;
  space : unit -> unit;
  box_o : unit -> unit;
  box_c : unit -> unit;
  box_v_o : unit -> unit;
  box_v_c : unit -> unit;
  info_o : unit -> unit;
  info_c : unit -> unit;
  flush : unit -> unit;
}

let rec print_list pe sep l =
  match l with
  | [] -> ()
  (*This case fires only for empty list*)
  | h :: t ->
      if t <> [] then (
        print_list pe sep t;
        sep ());
      pe h

let print_assoc pf ps pmap sep l =
  let pe (f, s) =
    pf f;
    pmap ();
    ps s
  in
  print_list pe sep l

let print_info ptb str =
  ptb.info_o ();
  ptb.print_string str;
  ptb.info_c ()

let print_sym ptb s =
  ptb.val_o ();
  ptb.print_string (Symbol.name s);
  ptb.val_c ()

let print_id ptb id =
  ptb.id_o ();
  ptb.print_string (Id.name id);
  ptb.id_c ()

let print_kwd ptb kwd =
  ptb.kwd_o ();
  ptb.print_string kwd;
  ptb.kwd_c ()

let print_prod ptb pe id es =
  let pf = print_id ptb in
  let ps = pe ptb in
  let pmap () = print_kwd ptb ":" in
  let sep () =
    print_kwd ptb ",";
    ptb.space ()
  in
  let print_es = print_assoc pf ps pmap sep in
  ptb.box_o ();
  print_id ptb id;
  print_kwd ptb "(";
  print_es es;
  print_kwd ptb ")";
  ptb.box_c ()

let rec print_val ptb v =
  match v with
  | VluInt s | VluLoc s -> print_sym ptb s
  | VluProd (id, es) -> print_prod ptb print_val id es

let mutability_to_string = function MtImm -> "imm" | MtMut -> "mut"

let perm_to_string =
  let open Exe in
  function PermDel -> "del" | PermWr -> "wr" | PermRd -> "rd"

let print_perm ptb perm =
  ptb.perm_o ();
  ptb.print_string (perm_to_string perm);
  ptb.perm_c ()

let rec print_st_typ ptb stt =
  let print_location_type kwd mty stt =
    ptb.box_o ();
    print_kwd ptb (kwd ^ " " ^ mutability_to_string mty);
    ptb.space ();
    print_st_typ ptb stt;
    ptb.box_c ()
  in
  match stt with
  | StTypInt ->
      ptb.stt_o ();
      ptb.print_string "int";
      ptb.stt_c ()
  | StTypRef (mty, stt) -> print_location_type "ref" mty stt
  | StTypRawPtr (mty, stt) -> print_location_type "ptr" mty stt
  | StTypProd (id, es) -> print_prod ptb print_st_typ id es

let rec print_term ptb = function
  | TmVal v -> print_val ptb v
  | TmVar id -> print_id ptb id
  | TmLet (mty, id, stt, ta, tb) ->
      print_kwd ptb "let";
      ptb.box_o ();
      ptb.space ();
      print_kwd ptb (mutability_to_string mty);
      ptb.space ();
      print_id ptb id;
      print_kwd ptb ":";
      print_st_typ ptb stt;
      print_kwd ptb "=";
      ptb.space ();
      print_term ptb ta;
      ptb.space ();
      print_kwd ptb "in";
      ptb.space ();
      print_term ptb tb;
      ptb.box_c ();
      ptb.space ();
      print_kwd ptb "end"
  | TmInLet (id, tb) ->
      print_kwd ptb "inlet";
      ptb.box_o ();
      ptb.space ();
      print_id ptb id;
      ptb.space ();
      print_kwd ptb "do";
      ptb.space ();
      print_term ptb tb;
      ptb.box_c ();
      ptb.space ();
      print_kwd ptb "end"
  | TmFin (tb, tp) ->
      print_kwd ptb "try";
      ptb.box_o ();
      ptb.space ();
      print_term ptb tb;
      ptb.space ();
      print_kwd ptb "finally";
      ptb.space ();
      print_term ptb tp;
      ptb.box_c ();
      ptb.space ();
      print_kwd ptb "end"
  | TmDrop t ->
      print_kwd ptb "drop";
      ptb.box_o ();
      ptb.space ();
      print_term ptb t;
      ptb.box_c ()
  | TmAssign (tl, tr) ->
      ptb.box_o ();
      print_term ptb tl;
      print_kwd ptb " =";
      ptb.space ();
      print_term ptb tr;
      ptb.box_c ()
  | TmRef (mty, t) ->
      ptb.box_o ();
      print_kwd ptb ("& " ^ mutability_to_string mty);
      print_term ptb t;
      ptb.box_c ()
  | TmDref t ->
      ptb.box_o ();
      print_kwd ptb "* ";
      print_term ptb t;
      ptb.box_c ()
  | TmProd (id, es) -> print_prod ptb print_term id es
  | TmSeq (t1, t2) ->
      print_term ptb t1;
      print_kwd ptb ";";
      ptb.space ();
      print_term ptb t2
  | TmGhost gt -> (
      let print_gt_rlz kwd id =
        print_kwd ptb kwd;
        ptb.box_o ();
        ptb.space ();
        print_id ptb id;
        ptb.box_c ()
      in
      match gt with
      | GtRealize id -> print_gt_rlz "realize" id
      | GtUnRealize id -> print_gt_rlz "unrealize" id)

let print_st_ctx ptb stctx =
  let pf = print_id ptb in
  let ps = print_st_typ ptb in
  let pmap () = print_kwd ptb ":" in
  let sep () =
    print_kwd ptb ",";
    ptb.space ()
  in
  print_assoc pf ps pmap sep stctx

let print_dy_ctx ptb dyctx =
  let pf = print_id ptb in
  let ps = print_sym ptb in
  let pmap () = print_kwd ptb ":" in
  let sep () =
    print_kwd ptb ",";
    ptb.space ()
  in
  print_assoc pf ps pmap sep dyctx

let print_smem ptb smem =
  let pf = print_sym ptb in
  let ps (v, perm) =
    ptb.box_o ();
    print_val ptb v;
    print_kwd ptb "[";
    print_perm ptb perm;
    print_kwd ptb "]";
    ptb.box_c ()
  in
  let pmap () = print_kwd ptb ":" in
  let sep () =
    print_kwd ptb ",";
    ptb.space ()
  in
  print_assoc pf ps pmap sep smem

let print_path_cond ptb pcond = (fun _ _ -> ()) ptb pcond
(***@todo: complete this*)

let print_rll ptb rll =
  let pe = print_id ptb in
  let sep () =
    print_kwd ptb ",";
    ptb.space ()
  in
  print_list pe sep rll

let print_sym_ctx ptb (dctx, smem, pcond, rll) =
  let pr_component content =
    ptb.box_o ();
    content ();
    ptb.box_c ();
    ptb.space ()
  in
  ptb.box_v_o ();

  pr_component (fun () ->
      print_info ptb "dyn ctx:";
      ptb.space ();
      print_dy_ctx ptb dctx);

  pr_component (fun () ->
      print_info ptb "sym mem:";
      ptb.space ();
      print_smem ptb smem);

  pr_component (fun () ->
      print_info ptb "path cond:";
      ptb.space ();
      print_path_cond ptb pcond);

  pr_component (fun () ->
      print_info ptb "realized vars:";
      ptb.space ();
      print_rll ptb rll);

  ptb.box_v_c ()

let print_state ptb (t, stctx, syctx) =
  let pr_txt content =
    ptb.box_o ();
    content ();
    ptb.box_c ();
    ptb.space ()
  in
  ptb.box_v_o ();
  pr_txt (fun () ->
      print_info ptb "term:";
      ptb.space ();
      print_term ptb t);

  pr_txt (fun () ->
      print_info ptb "static ctx:";
      ptb.space ();
      print_st_ctx ptb stctx);

  pr_txt (fun () ->
      print_info ptb "symbolic ctx:";
      ptb.space ();
      print_sym_ctx ptb syctx);

  ptb.box_v_c ()

type fmt = FmtShell | FmtLatex

module Shell = struct
  let esc = "\u{001B}"

  let shell_escape_ccolor_fg cc =
    let rgb8 = Color.ccolor_to_rgb8_string cc ";" in
    esc ^ "[38;2;" ^ rgb8 ^ "m"

  let shell_escape_ccolor_bg _ = ""
  (* let rgb8 = Color.ccolor_to_rgb8_string cc ";" in
     esc ^ "[48;2;" ^ rgb8 ^ "m" *)

  let reset_fmt = esc ^ "[0m"

  type txt_color = { fg : Color.ccolor; bg : Color.ccolor }

  type stag += StagColor of txt_color

  let mark_o_stag stag =
    match stag with
    | StagColor { fg; bg } ->
        shell_escape_ccolor_fg fg ^ shell_escape_ccolor_bg bg
    | _ -> ""

  let mark_c_stag _ = reset_fmt
end

let print_tool_box_shell formatter =
  pp_set_mark_tags formatter true;
  let { print_open_stag = pr_o; print_close_stag = pr_c; _ } =
    pp_get_formatter_stag_functions formatter ()
  in
  let fmt_stag_funs =
    {
      mark_open_stag = Shell.mark_o_stag;
      mark_close_stag = Shell.mark_c_stag;
      print_open_stag = pr_o;
      print_close_stag = pr_c;
    }
  in
  pp_set_formatter_stag_functions formatter fmt_stag_funs;
  {
    stt_o =
      (fun () ->
        pp_open_stag formatter (Shell.StagColor { fg = BrBlue; bg = Black }));
    stt_c = pp_close_stag formatter;
    val_o =
      (fun () ->
        pp_open_stag formatter (Shell.StagColor { fg = Green; bg = Black }));
    val_c = pp_close_stag formatter;
    kwd_o =
      (fun () ->
        pp_open_stag formatter (Shell.StagColor { fg = BrWhite; bg = Black }));
    kwd_c = pp_close_stag formatter;
    id_o =
      (fun () ->
        pp_open_stag formatter (Shell.StagColor { fg = BrMagenta; bg = Black }));
    id_c = pp_close_stag formatter;
    perm_o =
      (fun () ->
        pp_open_stag formatter (Shell.StagColor { fg = BrCyan; bg = Black }));
    perm_c = pp_close_stag formatter;
    print_string = (fun str -> pp_print_string formatter str);
    space = pp_print_space formatter;
    box_o = (fun () -> pp_open_hovbox formatter 2 (*indent*));
    box_c = pp_close_box formatter;
    box_v_o = (fun () -> pp_open_vbox formatter 0);
    box_v_c = pp_close_box formatter;
    info_o =
      (fun () ->
        pp_open_stag formatter (Shell.StagColor { fg = White; bg = Black }));
    info_c = pp_close_stag formatter;
    flush = pp_print_flush formatter;
  }

let make_print_toolbox fmt formatter =
  match fmt with
  | FmtShell -> print_tool_box_shell formatter
  | FmtLatex -> assert false

open Type
open Syntax

let fn_create id sign body : fn_def = { id; sign; body }

module StdeCellNatExample = struct
  let td_cell_nat = ("CellNat", TdbStruct ([], [ TypSynNat ]))

  let fn_new =
    fn_create "new"
      {
        safety = Safe;
        lft_params = [];
        lft_req = [];
        params = [ ("v", TypSynPtr (PkOwn, TypSynNat)) ];
        ret = TypSynPtr (PkOwn, TypSynDef ("CellNat", []));
      }
      [
        (*** Entry: let *r = CellNat<>{*v};goto L1*)
        ( "Entry",
          StIns (InsCrStruct ("r", TypSynDef ("CellNat", []), [ "v" ]), "L1") );
        (*** L1: return r *)
        ("L1", StRet "r");
      ]

  let fn_get =
    fn_create "get"
      {
        safety = Safe;
        lft_params = [ "alpha" ];
        lft_req = [];
        params =
          [
            ( "this",
              TypSynPtr (PkRef (RkImmut, "alpha"), TypSynDef ("CellNat", [])) );
          ];
        ret = TypSynPtr (PkOwn, TypSynNat);
      }
      [
        (*** Entry: let {*imm_value} = *this;goto L1 *)
        ("Entry", StIns (InsFieldAcc ([ "imm_value" ], "this"), "L1"));
        (*** L1: let *r = copy *imm_value;goto L2 *)
        ("L1", StIns (InsCopy ("r", "imm_value"), "L2"));
        (*** L2: drop imm_value;goto L3 *)
        ("L2", StIns (InsDrop "imm_value", "L3"));
        (*** L3: return r*)
        ("L3", StRet "r");
      ]

  let fn_set =
    fn_create "set"
      {
        safety = Safe;
        lft_params = [ "alpha" ];
        lft_req = [];
        params =
          [
            ( "this",
              TypSynPtr (PkRef (RkImmut, "alpha"), TypSynDef ("CellNat", [])) );
            ("v", TypSynPtr (PkOwn, TypSynNat));
          ];
        ret = TypSynPtr (PkOwn, typ_syn_unit);
      }
      [
        (*** Entry: let {*imm_value} = *this;goto L1*)
        ("Entry", StIns (InsFieldAcc ([ "imm_value" ], "this"), "L1"));
        (*** L1: let ptr_value = raw imm_value; L2 *)
        ("L1", StIns (InsCrRaw ("ptr_value", "imm_value"), "L2"));
        (*** L2: unsafe;goto L3 *)
        ("L2", StIns (InsUnsafe, "L3"));
        (*** L3: intro beta;goto L4 *)
        ("L3", StIns (InsIntro "beta", "L4"));
        (*** L4: let mut_value = mutbor'beta ptr_value;goto L5 *)
        ("L4", StIns (InsMutBor ("mut_value", "beta", "ptr_value"), "L5"));
        (*** L5: safe;goto L6 *)
        ("L5", StIns (InsSafe, "L6"));
        (*** L6: swap( *mut_value, *v);goto L7 *)
        ("L6", StIns (InsSwap ("mut_value", "v"), "L7"));
        (*** L7: drop mut_value;goto L8 *)
        ("L7", StIns (InsDrop "mut_value", "L8"));
        (*** L8: now beta;goto L9 *)
        ("L8", StIns (InsNow "beta", "L9"));
        (*** L9: drop ptr_value;goto L10 *)
        ("L9", StIns (InsDrop "ptr_value", "L10"));
        (*** L10: drop imm_value;goto L11 *)
        ("L10", StIns (InsDrop "Imm_value", "L11"));
        (*** L11: drop v;goto L12 *)
        ("L11", StIns (InsDrop "v", "L12"));
        (*** L12: let *r = unit<>{};goto L13 *)
        ("L12", StIns (InsCrStruct ("r", typ_syn_unit, []), "L13"));
        (*** L13: return r *)
        ("L13", StRet "r");
      ]
end

module ProgCellNatExample = struct
  let typ_defs = StdeCellNatExample.td_cell_nat :: reserved_typ_defs

  let fn_main =
    fn_create "main"
      {
        safety = Safe;
        lft_params = [];
        lft_req = [];
        params = [];
        ret = TypSynPtr (PkOwn, typ_syn_unit);
      }
      [
        (*** Entry: let *v = 42;goto L1 *)
        ("Entry", StIns (InsConst ("v", CvNat 42), "L1"));
        (*** L1: let c1 = new<>(v);goto L2 *)
        ("L1", StIns (InsFnCall ("c1", "new", [], [ "v" ]), "L2"));
        (*** L2: intro alpha;goto L3 *)
        ("L2", StIns (InsIntro "alpha", "L3"));
        (*** L3: let imm_c1 = mutbor'alpha c1;goto L4 *)
        ("L3", StIns (InsMutBor ("imm_c1", "alpha", "c1"), "L4"));
        (*** L4: immut imm_c1;goto L5 *)
        ("L4", StIns (InsImmut "imm_c1", "L5"));
        (*** L5: let *imm_c1_1 = copy *imm_c1;goto L6 *)
        ("L5", StIns (InsCopy ("imm_c1_1", "imm_c1"), "L6"));
        (*** L6: let *v = 43;goto L7 *)
        ("L6", StIns (InsConst ("v", CvNat 43), "L7"));
        (*** L7: let dummy = set<alpha>(imm_c1_1, v);goto L8 *)
        ( "L7",
          StIns
            (InsFnCall ("dummy", "set", [ "alpha" ], [ "imm_c1_1"; "v" ]), "L8")
        );
        (*** L8: drop dummy;goto L9 *)
        ("L8", StIns (InsDrop "dummy", "L9"));
        (*** L9: let v = get<alpha>(imm_c1);goto L10 *)
        ("L9", StIns (InsFnCall ("v", "get", [ "alpha" ], [ "imm_c1" ]), "L10"));
        (*** L10: now alpha;goto L11 *)
        ("L10", StIns (InsNow "alpha", "L11"));
        (*** L11: drop v;goto L12 *)
        ("L11", StIns (InsDrop "v", "L12"));
        (*** L12: drop c1;goto L13 *)
        ("L12", StIns (InsDrop "c1", "L13"));
        (*** L13: let *r = unit<>{};goto L14 *)
        ("L13", StIns (InsCrStruct ("r", typ_syn_unit, []), "L14"));
        (*** L14: return r *)
        ("L14", StRet "r");
      ]
end
(*
 module RcIntExample = struct
     let typ_cell_int = TypRec ("Cell_Int", [ ("value", TypInt) ])

     let fn_def_cell_int_new =
       fn_create "cell_int_new"
         {
           safety = Safe;
           lft_params = [];
           lft_req = [];
           params = [ ("value", TypPtr (PkOwn, TypInt)) ];
           ret = typ_cell_int;
         }
         [
           ( "Entry",
             StIns (InsCrRec ("r", "Cell_Int", [ ("value", "value") ]), "L1") );
           ("L1", StRet "r");
         ]

     let typ_rc_box_int =
       TypRec ("RcBox_Int", [ ("strong", typ_cell_int); ("value", TypInt) ])

     let typ_rc_int = TypRec ("Rc_Int", [ ("ptr", TypPtr (PkRaw, typ_rc_box_int)) ])

     let fn_def_rc_int_new =
       fn_create "create_rc_int"
         {
           lft_params = [];
           lft_req = [];
           params = [ ("x", TypPtr (PkOwn, TypInt)) ];
           ret = typ_rc_int;
         }
         [ ("Entry", StIns (InsConst ("count", CvInt 1), "L1")) ]

     let fn_def_main =
       fn_create "main"
         { lft_params = []; lft_req = []; params = []; ret = TypInt }
         [ ("entry", StIns (InsConst ("y", CvUnit), "L1")) ]
   end *)

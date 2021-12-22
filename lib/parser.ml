open Type
open Syntax

let fn_create id sign body : fn_def = { id; sign; body }

module StdeCellNatExample = struct
  let typ_cell_nat = TypStruct ("CellNat", [ TypNat ])

  let fn_new =
    fn_create "new"
      {
        safety = Safe;
        lft_params = [];
        lft_req = [];
        params = [ ("v", TypPtr (PkOwn, TypNat)) ];
        ret = TypPtr (PkOwn, TypId "CellNat");
      }
      [
        ("Entry", StIns (InsCrStruct ("r", TypId "CellNat", [ "v" ]), "L1"));
        ("L1", StRet "r");
      ]

  let fn_get =
    fn_create "get"
      {
        safety = Safe;
        lft_params = [ "alpha" ];
        lft_req = [];
        params =
          [ ("this", TypPtr (PkRef (RkImmut, "alpha"), TypId "CellNat")) ];
        ret = TypPtr (PkOwn, TypNat);
      }
      [
        ("Entry", StIns (InsFieldAcc ([ "imm_value" ], "this"), "L1"));
        ("L1", StIns (InsCopy ("r", "imm_value"), "L2"));
        ("L2", StIns (InsDrop "imm_value", "L3"));
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
            ("this", TypPtr (PkRef (RkImmut, "alpha"), TypId "CellNat"));
            ("v", TypPtr (PkOwn, TypNat));
          ];
        ret = TypPtr (PkOwn, TypId "unit");
      }
      [
        ("Entry", StIns (InsFieldAcc ([ "imm_value" ], "this"), "L1"));
        ("L1", StIns (InsCrRaw ("ptr_value", "imm_value"), "L2"));
        ("L2", StIns (InsUnsafe, "L3"));
        ("L3", StIns (InsIntro "beta", "L4"));
        ("L4", StIns (InsMutBor ("mut_value", "beta", "ptr_value"), "L5"));
        ("L5", StIns (InsSafe, "L6"));
        ("L6", StIns (InsSwap ("mut_value", "v"), "L7"));
        ("L7", StIns (InsDrop "mut_value", "L8"));
        ("L8", StIns (InsNow "beta", "L9"));
        ("L9", StIns (InsDrop "ptr_value", "L10"));
        ("L10", StIns (InsDrop "Imm_value", "L11"));
        ("L11", StIns (InsDrop "v", "L12"));
        ("L12", StIns (InsCrStruct ("r", TypId "unit", []), "L13"));
        ("L13", StRet "r");
      ]
end

module ProgCellNatExample = struct
  let typ_defs = [ StdeCellNatExample.typ_cell_nat ]

  let fn_main =
    fn_create "main"
      {
        safety = Safe;
        lft_params = [];
        lft_req = [];
        params = [];
        ret = TypPtr (PkOwn, TypId "unit");
      }
      [
        ("Entry", StIns (InsConst ("v", CvNat 42), "L1"));
        ("L1", StIns (InsFnCall ("c1", "new", [], [ "v" ]), "L2"));
        ("L2", StIns (InsIntro "alpha", "L3"));
        ("L3", StIns (InsMutBor ("imm_c1", "alpha", "c1"), "L4"));
        ("L4", StIns (InsImmut "imm_c1", "L5"));
        ("L5", StIns (InsConst ("v", CvNat 43), "L6"));
        ( "L6",
          StIns
            (InsFnCall ("dummy", "set", [ "alpha" ], [ "imm_c1"; "v" ]), "L7")
        );
        ("L7", StIns (InsDrop "dummy", "L8"));
        ("L8", StIns (InsFnCall ("v", "get", [ "alpha" ], [ "c1_imm" ]), "L9"));
        ("L9", StIns (InsDrop "v", "L10"));
        ("L10", StIns (InsDrop "imm_c1", "L11"));
        ("L11", StIns (InsNow "alpha", "L12"));
        ("L12", StIns (InsCrStruct ("r", TypId "unit", []), "L13"));
        ("L13", StRet "r");
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

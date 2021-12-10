open Type
open Syntax

let fn_create id sign body : fn_def = { id; sign; body }

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
end

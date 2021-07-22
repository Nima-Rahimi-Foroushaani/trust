open Trust
open Ast

let var_read =
  TmSeq (TmLet (MtImm, Id.make "x", unit_st, TmVal unit_v), TmVar (Id.make "x"))

let imm_ref =
  TmSeq
    ( TmLet (MtImm, Id.make "x", unit_st, TmVal unit_v),
      TmSeq
        ( TmLet
            ( MtImm,
              Id.make "xr",
              StTypRef (MtImm, unit_st),
              TmRef (MtImm, TmVar (Id.make "x")) ),
          TmDref (TmVar (Id.make "xr")) ) )

let unsafe_deref_fn_fail =
  {
    name = "unsafe_deref_fn_fail";
    rep = { pre = PrdTrue; post = PrdTrue };
    params = [ (Id.make "x", StTypRef (MtImm, unit_st)) ];
    body =
      TmSeq
        ( TmLet
            ( MtImm,
              Id.make "ptr",
              StTypRawPtr (MtImm, unit_st),
              TmVar (Id.make "x") ),
          TmDref (TmVar (Id.make "ptr")) );
  }
(* pub fn unsafe_deref_fn_fail (x: & /*Imm*/ () ) -> () /* () is the unit type */
   //@ requires true
   //@ ensures true
   {
       let /*Imm*/ ptr: *const () = x;
       unsafe {
           *ptr
       }
   }*)

let unsafe_deref_fn_pass =
  {
    name = "unsafe_deref_fn_pass";
    rep = { pre = PrdTrue; post = PrdTrue };
    params = [ (Id.make "x", StTypRef (MtImm, unit_st)) ];
    body =
      TmSeq
        ( TmLet
            ( MtImm,
              Id.make "ptr",
              StTypRawPtr (MtImm, unit_st),
              TmVar (Id.make "x") ),
          TmSeq
            (TmGhost (GtRealize (Id.make "x")), TmDref (TmVar (Id.make "ptr")))
        );
  }
(*pub fn unsafe_deref_fn_pass (x: & /*Imm*/ () ) -> () /* () is the unit type */
  //@ requires true
  //@ ensures true
  {
      let /*Imm*/ ptr: *const () = x;
      unsafe {
          /* @realize x; */
          *ptr
      }
  } *)

let () = print_endline "tRust 0.0.0"

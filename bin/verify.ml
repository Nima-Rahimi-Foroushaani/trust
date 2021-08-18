open Trust
open Ast

(***@todo: handle return value*)
(***@todo: handle mutability of function parameters themselves*)

(*
pub fn simple_i32_shared_pass(/*Imm*/ x: & /*Imm*/ i32, /*Imm*/ y: & /*Imm*/ i32) -> i32
//@ requires true;
//@ ensures true;
{
    let mut ptr: *const i32 = x;
    {
        /* some complex code using "ptr" and "n". really complex! believe me! */
        let /*Imm*/ n: i32 = 43;
        ptr = y;
    }
    unsafe{
        //@ realize y;
        *ptr
    }
}
*)
let simple_i32_shared_pass =
  {
    name = Id.make "simple_i32_shared_pass";
    rep = { pre = PropTrue; post = PropTrue };
    params =
      [
        (Id.make "x", StTypRef (MtImm, StTypInt));
        (Id.make "y", StTypRef (MtImm, StTypInt));
      ];
    body =
      TmLet
        ( MtMut,
          Id.make "ptr",
          StTypRawPtr (MtImm, StTypInt),
          TmVar (Id.make "x"),
          TmSeq
            ( TmLet
                ( MtImm,
                  Id.make "n",
                  StTypInt,
                  TmVal (VluInt (Symbol.make "43")),
                  TmAssign (TmVar (Id.make "ptr"), TmVar (Id.make "y")) ),
              TmSeq
                ( TmGhost (GtRealize (Id.make "y")),
                  TmDref (TmVar (Id.make "ptr")) ) ) );
  }

(*
pub fn simple_i32_shared_fail(/*Imm*/ x: & /*Imm*/ i32) -> i32
//@ requires true;
//@ ensures true;
{
    let mut ptr: *const i32 = x;
    {
        let /*Imm*/ n: i32 = 43;
        /* some complex code using "ptr" and "n". really complex! believe me! */
        ptr = & /*Imm*/ n;
    }
    unsafe {
        *ptr
    }
}
*)
let simple_i32_shared_fail =
  {
    name = Id.make "simple_i32_shared_fail";
    rep = { pre = PropTrue; post = PropTrue };
    params = [ (Id.make "x", StTypRef (MtImm, StTypInt)) ];
    body =
      TmLet
        ( MtMut,
          Id.make "ptr",
          StTypRawPtr (MtImm, StTypInt),
          TmVar (Id.make "x"),
          TmSeq
            ( TmLet
                ( MtImm,
                  Id.make "n",
                  StTypInt,
                  TmVal (VluInt (Symbol.make "43")),
                  TmAssign
                    (TmVar (Id.make "ptr"), TmRef (MtImm, TmVar (Id.make "n")))
                ),
              TmDref (TmVar (Id.make "ptr")) ) );
  }

let _ = print_endline "tRust 0.0.0"

let _ = Fun_verify.verify simple_i32_shared_pass

let _ = Fun_verify.verify simple_i32_shared_fail

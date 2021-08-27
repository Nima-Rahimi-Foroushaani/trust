open Trust
open Ast

(***@todo: handle return value*)
(***@todo: handle mutability of function parameters themselves*)
(***@todo: there is an inconsistency between the formalization and tRust implementation for the
  "realize" and "unrealize" ghost terms. In the formalization, the body of command can contain any kind of
  therm and then only the ones with variable names as their body have a defined semantic.
  On the other hand, in implementation, these gosht terms only accept ids as their body.
  Change implementation to coincide with formalization*)

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

let main () =
  let _ = print_endline "tRust 0.0.0" in
  let open Output in
  let ptb = make_print_toolbox FmtShell Format.std_formatter in
  let print_state = print_state ptb in
  let _ = Fun_verify.verify simple_i32_shared_pass print_state in
  (* let _ = Fun_verify.verify simple_i32_shared_fail print_state in *)
  exit 0
;;

main ()

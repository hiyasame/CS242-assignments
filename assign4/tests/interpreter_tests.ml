open Core
open Poly
open Ast

let parse = Parser.parse_expr_exn

let check_expr expected actual =
  if actual <> expected then
    failwith (Printf.sprintf "Expected %s, got %s"
      (Expr.to_string expected) (Expr.to_string actual))

let check_step source expected =
  match Interpreter.trystep (parse source) with
  | Interpreter.Step actual -> check_expr (parse expected) actual
  | Interpreter.Val -> failwith "Expected a step, got Val"

let check_eval source expected =
  let e = parse source in
  (match Typecheck.typecheck e with
   | Ok _ -> ()
   | Error message -> failwith message);
  match Interpreter.eval e with
  | Ok actual -> check_expr (parse expected) actual
  | Error message -> failwith message

let check_substitute variable replacement source expected =
  let actual = Ast_util.Expr.substitute variable (parse replacement) (parse source) in
  if not (Ast_util.Expr.aequiv actual (parse expected)) then
    failwith (Printf.sprintf "Expected alpha-equivalent to %s, got %s"
      expected (Expr.to_string actual))

let failures = ref 0
let count = ref 0

let test name f =
  incr count;
  try f (); Printf.printf "PASS %s\n" name
  with exn ->
    incr failures;
    Printf.printf "FAIL %s: %s\n" name (Exn.to_string exn)

let () =
  List.iter [
    ("numeric equality", "1 = 2", "false");
    ("numeric less-than", "2 < 3", "true");
    ("numeric greater-than", "3 > 2", "true");
    ("relop steps left first", "(1 + 2) < (3 + 4)", "3 < (3 + 4)");
    ("relop steps right", "3 < (3 + 4)", "3 < 7");
    ("if steps condition", "if (1 = 1) then 4 else 5", "if true then 4 else 5");
    ("if selects then", "if true then (1 + 2) else (1 / 0)", "1 + 2");
    ("if selects else", "if false then (1 / 0) else (2 + 3)", "2 + 3");
    ("and evaluates right even if left is false", "false && (1 = 1)", "false && true");
    ("or evaluates right even if left is true", "true || (1 = 1)", "true || true");
    ("app steps function only",
     "(if true then (fun (x : num) -> x) else (fun (y : num) -> y)) (1 + 2)",
     "(fun (x : num) -> x) (1 + 2)");
    ("app substitutes unevaluated argument", "(fun (x : num) -> x + x) (1 + 2)",
     "(1 + 2) + (1 + 2)");
    ("project steps pair expression", "(if true then (1, 2) else (3, 4)).R", "(1, 2).R");
    ("project selects left lazily", "(1 + 2, 1 / 0).L", "1 + 2");
    ("project selects right lazily", "(1 / 0, 2 + 3).R", "2 + 3");
    ("case steps scrutinee",
     "case (if true then (inj 1 = L as num + bool) else (inj false = R as num + bool)) { L(x) -> x | R(b) -> 0 }",
     "case (inj 1 = L as num + bool) { L(x) -> x | R(b) -> 0 }");
    ("case substitutes left payload",
     "case (inj (1 + 2) = L as num + bool) { L(x) -> x + 10 | R(b) -> 0 }",
     "(1 + 2) + 10");
    ("case substitutes right payload",
     "case (inj false = R as num + bool) { L(x) -> 0 | R(b) -> if b then 1 else 2 }",
     "if false then 1 else 2");
    ("type application steps function",
     "(if true then (tyfun a -> 1) else (tyfun b -> 2)) [num]", "(tyfun a -> 1) [num]");
    ("type application erases type abstraction",
     "(tyfun a -> fun (x : a) -> x) [num]", "fun (x : a) -> x");
    ("unfold steps operand",
     "unfold (if true then (fold 1 as rec a . num) else (fold 2 as rec a . num))",
     "unfold (fold 1 as rec a . num)");
    ("unfold exposes unevaluated payload", "unfold (fold (1 + 2) as rec a . num)", "1 + 2");
    ("import steps module",
     "import (x, a) = (if true then (export 1 without num as exists t . t) else (export 2 without num as exists t . t)) in x",
     "import (x, a) = (export 1 without num as exists t . t) in x");
    ("import substitutes unevaluated payload",
     "import (x, a) = (export (1 + 2) without num as exists t . t) in x", "1 + 2");
  ] ~f:(fun (name, source, expected) -> test name (fun () -> check_step source expected));

  test "fix substitutes the whole fixpoint in one step" (fun () ->
    let body = Expr.Binop {binop = Expr.Add; left = Expr.Var "f"; right = Expr.Num 1} in
    let fix = Expr.Fix {x = "f"; tau = Type.Num; e = body} in
    match Interpreter.trystep fix with
    | Interpreter.Step actual ->
      check_expr (Expr.Binop {binop = Expr.Add; left = fix; right = Expr.Num 1}) actual
    | Interpreter.Val -> failwith "Fixpoint must step");

  List.iter [
    "(1 + 2, 1 / 0)";
    "inj (1 / 0) = L as num + bool";
    "fold (1 / 0) as rec a . num";
    "export (1 / 0) without num as exists a . a";
  ] ~f:(fun source -> test ("lazy value: " ^ source) (fun () ->
    assert (Interpreter.trystep (parse source) = Interpreter.Val)));

  List.iter [
    ("arithmetic and relations", "if ((1 + 2) = 3) && ((4 > 2) || false) then 9 else 0", "9");
    ("unused argument is not evaluated", "(fun (x : num) -> 7) (1 / 0)", "7");
    ("sum elimination", "case (inj 4 = L as num + bool) { L(x) -> x + 1 | R(b) -> 0 }", "5");
    ("recursive factorial", "letrec f : num -> num = fun (n : num) -> if n = 0 then 1 else n * (f (n - 1)) in (f 5)", "120");
    ("polymorphic identity", "((tyfun a -> fun (x : a) -> x) [num]) 8", "8");
    ("recursive type", "(unfold (fold (6, ()) as rec a . num * unit)).L", "6");
    ("existential package",
     "import (m, a) = (export (4, fun (x : num) -> x + 1) without num as exists t . t * (t -> num)) in (m.R m.L)", "5");
  ] ~f:(fun (name, source, expected) -> test name (fun () -> check_eval source expected));

  test "substitution replaces free variables" (fun () ->
    check_expr (Expr.Num 3) (Ast_util.Expr.substitute "x" (Expr.Num 3) (Expr.Var "x")));
  test "substitution leaves other variables free" (fun () ->
    check_expr (Expr.Var "y") (Ast_util.Expr.substitute "x" (Expr.Num 3) (Expr.Var "y")));
  test "de Bruijn indices distinguish shadowing and free variables" (fun () ->
    let expected = Expr.Lam {x = "_"; tau = Type.Var "_"; e =
      Expr.Lam {x = "_"; tau = Type.Var "_"; e =
        Expr.Pair {left = Expr.Var "1";
          right = Expr.Pair {left = Expr.Var "0"; right = Expr.Var "free"}}}} in
    check_expr expected (Ast_util.Expr.to_debruijn
      (parse "fun (x : num) -> fun (y : num) -> (x, (y, free))")));
  test "type binders do not affect term indices" (fun () ->
    let expected = Expr.Lam {x = "_"; tau = Type.Var "_"; e =
      Expr.TyLam {a = "_"; e = Expr.Var "0"}} in
    check_expr expected (Ast_util.Expr.to_debruijn (parse "fun (x : num) -> tyfun a -> x")));
  test "alpha equivalence distinguishes variable scope" (fun () ->
    assert (not (Ast_util.Expr.aequiv
      (parse "fun (x : num) -> fun (x : num) -> x")
      (parse "fun (x : num) -> fun (y : num) -> x"))));
  List.iter [
    ("lambda shadowing", "x", "3", "fun (x : num) -> x", "fun (z : num) -> z");
    ("capture avoidance", "x", "y", "fun (y : num) -> x + y", "fun (z : num) -> y + z");
    ("nested shadowing", "x", "y", "fun (y : num) -> fun (y : num) -> x + y",
     "fun (a : num) -> fun (b : num) -> y + b");
    ("case binder scope", "x", "3", "case x { L(x) -> x | R(y) -> x }",
     "case 3 { L(z) -> z | R(y) -> 3 }");
    ("import binder scope", "x", "3", "import (x, a) = x in x",
     "import (z, a) = 3 in z");
    ("replacement is not recursively substituted", "x", "x + 1", "x + x", "(x + 1) + (x + 1)");
  ] ~f:(fun (name, variable, replacement, source, expected) ->
    test name (fun () -> check_substitute variable replacement source expected));

  test "fix binder shadows substitution" (fun () ->
    let fix = Expr.Fix {x = "x"; tau = Type.Num; e = Expr.Var "x"} in
    assert (Ast_util.Expr.aequiv fix (Ast_util.Expr.substitute "x" (Expr.Num 3) fix)));
  Printf.printf "\n%d/%d tests passed\n" (!count - !failures) !count;
  if !failures > 0 then exit 1

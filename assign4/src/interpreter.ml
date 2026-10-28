open Flags_util
open Core
open Poly
open Ast

type outcome =
  | Step of Expr.t
  | Val

exception RuntimeError of string

let rec trystep (e : Expr.t) : outcome =
  match e with
  | (Expr.Lam _ | Expr.Num _ | Expr.True | Expr.False | Expr.Pair _ | Expr.Unit
    | Expr.Inject _ | Expr.TyLam _ | Expr.Export _ | Expr.Fold_ _) -> Val

  | Expr.Binop {binop; left; right} ->
    (left, fun left' -> Expr.Binop {left = left'; binop; right;}) |-> fun () ->
    (right, (fun right' -> Expr.Binop {right = right'; binop; left})) |-> fun () ->
    let (Expr.Num n1, Expr.Num n2) = (left, right) in
    let f = match binop with
      | Expr.Add -> (+)
      | Expr.Sub -> (-)
      | Expr.Mul -> ( * )
      | Expr.Div -> (/)
    in
    Step (Expr.Num (f n1 n2) )

  | Expr.If {cond; then_; else_} ->
    (cond, fun cond' -> Expr.If {cond = cond'; then_; else_}) |-> fun () ->
    (match cond with
     | Expr.True -> Step then_
     | Expr.False -> Step else_
     | _ -> raise (RuntimeError "Expected a bool"))

  | Expr.Relop {relop; left; right} ->
    (left, fun left' -> Expr.Relop {relop; left = left'; right}) |-> fun () ->
    (right, (fun right' -> Expr.Relop {relop; right = right'; left})) |-> fun () ->
    (match (left, right) with
     | (Expr.Num n1, Expr.Num n2) ->
       let result = match relop with
         | Expr.Eq -> n1 = n2
         | Expr.Lt -> n1 < n2
         | Expr.Gt -> n1 > n2
       in
       Step (if result then Expr.True else Expr.False)
     | _ -> raise (RuntimeError "Expected numeric operands"))

  | Expr.And {left; right} ->
    (left, fun left' -> Expr.And {left = left'; right}) |-> fun () ->
    (right, (fun right' -> Expr.And {right = right'; left})) |-> fun () ->
    let a = (left = Expr.True) in
    let b = (right = Expr.True) in
    Step (if a && b then Expr.True else Expr.False)

  | Expr.Or {left; right} ->
    (left, fun left' -> Expr.Or {left = left'; right}) |-> fun () ->
    (right, (fun right' -> Expr.Or {right = right'; left})) |-> fun () ->
    let a = (left = Expr.True) in
    let b = (right = Expr.True) in
    Step (if a || b then Expr.True else Expr.False)

  | Expr.App {lam; arg} ->
    (lam, fun lam' -> Expr.App {lam = lam'; arg}) |-> fun () ->
    (match lam with
     | Expr.Lam {x; e = body; _} -> Step (Ast_util.Expr.substitute x arg body)
     | _ -> raise (RuntimeError "Expected a function"))

  | Expr.Project {e; d} ->
    (e, fun e' -> Expr.Project {e = e'; d}) |-> fun () ->
    (match e with
     | Expr.Pair {left; right} ->
       Step (match d with Expr.Left -> left | Expr.Right -> right)
     | _ -> raise (RuntimeError "Expected a pair"))

  | Expr.Case {e; xleft; eleft; xright; eright} ->
    (e, fun e' -> Expr.Case {e = e'; xleft; eleft; xright; eright}) |-> fun () ->
    (match e with
     | Expr.Inject {e = payload; d; _} ->
       (match d with
        | Expr.Left -> Step (Ast_util.Expr.substitute xleft payload eleft)
        | Expr.Right -> Step (Ast_util.Expr.substitute xright payload eright))
     | _ -> raise (RuntimeError "Expected an injection"))

  | Expr.Fix {x; e = body; _} ->
    (* Unroll once, replacing recursive uses with the whole fixpoint. *)
    Step (Ast_util.Expr.substitute x e body)

  | Expr.TyApp {e; tau} ->
    (e, fun e' -> Expr.TyApp {e = e'; tau}) |-> fun () ->
    (* The dynamic semantics erases type application without substituting types. *)
    (match e with
     | Expr.TyLam {e = body; _} -> Step body
     | _ -> raise (RuntimeError "Expected a type function"))

  | Expr.Unfold e ->
    (e, fun e' -> Expr.Unfold e') |-> fun () ->
    (match e with
     | Expr.Fold_ {e = body; _} -> Step body
     | _ -> raise (RuntimeError "Expected a folded value"))

  | Expr.Import {x; a; e_mod; e_body} ->
    (e_mod, fun e_mod' -> Expr.Import {x; a; e_mod = e_mod'; e_body}) |-> fun () ->
    (match e_mod with
     | Expr.Export {e = payload; _} ->
       Step (Ast_util.Expr.substitute x payload e_body)
     | _ -> raise (RuntimeError "Expected an exported module"))

  | _ -> raise (RuntimeError (
    Printf.sprintf "Reached a stuck state at expression: %s" (Expr.to_string e)))

and (|->) ((e, hole) : Expr.t * (Expr.t -> Expr.t)) (next : unit -> outcome)
  : outcome =
  match trystep e with Step e' -> Step (hole e') | Val -> next ()

let rec eval e =
  match trystep e with
  | Step e' ->
    (if extra_verbose () then
       Printf.printf "Stepped:\n%s\n|->\n%s\n\n"
         (Expr.to_string e) (Expr.to_string e'));
    eval e'
  | Val -> Ok e

let inline_tests () =
  let p = Parser.parse_expr_exn in
  let e1 = p "2 + 3" in
  assert (trystep e1 = Step(Expr.Num 5));

  let e2 = p "(fun (x : num) -> x) 3" in
  assert (trystep e2 = Step(Expr.Num 3))

(* Uncomment the line below when you want to run the inline tests. *)
(* let () = inline_tests () *)

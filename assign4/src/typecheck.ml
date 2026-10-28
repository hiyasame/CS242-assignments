open Flags_util
open Core
open Poly
open Result.Monad_infix
open Ast

let rec typecheck_expr (ctx : Type.t String.Map.t) (e : Expr.t)
  : (Type.t, string) Result.t =
  match e with
  | Expr.Num _ -> Ok Type.Num

  | Expr.Binop {left; right; _} ->
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
    (match (tau_left, tau_right) with
     | (Type.Num, Type.Num) -> Ok Type.Num
     | _ -> Error (
       Printf.sprintf
         "Binary operands have incompatible types: (%s : %s) and (%s : %s)"
         (Expr.to_string left) (Type.to_string tau_left)
         (Expr.to_string right) (Type.to_string tau_right)))

  (* Add more cases here! *)
  | Expr.True -> Ok Type.Bool
  | Expr.False -> Ok Type.Bool
  | Expr.If {cond; then_; else_} ->
    typecheck_expr ctx cond >>= fun tau_cond ->
    typecheck_expr ctx then_ >>= fun tau_then ->
    typecheck_expr ctx else_ >>= fun tau_else ->
    (match tau_cond with
     | Type.Bool ->
       if Ast_util.Type.aequiv tau_then tau_else
       then Ok tau_then
       else Error (Printf.sprintf
         "Then branch %s has type %s, not matching else branch type %s of type %s"
         (Expr.to_string then_) (Type.to_string tau_then)
         (Expr.to_string else_) (Type.to_string tau_else))
     | _ -> Error (Printf.sprintf
         "If condition expression %s has type %s, expected bool"
         (Expr.to_string cond) (Type.to_string tau_cond)))
  | Expr.Relop {relop = _; left; right} ->
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
    (match (tau_left, tau_right) with
     | (Type.Num, Type.Num) -> Ok Type.Bool
     | _ -> Error (Printf.sprintf
        "Relop operands have incompatible types: (%s : %s) and (%s : %s)"
        (Expr.to_string left) (Type.to_string tau_left)
        (Expr.to_string right) (Type.to_string tau_right)))
  | Expr.And {left; right} ->
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
    (match (tau_left, tau_right) with
     | (Type.Bool, Type.Bool) -> Ok Type.Bool
     | _ -> Error (Printf.sprintf
        "Logical operands have incompatible types: (%s : %s) and (%s : %s)"
        (Expr.to_string left) (Type.to_string tau_left)
        (Expr.to_string right) (Type.to_string tau_right)))
  | Expr.Or {left; right} ->
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
    (match (tau_left, tau_right) with
     | (Type.Bool, Type.Bool) -> Ok Type.Bool
     | _ -> Error (Printf.sprintf
        "Logical operands have incompatible types: (%s : %s) and (%s : %s)"
        (Expr.to_string left) (Type.to_string tau_left)
        (Expr.to_string right) (Type.to_string tau_right)))
  | Expr.Var var ->
    (match Map.find ctx var with
     | Some tau -> Ok tau
     | None -> Error (Printf.sprintf "Unbound variable %s" var))
  | Expr.Lam {x; tau; e} ->
    typecheck_expr (Map.set ctx ~key:x ~data:tau) e
      >>= fun ret -> Ok (Type.Fn {arg = tau; ret})
  | Expr.App {lam; arg} ->
    typecheck_expr ctx arg >>= fun arg_t ->
    typecheck_expr ctx lam >>= fun lam_t ->
    (match lam_t with
     | Type.Fn {arg = tau_arg; ret} ->
       if Ast_util.Type.aequiv tau_arg arg_t
       then Ok ret
       else Error (Printf.sprintf
         "Attempted to call function %s of expected argument type %s with argument expression %s of actual type %s"
         (Expr.to_string lam) (Type.to_string tau_arg)
         (Expr.to_string arg)   (Type.to_string arg_t))
     | _ -> Error (Printf.sprintf
         "Attempted to call expression %s of non-function type %s as a function"
         (Expr.to_string lam) (Type.to_string lam_t)))
  | Expr.Unit -> Ok Type.Unit
  | Expr.Pair {left; right} ->
    typecheck_expr ctx left >>= fun left_t ->
    typecheck_expr ctx right >>= fun right_t ->
        Ok (Type.Product { left = left_t; right= right_t })
  | Expr.Project {e; d} ->
    typecheck_expr ctx e >>= fun tau_e ->
    (match tau_e with
     | Type.Product {left; right} ->
       (match d with
        | Expr.Left -> Ok left
        | Expr.Right -> Ok right)
     | _ -> Error (Printf.sprintf
         "Attempted to project (.%s) from expression %s of non-product type %s"
         (match d with Expr.Left -> "L" | Expr.Right -> "R")
         (Expr.to_string e) (Type.to_string tau_e)))
  | Expr.Inject {e; d; tau} ->
     typecheck_expr ctx e >>= fun tau_e ->
        (match tau with
            | Type.Sum {left; right} ->
                let expected = (match d with Expr.Left -> left | Expr.Right -> right) in
                   if Ast_util.Type.aequiv tau_e expected
                   then Ok tau
                   else Error (Printf.sprintf
                                 "Inject (%s = %s as %s): expression %s has type %s, but the %s side of %s is %s"
                                 (Expr.to_string e)
                                 (match d with Expr.Left -> "L" | Expr.Right -> "R")
                                 (Type.to_string tau)
                                 (Expr.to_string e) (Type.to_string tau_e)
                                 (match d with Expr.Left -> "left" | Expr.Right -> "right")
                                 (Type.to_string tau) (Type.to_string expected))
            | _ -> Error (Printf.sprintf
                     "Inject annotation %s is not a sum type" (Type.to_string tau))
        )
  | Expr.Case {e; xleft; eleft; xright; eright;} ->
     typecheck_expr ctx e >>= fun tau_e ->
         (match tau_e with
             | Type.Sum {left; right} ->
               typecheck_expr (Map.set ctx ~key:xleft ~data:left) eleft >>= fun tau_left ->
               typecheck_expr (Map.set ctx ~key:xright ~data:right) eright >>= fun tau_right ->
               if Ast_util.Type.aequiv tau_left tau_right
               then Ok tau_left
               else Error (Printf.sprintf
                 "Case branches have different types: %s has type %s, but %s has type %s"
                 (Expr.to_string eleft) (Type.to_string tau_left)
                 (Expr.to_string eright) (Type.to_string tau_right))
             | _ -> Error (Printf.sprintf
                 "Case scrutinee %s has non-sum type %s"
                 (Expr.to_string e) (Type.to_string tau_e)))
  | Expr.Fix {x; tau; e} ->
     typecheck_expr (Map.set ctx ~key:x ~data:tau) e >>= fun tau_e ->
        if Ast_util.Type.aequiv tau_e tau
        then Ok tau
        else Error (Printf.sprintf
           "Fixpoint (%s : %s) has body %s of type %s, which does not match the annotation"
           x (Type.to_string tau) (Expr.to_string e) (Type.to_string tau_e))
  | Expr.TyLam {a; e} ->
    typecheck_expr ctx e >>= fun tau_e ->
    Ok (Type.Forall {a; tau = tau_e})
  | Expr.TyApp {e; tau} ->
    typecheck_expr ctx e >>= fun tau_e ->
    (match tau_e with
     | Type.Forall {a; tau = tau_body} ->
       Ok (Ast_util.Type.substitute a tau tau_body)
     | _ -> Error (Printf.sprintf
         "Attempted to apply a type to expression %s of non-universal type %s"
         (Expr.to_string e) (Type.to_string tau_e)))
  | Expr.Fold_ {e; tau} ->
    (match tau with
     | Type.Rec {a; tau = tau_body} ->
       let unfolded = Ast_util.Type.substitute a tau tau_body in
       typecheck_expr ctx e >>= fun tau_e ->
       if Ast_util.Type.aequiv tau_e unfolded
       then Ok tau
       else Error (Printf.sprintf
         "Fold of %s has type %s, but %s unfolds to %s"
         (Expr.to_string e) (Type.to_string tau_e)
         (Type.to_string tau) (Type.to_string unfolded))
     | _ -> Error (Printf.sprintf
         "Fold annotation %s is not a recursive type" (Type.to_string tau)))
  | Expr.Unfold e ->
    typecheck_expr ctx e >>= fun tau_e ->
    (match tau_e with
     | Type.Rec {a; tau} -> Ok (Ast_util.Type.substitute a tau_e tau)
     | _ -> Error (Printf.sprintf
         "Attempted to unfold expression %s of non-recursive type %s"
         (Expr.to_string e) (Type.to_string tau_e)))
  | Expr.Export {e; tau_adt; tau_mod} ->
    (match tau_mod with
     | Type.Exists {a; tau = rho} ->
       let hidden = Ast_util.Type.substitute a tau_adt rho in
       typecheck_expr ctx e >>= fun tau_e ->
       if Ast_util.Type.aequiv tau_e hidden
       then Ok tau_mod
       else Error (Printf.sprintf
         "Export of %s has type %s, but hiding %s in %s expects %s"
         (Expr.to_string e) (Type.to_string tau_e)
         (Type.to_string tau_adt) (Type.to_string tau_mod)
         (Type.to_string hidden))
     | _ -> Error (Printf.sprintf
         "Export annotation %s is not an existential type"
         (Type.to_string tau_mod)))
  | Expr.Import {x; a; e_mod; e_body} ->
    typecheck_expr ctx e_mod >>= fun tau_mod ->
    (match tau_mod with
     | Type.Exists {a = a_mod; tau = rho} ->
       (* The abstract type is named [a] inside the body. *)
       let rho' = Ast_util.Type.substitute a_mod (Type.Var a) rho in
       typecheck_expr (Map.set ctx ~key:x ~data:rho') e_body
     | _ -> Error (Printf.sprintf
         "Imported expression %s has non-existential type %s"
         (Expr.to_string e_mod) (Type.to_string tau_mod)))

let typecheck t = typecheck_expr String.Map.empty t

let inline_tests () =
  let p_ex = Parser.parse_expr_exn in
  let p_ty = Parser.parse_type_exn in
  let e1 = p_ex "fun (x : num) -> x" in
  assert (typecheck e1 = Ok(p_ty "num -> num"));

  let e2 = p_ex "fun (x : num) -> y" in
  assert (Result.is_error (typecheck e2));

  let t3 = p_ex "(fun (x : num) -> x) 3"in
  assert (typecheck t3 = Ok(p_ty "num"));

  let t4 = p_ex "((fun (x : num) -> x) 3) 3" in
  assert (Result.is_error (typecheck t4));

  let t5 = p_ex "0 + (fun (x : num) -> x)" in
  assert (Result.is_error (typecheck t5))

(* Uncomment the line below when you want to run the inline tests. *)
(* let () = inline_tests () *)

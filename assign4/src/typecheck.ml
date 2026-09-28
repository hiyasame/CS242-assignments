open Flags_util
open Core
open Poly
open Result.Monad_infix
open Ast

exception Unimplemented

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
  | _ -> raise Unimplemented

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

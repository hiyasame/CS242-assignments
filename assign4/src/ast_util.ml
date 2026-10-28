open Flags_util
open Core
open Poly

let fresh s = s ^ "'"

module Type = struct
  open Ast.Type

  (* Free type variables of a type, used to pick fresh names. *)
  let rec free_vars (tau : t) : String.Set.t =
    match tau with
    | Num | Bool | Unit -> String.Set.empty
    | Var x -> String.Set.singleton x
    | Fn {arg; ret} -> Set.union (free_vars arg) (free_vars ret)
    | Product {left; right}
    | Sum {left; right} -> Set.union (free_vars left) (free_vars right)
    | Rec {a; tau}
    | Forall {a; tau}
    | Exists {a; tau} -> Set.remove (free_vars tau) a

  (* Every name we must not collide with: names bound by enclosing binders,
     plus the free variables of the types they are replaced with. *)
  let used_names (rename : t String.Map.t) : String.Set.t =
    List.fold (Map.data rename)
      ~init:(String.Set.of_list (Map.keys rename))
      ~f:(fun acc tau -> Set.union acc (free_vars tau))

  let rec fresh_name (used : String.Set.t) (x : string) : string =
    if Set.mem used x then fresh_name used (fresh x) else x

  (* Enter a binder: rename [a] to a fresh name and extend [rename] so that
     occurrences of [a] in [body] now point at that fresh name. *)
  let rename_binder (rename : t String.Map.t) (a : string) (body : t)
    : string * t String.Map.t =
    let used = Set.union (used_names rename) (free_vars body) in
    let a' = fresh_name used a in
    let rename' =
      Map.set (Map.set rename ~key:a ~data:(Var a')) ~key:a' ~data:(Var a') in
    (a', rename')

  let rec substitute_map (rename : t String.Map.t) (tau : t) : t =
    match tau with
    | Num -> Num
    | Bool -> Bool
    | Unit -> Unit
    | Var x ->
      (match Map.find rename x with
       | Some tau' -> tau'
       | None -> Var x)
    | Fn {arg; ret} ->
      Fn {arg = substitute_map rename arg; ret = substitute_map rename ret}
    | Product {left; right} ->
      Product {
        left = substitute_map rename left;
        right = substitute_map rename right}
    | Sum {left; right} ->
      Sum {
        left = substitute_map rename left;
        right = substitute_map rename right}
    | Rec {a; tau} ->
      let (a', rename') = rename_binder rename a tau in
      Rec {a = a'; tau = substitute_map rename' tau}
    | Forall {a; tau} ->
      let (a', rename') = rename_binder rename a tau in
      Forall {a = a'; tau = substitute_map rename' tau}
    | Exists {a; tau} ->
      let (a', rename') = rename_binder rename a tau in
      Exists {a = a'; tau = substitute_map rename' tau}

  let substitute (x : string) (tau' : t) (tau : t) : t =
    substitute_map (String.Map.singleton x tau') tau

  (* Nameless representation: bound variables are replaced by the de Bruijn
     index of their binder (as a string), binders are renamed to "_", and
     free variables are left alone. *)
  let to_debruijn (tau : t) : t =
    let shift (depth : int String.Map.t) : int String.Map.t =
      Map.map depth ~f:(fun i -> i + 1)
    in
    let bind (depth : int String.Map.t) (a : string) : int String.Map.t =
      Map.set (shift depth) ~key:a ~data:0
    in
    let rec aux (depth : int String.Map.t) (tau : t) : t =
      match tau with
      | Num -> Num
      | Bool -> Bool
      | Unit -> Unit
      | Var x ->
        (match Map.find depth x with
         | Some i -> Var (Int.to_string i)
         | None -> Var x)
      | Fn {arg; ret} -> Fn {arg = aux depth arg; ret = aux depth ret}
      | Product {left; right} ->
        Product {left = aux depth left; right = aux depth right}
      | Sum {left; right} ->
        Sum {left = aux depth left; right = aux depth right}
      | Rec {a; tau} -> Rec {a = "_"; tau = aux (bind depth a) tau}
      | Forall {a; tau} -> Forall {a = "_"; tau = aux (bind depth a) tau}
      | Exists {a; tau} -> Exists {a = "_"; tau = aux (bind depth a) tau}
    in
    aux String.Map.empty tau

  let rec aequiv (tau1 : t) (tau2 : t) : bool =
    let rec aux (tau1 : t) (tau2 : t) : bool =
      match (tau1, tau2) with
      | (Num, Num) -> true
      | (Bool, Bool) | (Unit, Unit) -> true
      | (Var x, Var y) -> x = y
      | (Fn x, Fn y) -> aux x.arg y.arg && aux x.ret y.ret
      | (Sum x, Sum y) -> aux x.left y.left && aux x.right y.right
      | (Product x, Product y) -> aux x.left y.left && aux x.right y.right
      | (Rec x, Rec y) -> aux x.tau y.tau
      | (Forall x, Forall y) -> aux x.tau y.tau
      | (Exists x, Exists y) -> aux x.tau y.tau
      | _ -> false
    in
    aux (to_debruijn tau1) (to_debruijn tau2)

  let inline_tests () =
    let p = Parser.parse_type_exn in

    assert (
      aequiv
        (substitute "a" (p "num") (p "forall b . a"))
        (p "forall a . num"));
    assert (
      aequiv
        (substitute "a" (p "b") (p "forall b . a"))
        (p "forall c . b"));
    assert (
      not (aequiv
        (substitute "a" (p "b") (p "forall b . a"))
        (p "forall b . b")));
    assert (
      aequiv
        (substitute "a" (p "b") (p "forall b . forall b . a"))
        (p "forall q . forall c . b"));
    assert (
      not (aequiv
        (substitute "a" (p "b") (p "forall b . forall b . a"))
        (p "forall a . forall b . a")));

    assert (aequiv (p "forall a . a") (p "forall b . b"));
    assert (not (aequiv (p "forall a . a") (p "forall b . num")));
    assert (aequiv
              (p "forall a . forall b . a -> b")
              (p "forall x . forall y . x -> y"))

  (* Uncomment the line below when you want to run the inline tests. *)
  (* let () = inline_tests () *)
end

module Expr = struct
  open Ast.Expr

  (* Term variables only: type annotations do not affect runtime substitution. *)
  let rec free_vars (e : t) : String.Set.t =
    match e with
    | Num _ | True | False | Unit -> String.Set.empty
    | Var x -> String.Set.singleton x
    | Binop {left; right; _} | Relop {left; right; _}
    | And {left; right} | Or {left; right} | Pair {left; right} ->
      Set.union (free_vars left) (free_vars right)
    | If {cond; then_; else_} ->
      Set.union (free_vars cond) (Set.union (free_vars then_) (free_vars else_))
    | Lam {x; e; _} | Fix {x; e; _} -> Set.remove (free_vars e) x
    | App {lam; arg} -> Set.union (free_vars lam) (free_vars arg)
    | Project {e; _} | Inject {e; _} | TyLam {e; _} | TyApp {e; _}
    | Fold_ {e; _} | Unfold e | Export {e; _} -> free_vars e
    | Case {e; xleft; eleft; xright; eright} ->
      Set.union (free_vars e)
        (Set.union (Set.remove (free_vars eleft) xleft)
           (Set.remove (free_vars eright) xright))
    | Import {x; e_mod; e_body; _} ->
      Set.union (free_vars e_mod) (Set.remove (free_vars e_body) x)

  let rename_binder (rename : t String.Map.t) (x : string) (body : t)
    : string * t String.Map.t =
    let used = List.fold (Map.data rename)
      ~init:(Set.union (String.Set.of_list (Map.keys rename)) (free_vars body))
      ~f:(fun used e -> Set.union used (free_vars e)) in
    let rec fresh_name x =
      if Set.mem used x then fresh_name (fresh x) else x
    in
    let x' = fresh_name x in
    (* A new binding shadows any substitution for its old name. *)
    let rename' =
      Map.set (Map.set rename ~key:x ~data:(Var x')) ~key:x' ~data:(Var x') in
    (x', rename')

  let rec substitute_map (rename : t String.Map.t) (e : t) : t =
    let sub = substitute_map rename in
    match e with
    | Num _ | True | False | Unit -> e
    | Var x ->
      (match Map.find rename x with Some replacement -> replacement | None -> e)
    | Binop {binop; left; right} -> Binop {binop; left = sub left; right = sub right}
    | Relop {relop; left; right} -> Relop {relop; left = sub left; right = sub right}
    | And {left; right} -> And {left = sub left; right = sub right}
    | Or {left; right} -> Or {left = sub left; right = sub right}
    | If {cond; then_; else_} -> If {cond = sub cond; then_ = sub then_; else_ = sub else_}
    | Lam {x; tau; e} ->
      let (x', rename') = rename_binder rename x e in
      Lam {x = x'; tau; e = substitute_map rename' e}
    | App {lam; arg} -> App {lam = sub lam; arg = sub arg}
    | Pair {left; right} -> Pair {left = sub left; right = sub right}
    | Project {e; d} -> Project {e = sub e; d}
    | Inject {e; d; tau} -> Inject {e = sub e; d; tau}
    | Case {e; xleft; eleft; xright; eright} ->
      let (xleft', left_rename) = rename_binder rename xleft eleft in
      let (xright', right_rename) = rename_binder rename xright eright in
      Case {e = sub e; xleft = xleft'; eleft = substitute_map left_rename eleft;
        xright = xright'; eright = substitute_map right_rename eright}
    | Fix {x; tau; e} ->
      let (x', rename') = rename_binder rename x e in
      Fix {x = x'; tau; e = substitute_map rename' e}
    | TyLam {a; e} -> TyLam {a; e = sub e}
    | TyApp {e; tau} -> TyApp {e = sub e; tau}
    | Fold_ {e; tau} -> Fold_ {e = sub e; tau}
    | Unfold e -> Unfold (sub e)
    | Export {e; tau_adt; tau_mod} -> Export {e = sub e; tau_adt; tau_mod}
    | Import {x; a; e_mod; e_body} ->
      let (x', rename') = rename_binder rename x e_body in
      Import {x = x'; a; e_mod = sub e_mod; e_body = substitute_map rename' e_body}

  let substitute (x : string) (e' : t) (e : t) : t =
    substitute_map (String.Map.singleton x e') e

  let to_debruijn (e : t) : t =
    let bind depth x = Map.set (Map.map depth ~f:(fun i -> i + 1)) ~key:x ~data:0 in
    (* Runtime comparison ignores every type annotation and type binder name. *)
    let erased = Ast.Type.Var "_" in
    let rec aux (depth : int String.Map.t) (e : t) : t =
      let conv = aux depth in
      match e with
      | Num _ | True | False | Unit -> e
      | Var x ->
        (match Map.find depth x with Some i -> Var (Int.to_string i) | None -> e)
      | Binop {binop; left; right} -> Binop {binop; left = conv left; right = conv right}
      | Relop {relop; left; right} -> Relop {relop; left = conv left; right = conv right}
      | And {left; right} -> And {left = conv left; right = conv right}
      | Or {left; right} -> Or {left = conv left; right = conv right}
      | If {cond; then_; else_} ->
        If {cond = conv cond; then_ = conv then_; else_ = conv else_}
      | Lam {x; e; _} -> Lam {x = "_"; tau = erased; e = aux (bind depth x) e}
      | App {lam; arg} -> App {lam = conv lam; arg = conv arg}
      | Pair {left; right} -> Pair {left = conv left; right = conv right}
      | Project {e; d} -> Project {e = conv e; d}
      | Inject {e; d; _} -> Inject {e = conv e; d; tau = erased}
      | Case {e; xleft; eleft; xright; eright} ->
        Case {e = conv e; xleft = "_"; eleft = aux (bind depth xleft) eleft;
          xright = "_"; eright = aux (bind depth xright) eright}
      | Fix {x; e; _} -> Fix {x = "_"; tau = erased; e = aux (bind depth x) e}
      | TyLam {e; _} -> TyLam {a = "_"; e = conv e}
      | TyApp {e; _} -> TyApp {e = conv e; tau = erased}
      | Fold_ {e; _} -> Fold_ {e = conv e; tau = erased}
      | Unfold e -> Unfold (conv e)
      | Export {e; _} -> Export {e = conv e; tau_adt = erased; tau_mod = erased}
      | Import {x; e_mod; e_body; _} ->
        Import {x = "_"; a = "_"; e_mod = conv e_mod; e_body = aux (bind depth x) e_body}
    in
    aux String.Map.empty e

  let aequiv (e1 : t) (e2 : t) : bool =
    let rec aux (e1 : t) (e2 : t) : bool =
      match (e1, e2) with
      | (Num n1, Num n2) -> n1 = n2
      | (Var x, Var y) -> x = y
      | (Binop l, Binop r) ->
        l.binop = r.binop && aux l.left r.left && aux l.right r.right
      | (True, True) | (False, False) -> true
      | (If l, If r) ->
        aux l.cond r.cond && aux l.then_ r.then_ && aux l.else_ r.else_
      | (Relop l, Relop r) ->
        l.relop = r.relop && aux l.left r.left && aux l.right r.right
      | (And l, And r) ->
        aux l.left r.left && aux l.right r.right
      | (Or l, Or r) ->
        aux l.left r.left && aux l.right r.right
      | (Lam l, Lam r) ->
        aux l.e r.e
      | (App l, App r) ->
        aux l.lam r.lam && aux l.arg r.arg
      | (Unit, Unit) -> true
      | (Pair l, Pair r) ->
        aux l.left r.left && aux l.right r.right
      | (Project l, Project r) ->
        aux l.e r.e && l.d = r.d
      | (Inject l, Inject r) ->
        aux l.e r.e && l.d = r.d
      | (Case l, Case r) ->
        aux l.e r.e && aux l.eleft r.eleft && aux l.eright r.eright
      | (Fix l, Fix r) -> aux l.e r.e
      | (TyLam l, TyLam r) ->
        aux l.e r.e
      | (TyApp l, TyApp r) -> aux l.e r.e
      | (Fold_ l, Fold_ r) -> aux l.e r.e
      | (Unfold l, Unfold r) -> aux l r
      | (Export l, Export r) -> aux l.e r.e
      | (Import l, Import r) -> aux l.e_mod r.e_mod && aux l.e_body r.e_body
      | _ -> false
    in
    aux (to_debruijn e1) (to_debruijn e2)

  let inline_tests () =
    let p = Parser.parse_expr_exn in
    let t1 = p "(fun (x : num) -> x) y" in
    assert (aequiv (substitute "x" (Num 0) t1) t1);
    assert (aequiv (substitute "y" (Num 0) t1)
              (p "(fun (x : num) -> x) 0"));

    let t2 = p "x + (fun (x : num) -> y)" in
    assert (aequiv
              (substitute "x" (Num 0) t2)
              (p "0 + (fun (x : num) -> y)"));
    assert (aequiv (substitute "y" (Num 0) t2)
              (p "x + (fun (x : num) -> 0)"));

    assert (aequiv (p "fun (x : num) -> x") (p "fun (y : num) -> y"));

    assert (not (aequiv (p "fun (x : num) -> fun (x : num) -> x + x")
                   (p "fun (x : num) -> fun (y : num) -> y + x")));

    assert (
      aequiv
        (p "tyfun a -> fun (x : a) -> x")
        (p "tyfun b -> fun (x : b) -> x"));

    ()

  (* Uncomment the line below when you want to run the inline tests. *)
  (* let () = inline_tests () *)
end

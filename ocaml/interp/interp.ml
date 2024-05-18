open Luaparser.Ast

type value = Value.t
type env = Value.env

(* Fonction auxiliaire pour créer une table d'environnement à partir de noms et
   valeurs associées. *)
let create_scope (names : string list) (values : value list) :
    (name, value) Hashtbl.t =
  let hash = Hashtbl.create (List.length names) in
  let rec aux = function
    | [], [] -> ()
    | [], _ -> ()
    | k :: ks, [] ->
        Hashtbl.add hash k Value.Nil;
        aux (ks, [])
    | k :: ks, v :: vs ->
        Hashtbl.add hash k v;
        aux (ks, vs)
  in
  aux (names, values);
  hash

(* Fonctions de l'interprète, mutuellement récursives. Une fonction par
   catégorie syntaxique de l'AST. *)

(* Interprète un bloc de code *)
let rec interp_block (env : env) (blk : block) : value =
  let new_env =
    Value.
      {
        globals = env.globals;
        locals =
          create_scope blk.locals (List.map (fun _ -> Value.Nil) blk.locals)
          :: env.locals;
      }
  in
  interp_stat new_env blk.body;
  interp_exp new_env blk.ret

(* Interprète une liste de statements *)

(* Interprète un statement *)
and interp_stat (env : env) (stat : stat) : unit =
  match stat with
  | Nop -> ()
  | Seq (s1, s2) ->
      interp_stat env s1;
      interp_stat env s2
  | Assign (Name name, exp) ->
      let value = interp_exp env exp in
      Value.set_ident env name value
  | Assign (IndexTable (table, index), exp) ->
      let t = Value.as_table (interp_exp env table) in
      let key = Value.as_table_key (interp_exp env index) in
      let value = interp_exp env exp in
      Hashtbl.add t key value
  | FunctionCall fc -> ignore (interp_funcall env fc)
  | If (cond, then_, else_) ->
      if Value.as_bool (interp_exp env cond) then interp_stat env then_
      else interp_stat env else_
  | WhileDoEnd (cond, body) ->
      while Value.as_bool (interp_exp env cond) do
        interp_stat env body
      done

(* Interprète un appel de fonction *)
and interp_funcall (env : env) ((exp, args) : functioncall) : value =
  match Value.as_function (interp_exp env exp) with
  | Closure (names, closure, block) ->
      let values = List.map (fun arg -> interp_exp env arg) args in
      let new_env =
        Value.
          {
            globals = env.globals;
            locals = create_scope names values :: closure.locals;
          }
      in
      interp_block new_env block
  | Print ->
      (match args with
      | [] -> Printf.printf "\n"
      | arg :: agrs ->
          Printf.printf "%s" (Value.to_string (interp_exp env arg));
          List.iter
            (fun arg ->
              Printf.printf "\t%s" (Value.to_string (interp_exp env arg)))
            agrs;
          Printf.printf "\n");
      Value.Nil

(* Interprète une expression *)
and interp_exp (env : env) (e : exp) : value =
  match e with
  | Nil -> Value.Nil
  | False -> Value.Bool false
  | True -> Value.Bool true
  | Integer n -> Value.Int n
  | Float f -> Value.Float f
  | LiteralString s -> Value.String s
  | Var (Name name) -> Value.lookup_ident env name
  | Var (IndexTable (table, index)) -> (
      let t = Value.as_table (interp_exp env table) in
      let key = Value.as_table_key (interp_exp env index) in
      try Hashtbl.find t key with Not_found -> Value.Nil)
  | FunctionCallE fc -> interp_funcall env fc
  | FunctionDef (names, block) ->
      Value.Function (Value.Closure (names, env, block))
  | BinOp (bop, e1, e2) -> (
      let v1 = interp_exp env e1 in
      match bop with
      | LogicalAnd -> if Value.as_bool v1 then interp_exp env e2 else v1
      | LogicalOr -> if Value.as_bool v1 then v1 else interp_exp env e2
      | _other_bop -> (
          let v2 = interp_exp env e2 in
          match bop with
          | Addition -> Value.add v1 v2
          | Subtraction -> Value.sub v1 v2
          | Multiplication -> Value.mul v1 v2
          | Equality -> Value.Bool (Value.equal v1 v2)
          | Inequality -> Value.Bool (not (Value.equal v1 v2))
          | Less -> Value.Bool (Value.lt v1 v2)
          | LessEq -> Value.Bool (Value.le v1 v2)
          | Greater -> Value.Bool (Value.lt v2 v1)
          | GreaterEq -> Value.Bool (Value.le v2 v1)
          | _ -> assert false))
  | UnOp (uop, e) -> (
      let v = interp_exp env e in
      match uop with
      | UnaryMinus -> Value.neg v
      | Not -> Value.Bool (not (Value.as_bool v)))
  | Table l ->
      let table = Hashtbl.create (List.length l) in
      List.iter
        (fun (k, v) ->
          Hashtbl.add table
            (Value.as_table_key (interp_exp env k))
            (interp_exp env v))
        l;
      Value.Table table

let run ast =
  let globals = Hashtbl.create 47 in
  Hashtbl.add globals "print" (Value.Function Print);
  let env = Value.{ globals; locals = [] } in
  ignore (interp_block env ast)

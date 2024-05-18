open Luaparser.Ast

type value = Value.t
type coroutine = Value.coroutine
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

let convert_key_to_exp = function
  | Value.KInt n -> Integer n
  | Value.KString n -> LiteralString n

let rec convert_val_to_exp = function
  | Value.Nil -> Nil
  | Value.Bool b -> if b then True else False
  | Value.Int n -> Integer n
  | Value.Float f -> Float f
  | Value.String s -> LiteralString s
  | Value.Table h ->
      Table
        (Hashtbl.fold
           (fun k v l -> (convert_key_to_exp k, convert_val_to_exp v) :: l)
           h [])
  | Value.Function f -> (
      match f with
      | Print -> Var (Name "print")
      | Closure (name, _, block) -> FunctionDef (name, block)
      | _ -> assert false)
  | Value.Coroutine _ -> assert false

let rec interp_block (env : env) (blk : block) (co : coroutine)
    (k : value -> unit) : unit =
  let new_env =
    Value.
      {
        globals = env.globals;
        locals =
          create_scope blk.locals (List.map (fun _ -> Value.Nil) blk.locals)
          :: env.locals;
      }
  in
  interp_stat new_env blk.body co (fun _ ->
      interp_exp new_env blk.ret co (fun v -> k v))

and interp_stat (env : env) (stat : stat) (co : coroutine) (k : unit -> unit) :
    unit =
  match stat with
  | Nop -> k ()
  | Seq (s1, s2) -> interp_stat env s1 co (fun _ -> interp_stat env s2 co k)
  | Assign (Name name, exp) ->
      interp_exp env exp co (fun v ->
          Value.set_ident env name v;
          k ())
  | Assign (IndexTable (table, index), exp) ->
      interp_exp env table co (fun v1 ->
          let table = Value.as_table v1 in
          interp_exp env index co (fun v2 ->
              let key = Value.as_table_key v2 in
              interp_exp env exp co (fun v3 ->
                  Hashtbl.add table key v3;
                  k ())))
  | FunctionCall fc -> interp_funcall env fc co (fun _ -> k ())
  | If (cond, then_, else_) ->
      interp_exp env cond co (fun v ->
          if Value.as_bool v then interp_stat env then_ co k
          else interp_stat env else_ co k)
  | WhileDoEnd (cond, body) ->
      interp_exp env cond co (fun v ->
          if Value.as_bool v then
            interp_stat env body co (fun _ -> interp_stat env stat co k)
          else k ())

and interp_funcall (env : env) ((exp, args) : functioncall) (co : coroutine)
    (k : value -> unit) : unit =
  let arg_list = args in
  interp_exp env exp co (fun f ->
      let args = ref args in
      let pop l =
        match !l with
        | e :: l' ->
            l := l';
            Some e
        | [] -> None
      in
      let arg_f ?(g : unit -> unit = fun _ -> ()) f =
        match pop args with Some arg -> interp_exp env arg co f | None -> g ()
      in
      match Value.as_function f with
      | Closure (names, closure, block) -> (
          let new_env =
            Value.
              {
                globals = env.globals;
                locals =
                  create_scope names (List.map (fun _ -> Value.Nil) names)
                  :: closure.locals;
              }
          in
          let names = ref names in
          let g () =
            List.iter
              (fun name -> Value.set_ident new_env name Value.Nil)
              !names;
            interp_block new_env block co (fun v -> k v)
          in
          let rec f v =
            (match pop names with
            | Some name -> Value.set_ident new_env name v
            | None -> ());
            arg_f ~g f
          in
          match pop args with
          | Some arg -> interp_exp env arg co f
          | None -> g ())
      | Print -> (
          let s = ref "" in
          let g () =
            Printf.printf "%s\n" (String.sub !s 1 (String.length !s - 1));
            k Value.Nil
          in
          let rec f v =
            s := !s ^ Printf.sprintf "\t%s" (Value.to_string v);
            arg_f ~g f
          in
          match pop args with
          | Some arg -> interp_exp env arg co f
          | None -> g ())
      | CoroutCreate ->
          let arg = List.hd arg_list in
          interp_exp env arg co (fun v ->
              match v with
              | Value.Function (Closure (params, lenv, blk)) ->
                  let locals = create_scope params [] in
                  let new_env =
                    Value.
                      { globals = lenv.globals; locals = locals :: lenv.locals }
                  in
                  let new_co = Value.{ stat = Value.Suspended (fun _ -> ()) } in
                  let rec continuation value =
                    if List.length params = 1 then
                      Value.set_ident new_env (List.hd params) value;
                    interp_block new_env blk
                      (Value.as_coroutine (Value.Coroutine new_co)) (fun ret ->
                        match new_co with
                        | { stat = Value.Running continuation } ->
                            (Value.as_coroutine (Value.Coroutine new_co)).stat <-
                              Value.Dead;
                            continuation ret
                        | { stat = Value.Suspended continuation } ->
                            (Value.as_coroutine (Value.Coroutine new_co)).stat <-
                              Value.Dead;
                            continuation ret
                        | _ -> failwith "Not implemented in coroutine create")
                  in
                  new_co.stat <- Value.Suspended continuation;
                  k (Value.Coroutine new_co)
              | _ -> failwith "Not implemented in coroutine create")
      | CoroutYield -> (
          match co with
          | { stat = Value.Running continuation } ->
              co.stat <- Value.Suspended k;
              if List.length arg_list = 1 then
                interp_exp env (List.nth arg_list 0) co (fun v ->
                    continuation v)
              else continuation Value.Nil
          | { stat = Suspended _ } -> ()
          | _ -> ())
      | CoroutResume ->
          interp_exp env (List.nth arg_list 0) co (fun v ->
              match Value.as_coroutine v with
              | { stat = Value.Suspended continuation } ->
                  let co = Value.as_coroutine v in
                  co.stat <- Value.Running k;
                  if List.length arg_list > 1 then
                    let arg = List.nth arg_list 1 in
                    interp_exp env arg co (fun v -> continuation v)
                  else continuation Value.Nil
              | { stat = Value.Dead } ->
                  failwith "Cannot resume a dead coroutine\n"
              | { stat = Value.Running _ } -> ()
              | _ -> failwith "Not implemented in coroutine resume")
      | CoroutStatus ->
          interp_exp env (List.hd arg_list) co (fun v ->
              match Value.as_coroutine v with
              | { stat = Value.Suspended _ } -> k (Value.String "suspended")
              | { stat = Value.Running _ } -> k (Value.String "running")
              | { stat = Value.Dead } -> k (Value.String "dead"))
      | _ -> failwith "Not implemented in function call")

and interp_exp (env : env) (e : exp) (co : coroutine) (k : value -> unit) : unit
    =
  match e with
  | Nil -> k Value.Nil
  | True -> k (Value.Bool true)
  | False -> k (Value.Bool false)
  | Integer n -> k (Value.Int n)
  | Float f -> k (Value.Float f)
  | LiteralString s -> k (Value.String s)
  | Var (Name name) -> k (Value.lookup_ident env name)
  | Var (IndexTable (table, index)) ->
      interp_exp env table co (fun v1 ->
          let table = Value.as_table v1 in
          interp_exp env index co (fun v2 ->
              let key = Value.as_table_key v2 in
              k (try Hashtbl.find table key with Not_found -> Value.Nil)))
  | FunctionCallE fc -> interp_funcall env fc co k
  | FunctionDef (names, block) ->
      k (Value.Function (Value.Closure (names, env, block)))
  | BinOp (op, e1, e2) ->
      interp_exp env e1 co (fun v1 ->
          let _other_bop bop = interp_exp env e2 co (fun v2 -> k (bop v1 v2)) in
          match op with
          | LogicalAnd ->
              if Value.as_bool v1 then interp_exp env e2 co k else k v1
          | LogicalOr ->
              if Value.as_bool v1 then k v1 else interp_exp env e2 co k
          | Addition -> _other_bop Value.add
          | Subtraction -> _other_bop Value.sub
          | Multiplication -> _other_bop Value.mul
          | Equality -> _other_bop (fun v1 v2 -> Value.Bool (Value.equal v1 v2))
          | Inequality ->
              _other_bop (fun v1 v2 -> Value.Bool (not (Value.equal v1 v2)))
          | Less -> _other_bop (fun v1 v2 -> Value.Bool (Value.lt v1 v2))
          | LessEq -> _other_bop (fun v1 v2 -> Value.Bool (Value.le v1 v2))
          | Greater -> _other_bop (fun v1 v2 -> Value.Bool (Value.lt v2 v1))
          | GreaterEq -> _other_bop (fun v1 v2 -> Value.Bool (Value.le v2 v1)))
  | UnOp (op, e) ->
      interp_exp env e co (fun v ->
          k
            (match op with
            | UnaryMinus -> Value.neg v
            | Not -> Value.Bool (not (Value.as_bool v))))
  | Table fields ->
      let table = Hashtbl.create (List.length fields) in
      let rec aux = function
        | [] -> k (Value.Table table)
        | (exp1, exp2) :: fields ->
            interp_exp env exp1 co (fun k ->
                interp_exp env exp2 co (fun v ->
                    Hashtbl.add table (Value.as_table_key k) v;
                    aux fields))
      in
      aux fields

let run ast =
  let coroutine : (Value.tkey, value) Hashtbl.t = Hashtbl.create 4 in
  Hashtbl.add coroutine (KString "create") (Value.Function CoroutCreate);
  Hashtbl.add coroutine (KString "yield") (Value.Function CoroutYield);
  Hashtbl.add coroutine (KString "mini_resume") (Value.Function CoroutResume);
  Hashtbl.add coroutine (KString "status") (Value.Function CoroutStatus);
  let globals : (string, value) Hashtbl.t = Hashtbl.create 47 in
  Hashtbl.add globals "print" (Function Print);
  Hashtbl.add globals "coroutine" (Table coroutine);
  let env = Value.{ globals; locals = [] } in
  let co = Value.{ stat = Value.Running (fun _ -> ()) } in
  ignore (interp_block env ast co (fun _ -> ()))

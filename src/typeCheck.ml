(*
 * Example compiler
 * Copyright (C) 2015-2016 Scott Owens
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

(* The type checker *)

open Util
open SourceAst
module T = Tokens

(* Types *)
type t =
  | Tint
  | Tfloat
  | Tbool
  | Tfunction of ((id*t) list) * t
  | Tunknown
  | Tarray of int (* The number of dimensions that the array has *)

let rec show_t t =
  let rec show_param_ts (params:(id*t) list) (show_string:string) =
    match params with
    | [] -> show_string
    | (param_id, param_t)::params ->
        let show_string = show_string ^ "(" ^ (show_id param_id) ^ ":" ^ (show_t param_t) ^ ") -> " in
        show_param_ts params show_string
  in
  match t with
  | Tint -> "int"
  | Tfloat -> "float"
  | Tbool -> "bool"
  | Tfunction (params, t) -> "function of type " ^ (show_param_ts (List.rev params) "") ^ (show_t t)
  | Tunknown -> "unknown"
  | Tarray n -> "array " ^ string_of_int n
      

(* Map identifiers to their types *)
type env_t = t Idmap.t

(* Raise a type error *)
let type_error (ln : int option) (msg : string) : 'a =
  match ln with
  Some ln ->
    raise (BadInput ("Type error on line " ^ string_of_int ln ^ ": " ^ msg))
  | None ->
    raise (BadInput ("Type error at unknown location: " ^ msg))

let op_argument_type op : t =
  match op with
  | (T.Plus | T.Minus | T.Times | T.Div | T.Lt | T.Gt | T.Eq | T.Lshift | T.BitOr | T.BitAnd) -> Tint
  | (T.Fplus | T.Fminus | T.Ftimes | T.Fdiv) -> Tfloat
  | (T.And | T.Or) -> Tbool

let op_result_type op : t =
  match op with
  | (T.Plus | T.Minus | T.Times | T.Div | T.Lshift | T.BitOr | T.BitAnd) -> Tint
  | (T.Fplus | T.Fminus | T.Ftimes | T.Fdiv) -> Tfloat
  | (T.And | T.Or | T.Lt | T.Gt | T.Eq) -> Tbool

let pp_env env =
  let print_key k v = 
    Printf.printf "key: %s, value %s\n" (show_id k) (show_t v);
    ()
  in
  Idmap.iter print_key env;
  Printf.printf "\n"
  
(* Compute the type of an expression, or raise BadInput if there is a type
   error *)
let rec type_exp (ln : int option) (env : env_t) (e : exp) : t*env_t =
  let infer_ident_type ln exp op env : t*env_t =
    let (exp_t, env) = type_exp ln env exp in
    let op_arg_t = op_argument_type op in
    let op_res_t = op_result_type op in
    match exp with
    | Ident (id, _) ->
	(try 
          (match Idmap.find id env with 
	  | Tunknown -> (op_res_t, (Idmap.add id op_arg_t env))
          | id_t when id_t <> op_arg_t -> type_error ln ("Op " ^ (T.show_op op) ^ " applied to " ^ (show_t id_t) ) 
          | _ -> (op_res_t, env))   
        with
	  Not_found -> (op_res_t, (Idmap.add id op_arg_t env))) 
    | _ when op_arg_t = exp_t -> (op_res_t, env)
    | _ -> type_error ln ("Op " ^ (T.show_op op) ^ " applied to " ^ (show_t exp_t) )
  in
  match e with
  | Ident (i, es) ->
    let t =
      try Idmap.find i env
      with Not_found ->
        type_error ln ("Uninitialised variable " ^ show_id i)
    in
    let ts = List.map (type_exp ln env) es in
    let l = List.length ts in
    (match t with
     | Tarray num_dims ->
       if num_dims = l && List.for_all (fun (x, _) -> x = Tint) ts then
         (Tint, env)
       else if num_dims = l then
         type_error ln "Array index with non-integer type"
       else
         type_error ln ("Array reference with " ^ string_of_int l ^
                        " indices, expected " ^ string_of_int num_dims)
     | t ->
       if l = 0 then
         (t, env)
       else
         type_error ln ("Attempt to index non-array variable " ^ show_id i))
  | Num n -> (Tint, env)
  | Float n ->(Tfloat, env)
  | Bool b -> (Tbool, env)
  | FunctionCall (id, call_params) ->
    let rec type_check_call_params call_params fun_params =
      match (call_params, fun_params) with
      | ([], _::_) | (_::_, []) -> type_error ln "Function parameter count doesn't match function call"
      | (call_param::call_params, (fun_param_id, fun_param_t)::fun_params) ->
        let (call_param_t, _) = type_exp ln env call_param in
        if call_param_t = fun_param_t then
          type_check_call_params call_params fun_params
        else
          type_error ln ("Error in call to function " ^ (show_id id) 
            ^ " parameter " ^ (show_id fun_param_id) 
            ^ " is of type " ^ (show_t fun_param_t) 
            ^ " but expression is of type " ^ (show_t call_param_t))
      | ([], []) -> ()
    in
    (try 
      (match Idmap.find id env with
        Tfunction (fun_param_list, return_type) -> 
          type_check_call_params call_params fun_param_list;
          (return_type, env))
    with
    | _ -> type_error ln ("Function " ^ (show_id id) ^ " not defined. No reccursion allowed"))
    
    
  | Op (e1, op, e2) ->
    let (exp_t, env) = infer_ident_type ln e1 op env in
    infer_ident_type ln e2 op env
  | Uop (uop, e) ->
    let (e_t, env) = type_exp ln env e in
    (match (uop, e_t) with
     | (T.Not, Tbool) -> (Tbool, env)
     | (_, t) ->
       type_error ln ("Operator " ^ T.show_uop uop ^ " applied to " ^ show_t t))
  | Array es ->
    let ts = List.map (type_exp ln env) es in
    let l = List.length ts in
    if l = 0 then
      type_error ln "Array must have at least 1 dimension"
    else if List.for_all (fun (x, _) -> x = Tint) ts then
      ((Tarray l), env)
    else
      type_error ln "Array dimension with non-integer type";;

(* Type check an identifier being assigned to.
   If it is already assigned, check its type. If it has not been assigned,
   extend the type environment *)
let type_lhs_ident (env :env_t) (x : id) (t : t) (ln : int option) : env_t =
  try
    let t_found = Idmap.find x env in
    match t_found with
    | Tunknown -> 
       let new_env = Idmap.add x t env in
       new_env
    | _ when t_found = t -> env
    | _ -> type_error ln ("Bad type for " ^ show_id x)
  with Not_found ->
    let new_env = Idmap.add x t env in
    new_env

let join_environments ln outer_env inner_env : env_t =
  let contains k a b = 
    match (a, b) with
    | (Some Tunknown, Some inner) -> Some inner
    | (None, Some _) -> None
    | (Some outer, Some inner) when inner = outer ->
       Some outer
    | (Some outer, Some inner) ->
       type_error ln ("Found type " ^ (show_t inner) ^ " when expecting type: " ^ (show_t outer))
    | _ -> type_error ln "Compiler error: idents missing in inner enironment that are in outer environment\n"
  in
  Idmap.merge contains outer_env inner_env

(* Type check a list of statements. Raise BadInput if there is an error.  Check
   a list so that earlier assignment statements can extend the environment for
   later statements *)
let rec type_stmts (ln : int option) (env :env_t) (stmts : stmt list) (fun_id : id option): env_t =
  match stmts with
  | [] -> env
  | In x :: stmts' ->
    let env' = type_lhs_ident env x Tint ln in
    type_stmts ln env' stmts' fun_id
  | Out x :: stmts' ->
    if Idmap.find x env = Tint then
      type_stmts ln env stmts' fun_id
    else
      type_error ln "Output with non-integer type"
  | Assign (x, [], e) :: stmts' ->
    let (t, env) = type_exp ln env e in
    let env = type_lhs_ident env x t ln in
    type_stmts ln env stmts' fun_id
  | Assign (x, es, e) :: stmts' ->
    (* Assignments to arrays require the lhs to be checkable as an expression.
       In particular, the identifier must already be bound to an array type of
       the correct dimension. *)
    let (t1, env) = type_exp ln env (Ident (x, es)) in
    let (t2, env) = type_exp ln env e in
    if t1 = t2 then
      type_stmts ln env stmts' fun_id
    else
      type_error ln "Array assignment type mismatch"
  | Function (id, parameters, statements) :: stmts' ->
     let env = type_lhs_ident env id Tunknown ln in
     let rec add_params params env = 
       match params with
       | [] -> env
       | param::params -> 
         let env = Idmap.add param Tunknown env in
	       add_params params env
     in
     let rec get_param_types (param_ids:id list) (type_list:(id*t) list) (env: env_t): (id*t) list =
       match param_ids with
       | [] -> type_list
       | param_id::param_ids -> 
         let param_type:t = Idmap.find param_id env in
         let id_type:id*t = (param_id, param_type) in
         get_param_types param_ids (type_list@[id_type]) env
     in  
     let env' = add_params parameters env in
     let env' = type_stmts ln env' [statements] (Some id) in
     let env = join_environments ln env env' in
     let Tfunction (_, fun_ret_type) = Idmap.find id env' in
     let param_types = get_param_types parameters [] env' in
     let env = Idmap.add id (Tfunction (param_types, fun_ret_type)) env in
     type_stmts ln env stmts' fun_id
  | FunctionReturn exp :: stmts' ->
     (match fun_id with
      | Some fun_id -> 
	      let (exp_type, env) = type_exp ln env exp in
        pp_env env;
	      let env = type_lhs_ident env fun_id (Tfunction ([], exp_type)) ln in
	      type_stmts ln env stmts' (Some fun_id)
      | None -> type_error ln "return statement not in a function")     
  | DoWhile (s1, e, s2) :: stmts ->
    let env_s1 = type_stmts ln env [s1] fun_id in
    let (e_t, env) = type_exp ln env e in 
    if e_t = Tbool then
      (let env_s2 = type_stmts ln env [s2] fun_id in
       let env = join_environments ln env env_s1 in
       let env = join_environments ln env env_s2 in
       type_stmts ln env stmts fun_id)
    else
      type_error ln "While test of non-bool type"
  | Ite (e, s1, s2) :: stmts ->
    let (e_t, env) = type_exp ln env e in
    if e_t = Tbool then
      (let if_env = type_stmts ln env [s1] fun_id in
       let env = join_environments ln env if_env in
       let else_env = type_stmts ln env [s2] fun_id in
       let env = join_environments ln env else_env in
       type_stmts ln env stmts fun_id)
    else
      type_error ln "If test of non-bool type"
  | Stmts (s_list) :: stmts' ->
    (let env = type_stmts ln env s_list fun_id in
     type_stmts ln env stmts' fun_id)
  | Loc (s, ln') :: stmts' ->
    type_stmts (Some ln') env (s :: stmts') fun_id

let rec remove_loc (stmts : stmt list) : stmt list =
  List.map remove_loc_one stmts

and remove_loc_one s =
  match s with
  | DoWhile (s1, e, s) ->
    DoWhile (remove_loc_one s1, e, remove_loc_one s)
  | Ite (e, s1, s2) ->
    Ite (e, remove_loc_one s1, remove_loc_one s2)
  | Stmts s ->
    Stmts (remove_loc s)
  | Loc (s, _) -> remove_loc_one s
  | s -> s

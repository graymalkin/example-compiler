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

(* A control flow graph representation with basic blocks, and the source AST ->
   CGF algorithm. Also compiles arrays to loads and stores. *)

type var =
  | Vreg of int
  | Stack of int
  | NamedSource of string
  | NamedTmp of string * int
  [@@deriving show]

module Varset : sig
  include Set.S with type elt = var
  val show : t -> string
  val pp : Format.formatter -> t -> unit
end

module Varmap : sig
  include Map.S with type key = var
end

type atomic_exp =
  | Ident of var
  | Num of int64
  | Float of float
  [@@deriving show]

type block_elem =
  | AssignOp of var * atomic_exp * Tokens.op * atomic_exp
  | AssignAtom of var * atomic_exp
  (* Ld (x,y,e) represents x := *(y+e) *)
  | Ld of var * var * atomic_exp
  (* St (x,e1,e2) represents *(x+e1) := e2 *)
  | St of var * atomic_exp * atomic_exp
  (* Call (x, f, aes) represents x := f(aes) *)
  | Call of var option * string * atomic_exp list
  (* BoundCheck (a1, a2) represents assert (a1 >= 0 && a1 < a2) *)
  | BoundCheck of atomic_exp * atomic_exp
  | FunctionStart of string * var list
  | FunctionReturn of atomic_exp

  [@@deriving show]

type basic_block = block_elem list
  [@@deriving show]

type test_op =
  | Lt
  | Gt
  | Eq
  [@@deriving show]

type test = atomic_exp * test_op * atomic_exp
  [@@deriving show]

type next_block =
  | End
  | EndOfFunction
  | Next of int
  (* The first int is the block number if the ident is true, and the second if
   * it is false *)
  | Branch of test * int * int
  [@@deriving show]

type cfg_entry = { bnum : int; elems : block_elem list; next : next_block;
                   mutable started : bool; mutable finished : bool }
  [@@deriving show]

type cfg = cfg_entry list
  [@@deriving show]

val build_cfg : SourceAst.stmt list -> cfg

val cfg_to_graphviz : Format.formatter -> cfg -> unit

val id_to_var : SourceAst.id -> var

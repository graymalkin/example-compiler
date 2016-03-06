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

(* The language's tokens, and a simple lexer *)

type op =
  | Plus
  | Minus
  | Times
  | Div
  | Fplus
  | Fminus
  | Ftimes
  | Fdiv
  | Lt
  | Gt
  | Eq
  | And
  | Or
  | Lshift
  | BitOr
  | BitAnd
  [@@deriving show]

type uop =
  | Not
  [@@deriving show]

val op_to_string : op -> string
val uop_to_string : uop -> string

type token =
  | Num of int64
  | Float of float
  | Ident of string
  | Op of op
  | Uop of uop
  | Lparen
  | Rparen
  | Lcurly
  | Rcurly
  | Lbrac
  | Rbrac
  | While
  | Do
  | If
  | Then
  | Else
  | Assign
  | True
  | False
  | Input
  | Output
  | Array
  | Function
  | Comma
  | Return
  [@@deriving show]

type tok_loc = (token * int)
  [@@deriving show]

val lex : string -> int -> int -> tok_loc list

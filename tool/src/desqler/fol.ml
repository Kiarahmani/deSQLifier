open Typedtree
open Speclang
open Var


(*----------------------------------------------------------------------------------------------------*)
let printf = Printf.printf
let print_txn_name (Speclang.Fun.T app) = print_string app.name.name
let print_ident : Ident.t -> unit = fun ident -> print_string ident.name



module L = 
struct
  type expr = |Cons: int -> expr
							|Var: Var.Variable.t -> expr
							|PLUS: expr * expr -> expr
							|MINUS: expr * expr -> expr
							|MULT: expr * expr -> expr
							|DIV: expr * expr -> expr


	type condition = |Bool: bool -> condition 
									 |GT: expr*expr -> condition



module Record = 
struct
	type t = T of {name: string; vars: L.expr list}
end



type t = T of {cond: L.condition}




open Typedtree
open Speclang
open Var
module V = Var.Variable


(*----------------------------------------------------------------------------------------------------*)
let printf = Printf.printf
let print_txn_name (Speclang.Fun.T app) = print_string app.name.name
let print_ident : Ident.t -> unit = fun ident -> print_string ident.name



module L = 
struct
  type expr = |Cons: int -> expr
              |Str: string -> expr
							|Var: Var.Variable.t -> expr
							|PLUS: expr * expr -> expr
							|MINUS: expr * expr -> expr
							|MULT: expr * expr -> expr
							|DIV: expr * expr -> expr


	type condition = |Bool: bool -> condition 
									 |Gt: expr*expr -> condition
									 |Lt: expr*expr -> condition
                   |Eq:  expr*expr -> condition
end


module Record = 
struct
	type t = T of {name: string; vars: (string*L.expr) list}
end



type t = T of {cond: L.condition}
let make ~cond = T{cond}
let cond (T{cond}) = cond
let my_true = make (L.Bool true)
let my_const = L.Var V.test_field
let my_test_equal = make (L.Eq (my_const,my_const))

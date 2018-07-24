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


	type condition = |Bool: expr-> condition 
									 |Gt: expr*expr -> condition
									 |Lt: expr*expr -> condition
                   |Eq:  expr*expr -> condition
                   |Nq: expr*expr -> condition
                   |AND: condition*condition -> condition
                   |OR: condition*condition -> condition
                   |NOT: condition -> condition
end


module Record = 
struct
	type t = T of {name: string; vars: (string*L.expr) list}
end



type t = L.condition
let my_true = L.Bool (L.Var Var.Variable.test_var)
let my_one = L.Cons 1
let my_two = L.Cons 2
let my_false = L.Gt (my_one,my_two)
let my_const = L.Var V.test_field
let my_test_equal = L.Eq (my_const,my_const)

open Typedtree
open Speclang
open Fol
open Var

(*helping function to determine the case to catch*)
let exp_to_stirng: Typedtree.expression -> unit = 
		fun exp -> let desc = exp.exp_desc in
			match desc with 
                        |Texp_ident (_,_,_) -> printf "Texp_ident"
                        |Texp_constant _ -> printf "Texp_constant"
                        |Texp_let (_,_,_) -> printf "Texp_let"
                        |Texp_function (_,_,_) -> printf "Texp_function"
                        |Texp_apply (_,_) -> printf "Texp_apply"
                        |Texp_match (_,_,_,_) -> printf "Texp_match"
                        |Texp_try (_,_) -> printf "Texp_try"
                        |Texp_tuple _ -> printf "Texp_try"
                        |Texp_construct (_,_,_) -> printf "Texp_try"
                        |Texp_variant (_,_) -> printf "Texp_try"
                        |_ -> printf "ERROR: Print Expression - case not implemented yet"

let printf = Printf.printf
let print_txn_name (Speclang.Fun.T app) = print_string app.name.name
let print_ident : Ident.t -> unit = fun ident -> print_string ident.name




(*----------------------------------------------------------------------------------------------------*)
module Statement =
struct
  type st = |SELECT: Var.Table.col * Var.Variable.t * Fol.t * Fol.t -> st
            |INSERT: Var.Table.t *  Fol.Record.t * Fol.t -> st
            |UPDATE: Var.Table.col * Fol.L.expr * Fol.t  -> st
            |DELETE: Var.Table.t * Fol.t * Fol.t -> st
end


(*----------------------------------------------------------------------------------------------------*)
module Transaction = 
struct
  type t = T of {name: string;
                 params: Var.Variable.t list;
                 stmts: (Statement.st) list}
  let make ~name ~params ~stmts = T {name=name; params=params; stmts=stmts}
  let name (T{name}) = name
  let stmts (T{stmts}) = stmts
end







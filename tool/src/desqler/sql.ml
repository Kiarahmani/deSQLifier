open Typedtree
open Speclang
open Fol
open Var

let printf = Printf.printf
let print_txn_name (Speclang.Fun.T app) = print_string app.name.name
let print_ident : Ident.t -> unit = fun ident -> print_string ident.name




(*----------------------------------------------------------------------------------------------------*)
module Statement =
struct
  type st = |SELECT:       Var.Table.col * Var.Variable.t * Fol.t * Fol.t -> st
            |RANGE_SELECT: Var.Table.col * Var.Variable.t * Fol.t * Fol.t -> st
            |MAX_SELECT:   Var.Table.col * Var.Variable.t * Fol.t * Fol.t -> st
            |MIN_SELECT:   Var.Table.col * Var.Variable.t * Fol.t * Fol.t -> st
            |COUNT_SELECT: Var.Table.col * Var.Variable.t * Fol.t * Fol.t -> st
            |INSERT: Var.Table.t *  Fol.Record.t * Fol.t -> st
            |UPDATE: Var.Table.col * Fol.L.expr * Fol.t * Fol.t -> st
            |DELETE: Var.Table.t * Fol.t * Fol.t -> st
            |CHOOSE: Var.Variable.t * Var.Variable.t * Fol.t * Fol.t -> st
      


end


(*----------------------------------------------------------------------------------------------------*)
module Transaction = 
struct
  type t = T of {name: string;
                 params: Var.Variable.t list;
                 stmts: (Statement.st) list;
                 vars: (string*Var.Variable.t) list }
  let make ~name ~params ~stmts ~vars = T {name=name; params=params; stmts=stmts; vars=vars}
  let name (T{name}) = name
  let stmts (T{stmts}) = stmts
end







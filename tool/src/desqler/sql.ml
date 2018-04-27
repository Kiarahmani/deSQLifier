open Typedtree
open Speclang
open Fol
open Var

(*----------------------------------------------------------------------------------------------------*)
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
                 stmts: (Statement.st) list}
  let make ~name ~stmts = T {name=name; stmts=stmts}
  let name (T{name}) = name
  let stmts (T{stmts}) = stmts
end







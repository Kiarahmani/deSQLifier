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
  type st = |SELECT: Var.Table.col * Var.Variable.t * Fol.t * Fol.t -> st
            |INSERT: Var.Table.t *  Fol.Record.t * Fol.t -> st
            |UPDATE: Var.Table.col * Fol.L.expr * Fol.t  -> st
            |DELETE: Var.Table.t * Fol.t * Fol.t -> st

  let sample_stmt = SELECT (("test_col", Var.Type.Int ,true),Var.Variable.test_var,Fol.my_true,Fol.my_true)
  let sample_stmt2 = DELETE (Var.Table.make "test_table" [("test_col", Var.Type.Int ,true)],Fol.my_true,Fol.my_true)

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







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
            |RANGE_SELECT: Var.Table.col * Var.Variable.t * Fol.t * Fol.t -> st
            |MAX_SELECT: Var.Table.col * Var.Variable.t * Fol.t * Fol.t -> st
            |MIN_SELECT: Var.Table.col * Var.Variable.t * Fol.t * Fol.t -> st
            |COUNT_SELECT: Var.Table.col * Var.Variable.t * Fol.t * Fol.t -> st
            |INSERT: Var.Table.t *  Fol.Record.t * Fol.t -> st
            |UPDATE: Var.Table.col * Fol.L.expr * Fol.t * Fol.t -> st
            |DELETE: Var.Table.t * Fol.t * Fol.t -> st
      

  let sample_stmt = SELECT (Var.my_col,Var.Variable.test_var,Fol.my_true,Fol.my_true)
  let sample_stmt2 = DELETE (Var.Table.make "test_table" [Var.my_col],Fol.my_true,Fol.my_true)
  let sample_stmt3 = INSERT (Var.Table.make "test_table" [Var.my_col],Fol.Record.T{name="test_record"; vars=[]} ,Fol.my_true)

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







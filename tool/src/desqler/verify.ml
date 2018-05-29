open App
open Rules
open EncodeIR
open EncodeZ3
open Speclang
open Sql
open Var
module M = Misc
module L = Sql.Transaction
module V = Var.Variable
module T = Var.Type


(*----------------------------------------------------------------------------------------------------*)
let doIt: (App.t) -> unit = fun a ->
        let _ = printf "=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=\n|" in
        let _ = printf "                 Compilation Phase                   " in 
        let _ = printf "|\n=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=\n" in
        let (tables_IR,txns_IR) = (EncodeIR.extract_program a) in
        Rules.apply;
        EncodeZ3.encode tables_IR txns_IR
                                 


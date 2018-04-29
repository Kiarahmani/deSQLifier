open App
open Sql
open Rules
open EncodeIR
open EncodeZ3
open Speclang
module M = Misc



(*----------------------------------------------------------------------------------------------------*)
let doIt: (App.t) -> unit = fun a ->
        let _ = printf "=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=\n|" in
        let _ = printf "                 Compilation Phase                   " in 
        let _ = printf "|\n=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=\n" in
        let tables_IR = (EncodeIR.extract_program a) in
        printf "\n𝙴𝚗𝚌𝚘𝚍𝚒𝚗𝚐:\n";
        Rules.apply;
        EncodeZ3.encode tables_IR []


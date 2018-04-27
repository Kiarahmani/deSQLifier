open App
open Sql
open Rules
open Speclang
module M = Misc



(*----------------------------------------------------------------------------------------------------*)
let doIt (App.T a) = 
        let _ = printf "=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=\n|" in
        let _ = printf "                 Compilation Phase                   " in 
        let _ = printf "|\n=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=\n" in
        (*let ex_txn_list = List.fold_left (fun l -> fun t -> (List.cons t l)) [] 
            (List.map (fun tx -> EncodeIR.extract_txn tx) a.txns) in *)
        printf "\n𝙴𝚗𝚌𝚘𝚍𝚒𝚗𝚐:\n";
        Rules.apply
(*        EncodeZ3.encode_txns ex_txn_list *)


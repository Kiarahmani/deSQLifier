open App
open Sql
open Speclang
module M = Misc


(*----------------------------------------------------------------------------------------------------*)
module Print = 
struct 
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

end


(*----------------------------------------------------------------------------------------------------*)

module Tables = 
struct
  (*redundant: creates my IR tables from Gowtham's*)
	let convert_type_to_IR :  type a. a Speclang.Type.t -> Var.Type.t  = function
    |Speclang.Type.Int -> Var.Type.Int
    |Speclang.Type.Bool -> Var.Type.Bool
    |Speclang.Type.String -> Var.Type.String


  let convert : App.Tableschema.t -> Var.Table.t =
    fun table -> 
      Var.Table.make  (App.Tableschema.name table)
      (List.map (fun (col_name, SomeType col_type, col_pk) -> (col_name,(convert_type_to_IR  col_type), col_pk)) 
                (App.Tableschema.cols table))

end


module EncodeIR_TXN = 
struct

end
	

(*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)
  

  let extract_program: App.t -> Var.Table.t list =
    fun (App.T {schemas; txns}) -> 
      List.map (fun x -> Tables.convert x) schemas

  
  (*
  let extract_txn:Speclang.Fun.t -> Transaction.t =
		fun app  -> let _ = printf "\n𝙸𝚁 𝙴𝚡𝚝𝚛𝚊𝚌𝚝𝚒𝚘𝚗:\n ";
			  	  				  	print_txn_name app; in
			    		  				let Speclang.Fun.T {name; rec_flag; args_t ; body} = app in
													printf " ---> ✅ \n";
                          Transaction.make (name.name) [](*(Extract.extract_exps body)*) (*TODO*)
*)



open App
open Sql
open Speclang
open Types
open Typedtree
module M = Misc
module L = Sql.Transaction
module V = Var.Variable
module T = Var.Type
module G = Speclang.Fun


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


module Txn = 
struct

let remove_txn_tail s = 
  String.sub s 0 ((String.length s) - 4)


(*
let open Asttypes in
  let rec doIt_core_type_desc (ctyp_desc) : some_type =
    match ctyp_desc with
      | Ttyp_constr (path,longident,_) ->
          begin
          match longident with
          | x ->
          let path_str = Printtyp.string_of_path path in
          let some t = SomeType t in
            begin
              match path_str with
                | "string" -> some @@ Type.String
                | "int" -> some @@ Type.Int
                | "bool" -> some @@ Type.Bool
                | _ -> failwith "doIt_core_type_desc: Unimpl."
              end
          end

      | Ttyp_poly (_,core_t) -> doIt_core_type_desc core_t.ctyp_desc
      | _ -> failwith "doIt_core_type_desc: Unimpl." in


*)


let rec print_helpful : type_desc -> unit =
fun x -> 
match x with
  |  Tvar _ -> print_string "Tvar"
  | Tarrow _ -> print_string "Tarrow"
  | Ttuple _ -> print_string "Ttuple"
  | Tconstr (patht,_,_)  -> begin 
																	match patht with	
																  	|Pident x -> print_string x.name
																	end
  | Tobject _ -> print_string "Tobject"
  | Tfield _ -> print_string "Tfield"
  | Tnil -> print_string "Tnil"
  | Tlink {desc;level;id} -> print_helpful desc
  | Tsubst _ -> print_string "Tsubst"
  | Tvariant _ -> print_string "Tvariant"
  | Tunivar _ -> print_string "Tunivar"
  | Tpoly _ -> print_string "Tpoly"
  | Tpackage _ -> print_string "Tpackage"
	| _ -> print_string "FUUUUUCCKCKCKCCCCK"





let rec convert_types: type_desc -> Var.Type.t =
	fun tp -> let open Asttypes in 
		match tp with
			| Tconstr (patht,_,_) -> begin 
																match patht with
																	|Pident {stamp;name;flags} -> 
																				begin match name with "int" -> T.Int | "string" -> T.String | "bool" -> T.Bool  end
																end
			| Tlink {desc;level;id} -> convert_types desc
			| _ -> failwith "encodeIR: convert_types error"



let convert_param: (Ident.t * type_desc) -> V.t  = 
  fun (id,tp) ->  V.make id.name (convert_types tp) V.PARAM




let convert : G.t -> L.t = 
  fun (G.T {name;rec_flag;args_t;res_t;body}) -> 
    let t_name = remove_txn_tail name.name in
    let t_params = List.map convert_param args_t in
    L.make t_name t_params [] (*TODO not doing anything about the statements*)

end
	

(*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)
let sample_txns = [L.make "deposit" [V.make "amount" T.Int V.PARAM] []; L.make "withdraw" [V.make "accID" T.String V.PARAM; V.make "amount" T.Int V.PARAM] []] 






let extract_program: App.t -> (Var.Table.t list * Sql.Transaction.t list) =
    fun (App.T {schemas; txns}) -> 
      let cv_schemas =  List.map (fun x -> Tables.convert x) schemas in
      let cv_txns = List.map (fun x -> Txn.convert x) txns in 
      (cv_schemas,cv_txns)


































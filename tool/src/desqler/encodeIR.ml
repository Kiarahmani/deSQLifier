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
module S = Sql.Statement


(*----------------------------------------------------------------------------------------------------*)

module Utils = 
struct

  let rec print_helpful_type_desc : type_desc -> unit =
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
    | Tlink {desc;level;id} -> print_helpful_type_desc desc
    | Tsubst _ -> print_string "Tsubst"
    | Tvariant _ -> print_string "Tvariant"
    | Tunivar _ -> print_string "Tunivar"
    | Tpoly _ -> print_string "Tpoly"
    | Tpackage _ -> print_string "Tpackage"
	  | _ -> print_string "@#$%$!!"

let print_helpful_expression_desc : expression_desc -> unit = 
  fun x -> 
  let output = match x with 
    |Texp_ident _ -> "Texp_ident"
    |Texp_constant _ -> "Texp_constant"
    |Texp_let _ -> "Texp_let"
    |Texp_function _ -> "Texp_function"
    |Texp_apply _ -> "Tepx_apply"
    |Texp_match _ -> "Texp_match"
    |Texp_try _ -> "Texp_try"
    |Texp_tuple _ -> "Texp_tuple"
    |Texp_construct _ -> "Texp_construct"
    |Texp_variant _ -> "Texp_variant"
    |Texp_record _ -> "Texp_record"
    |Texp_field _ -> "Texp_field"
    |Texp_setfield _ -> "Texp_setfield"
    |Texp_array _ -> "Texp_array"
    |Texp_ifthenelse _ -> "Texp_ifthenelse"
    |Texp_sequence _ -> "Texp_sequence"
    |_ -> "ERROR: print_helpful_expression_desc not catching the case YET"
  in print_string output


let print_helpful_pattern_desc : pattern_desc -> unit = 
  fun x -> 
  let output = match x with
    |Tpat_any -> "Tpat_any"
    |Tpat_var _ -> "Tpat_var"
    |Tpat_alias _ -> "Tpat_alias"
    |Tpat_constant _ -> "Tpat_constant"
    |Tpat_tuple _ -> "Tpat_tuple"
    |Tpat_construct _ -> "Tpat_construct"
    |Tpat_variant _ -> "Tpat_variant"
    |Tpat_record _ -> "Tpat_record"
    |Tpat_array _ -> "Tpat_array"
    |Tpat_or _ -> "Tpat_or"
    |Tpat_lazy _ -> "Tpat_lazy"
    | _ -> failwith "ERROR: print_helpful_pattern_desc -> unexpected pattern"
  in print_string output



let print_stmt : S.st -> unit = fun st -> 
  let open S in 
  match st with
  |SELECT ((col_name,_,_),_,_,_) -> printf "\n SELECT %s" col_name   
  |INSERT _ -> printf "\n INSERT"   
  |UPDATE _ -> printf "\n UPDATE"   
  |DELETE _ -> printf "\n DELETE"   
  |_ -> failwith "ERROR print_stmt: unexpected sql operation"


let print_stmts_list : S.st list -> unit = fun st_list -> 
  let _ = print_string "\nExtracted TXN:\n#########";
          List.iter print_stmt st_list in
  print_string "\n########\n\n\n"



end


(*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*)

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


let rec convert_types: type_desc -> T.t =
	fun tp -> let open Asttypes in 
		match tp with
			| Tconstr (patht,_,_) -> 
        begin 
					match patht with
					|Pident {stamp;name;flags} -> 
						begin match name with "int" -> T.Int | "string" -> T.String | "bool" -> T.Bool  end
					end
			| Tlink {desc;level;id} -> convert_types desc
			| _ -> failwith "encodeIR: convert_types error"


let convert_param: (Ident.t * type_desc) -> V.t  = 
  fun (id,tp) ->  V.make id.name (convert_types tp) V.PARAM


let rec convert_body_rec: S.st list -> Typedtree.expression -> S.st list = 
fun old_stmts -> fun {exp_desc;exp_loc;exp_extra;exp_type;exp_env;exp_attributes} ->
    match exp_desc with 
    (*select case*)
    |Texp_let (_,[{vb_pat;vb_expr}],body) ->  (*vb_expr contains the left hand side of the let --> its a Tepx_apply which I should create a function to handle*)
      let Tpat_var ({name},_) = vb_pat.pat_desc in 
      let new_stmt = S.SELECT (("test_col", T.Int ,true),(V.make name T.Int V.LOCAL),Fol.my_true,Fol.my_true) in
      convert_body_rec (old_stmts@[new_stmt]) body
    (*final delete/update/insert cases*)
    |Texp_apply (app_exp,_) -> 
      let Texp_ident (app_path,_,_) = app_exp.exp_desc in
      let Path.Pdot (_,op,_) = app_path in 
      let new_stmt = match op with
                      |"insert" -> failwith "ERROR convert_body_rec: insert is not handled yet"
                      |"update" ->  S.UPDATE (Var.my_col,Fol.my_const,Fol.my_true)
                      |"delete" -> failwith "ERROR convert_body_rec :delete is not handled yet!"
                      |_ -> failwith "ERROR convert_body_rec: unexpected SQL operation"
      in old_stmts@[new_stmt]
    (*intermediate del/upt/ins*)
    |Texp_sequence (app_exp1,body_exps) -> 
        (convert_body_rec (convert_body_rec old_stmts app_exp1) app_exp1)
    |_ -> failwith "ERROR convert_body_rec: unexpected case"

(*TODO*)
(*TODO*)



let convert_body_stmts: Typedtree.expression -> S.st list =
  fun body -> let output = convert_body_rec [] body in
  let _ = Utils.print_stmts_list output in 
  output


let convert : G.t -> L.t = 
  fun (G.T {name;rec_flag;args_t;res_t;body}) -> 
    let t_name = remove_txn_tail name.name in
    let t_params = List.map convert_param args_t in
    L.make t_name t_params (convert_body_stmts body) 

end
	

(*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)
let sample_txns = [
L.make "deposit" [V.make "amount" T.Int V.PARAM] []; 
L.make "withdraw" [V.make "accID" T.String V.PARAM; V.make "amount" T.Int V.PARAM] [S.sample_stmt]
] 





let extract_program: App.t -> (Var.Table.t list * L.t list) = 
    fun (App.T {schemas; txns}) -> 
      let cv_schemas =  List.map (fun x -> Tables.convert x) schemas in
      let cv_txns = List.map (fun x -> Txn.convert x) txns in 
      (cv_schemas,cv_txns) 

































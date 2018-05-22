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
module F = Fol

(*----------------------------------------------------------------------------------------------------*)

module Utils = 
struct

  let test_print: string -> unit = 
    fun s -> 
      printf "\n\n==================\n       %s     \n==================\n\n" s

    
  let print_asttypes_arg_label: Asttypes.arg_label -> string = fun x  ->
    match x with 
      | Nolabel -> "Nolabel"
      | Labelled s -> "label: "^s
      | Optional s -> "optional: "^s
 


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



(*helping print functions to see the extraction process*)
let print_stmt : S.st -> unit = fun st -> 
  let open S in 
  match st with
  |SELECT ((_,col_name,_,_),_,_,_) -> printf "\n ꜱᴇʟᴇᴄᴛ %s" col_name   
  |INSERT _ -> printf "\n ɪɴꜱᴇʀᴛ"   
  |UPDATE _ -> printf "\n ᴜᴩᴅᴀᴛᴇ"   
  |DELETE _ -> printf "\n ᴅᴇʟᴇᴛᴇ"   
  |_ -> failwith "ERROR print_stmt: unexpected sql operation"

let print_var: V.t -> unit = let open V in 
      fun x -> printf "\n %s" @@ name x

let print_var_list:  V.t list -> unit = fun var_list -> 
  let _ = print_string "\nExtracted VARS:\n########";
          List.iter print_var var_list in
  print_string "\n########\n\n\n"

let print_stmts_list : S.st list -> unit = fun st_list -> 
  let _ = print_string "\nExtracted TXN:\n########";
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
      let t_name = App.Tableschema.name table in
      Var.Table.make  (App.Tableschema.name table)
      (List.map (fun (col_name, SomeType col_type, col_pk) -> 
                     (t_name,col_name,(convert_type_to_IR col_type), col_pk)
                ) 
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
      | _ -> Utils.print_helpful_type_desc tp;  failwith "encodeIR: convert_types error"


let convert_param: (Ident.t * type_desc) -> V.t  = 
  fun (id,tp) ->  V.make id.name (convert_types tp) V.PARAM


let rec extract_operands:  (string*V.t) list -> Typedtree.expression_desc -> F.L.expr = 
  fun var_list -> fun desc -> match desc with
    |Texp_field (_,_,{lbl_name}) ->  F.L.Var (V.make lbl_name T.Int FIELD) 
    |Texp_ident (Pident {name},_,_) -> let open List in
                                       if mem name  @@ fst @@ split var_list
                                       then F.L.Var (V.make name T.Int LOCAL)
                                       else F.L.Var (V.make name T.Int PARAM)
    |Texp_constant (Const_int i) -> F.L.Cons i
    |Texp_apply ({exp_desc=Texp_ident (Pdot (_,op,_),_,_)},[(Nolabel,Some l);(Nolabel,Some r)]) ->
      let lhs = extract_operands var_list (l.exp_desc) in 
      let rhs = extract_operands var_list (r.exp_desc) in
      match op with
        |"-" -> F.L.MINUS (lhs,rhs)
        |"+" -> F.L.PLUS (lhs,rhs)
    |_ -> let _ = Utils.print_helpful_expression_desc desc in failwith "ERROR extract_operands: case not handled yet"  
  

let extract_where_clause: (string*V.t) list -> Typedtree.expression_desc -> Typedtree.expression_desc -> string -> Fol.t =
  fun var_list -> fun desc_l -> fun desc_r ->  fun op ->
    let l_var = extract_operands var_list desc_l in
    let r_var = extract_operands var_list desc_r in
      match op with 
        |"=" -> F.make (F.L.Eq (l_var,r_var))
        |_ -> failwith "ERROR extract_where_clause: the operation not handled yet"


(*handle the rhs of select*)
let extract_select: (string*V.t) list -> Typedtree.expression -> string*string*string*Fol.t  =  
  fun var_list -> fun body -> match body.exp_desc with
    |Texp_apply (e0,[(arg1,Some exp1);(arg3,Some exp3);(arg2,Some exp2)]) -> (*this is old version: before adding column support. should be eventually removed*)
      let open Utils in
      let Texp_construct (_,{cstr_name=table_name},_) = exp1.exp_desc in (*table name is extracted here*) (*the rest are not used for this case but I'm gonna keep them for future*)
      let Texp_construct (_,{cstr_name=column_name},_) = exp3.exp_desc in (*column name is extracted here*) 
      let Texp_function (_,[{c_lhs;c_guard=None;c_rhs}],_) = exp2.exp_desc in (*the rest contains the where funtion some where...*)
        let Tpat_var ({name},_) = c_lhs.pat_desc in (* the u in where clause/ for future use*)
        let Texp_apply ({exp_desc = Texp_ident (Pdot (_,op,_),_,_) }, (*operator is extracted here. e.g. =*)
                        [(Nolabel,Some {exp_desc=exp1});(Nolabel,Some {exp_desc=exp2})] )= c_rhs.exp_desc in (*operands are extracted here: exp_desc are passed to a handler*) 
      let Texp_ident (Pdot (_,select_kind,_) ,_,_) = e0.exp_desc in 
      let wh_c = extract_where_clause var_list exp1 exp2 op in
      (select_kind,table_name,column_name,wh_c)
    
    |_ -> Utils.print_helpful_expression_desc  body.exp_desc; 
          failwith "ERROR extract_select_table_name: unexpected case for handling select"



(*handle the rhs of update*)
let extract_update: (Asttypes.arg_label * Typedtree.expression option) list -> string*string*Fol.t = 
  fun [(_,Some exp1);(_,Some exp2);(_,Some exp3)] ->
        let Texp_construct (_,{cstr_name=table_name},_) = exp1.exp_desc in (*already extracted... keeping the rest for the future*)
        let Texp_function (_,[{c_lhs=fun_lhs;c_guard=None;c_rhs={exp_desc=Texp_setfield(u_in_fun,{txt=Lident field_name},_,right_of_arrow)}}],_) = exp2.exp_desc in (*the updating function*)
        let Texp_ident (Pident uu,_,{val_type=record_type}) = u_in_fun.exp_desc in 
        let Texp_function (_,[{c_lhs;c_guard=None;c_rhs}],_) = exp3.exp_desc in (*the where clause*)
          let Tpat_var ({name},_) = c_lhs.pat_desc in 
          let Texp_apply ({exp_desc = Texp_ident (Pdot (_,op,_),_,_) }, (*operator is extracted here. e.g. =*)
                           [(Nolabel,Some {exp_desc=exp1});(Nolabel,Some {exp_desc=exp2})] )= c_rhs.exp_desc in (*operands are extracted here: exp_desc are passed to a handler*)
        let wh_c = extract_where_clause [] exp1 exp2 op in 
        let column_name = let open String in 
                          let prefix_size = index field_name '_' in
                          let prefix_name = uppercase @@ sub field_name 0 prefix_size in (*fine the prefix before _ and capitalize it*)
                          let postfix_name = sub field_name (prefix_size+1) (length field_name - prefix_size - 1) 
                          in prefix_name^"_"^postfix_name
        in (table_name,column_name,wh_c)


let extract_variable: Typedtree.pattern_desc -> (string*V.t) =
  fun pat_desc ->
    let Tpat_var ({name},_) = pat_desc in
    (name,(V.make name T.Int V.LOCAL)) (*TODO types must be extracted*)




let rec convert_body_rec: (string*V.t) list -> S.st list -> 
                            Typedtree.expression -> S.st list*(string*V.t) list = 
  fun old_vars -> fun old_stmts -> 
  fun {exp_desc;exp_loc;exp_extra;exp_type;exp_env;exp_attributes} ->
    match exp_desc with 
    (*select case*)
    |Texp_let (_,[{vb_pat;vb_expr}],body) ->  
      let (name,curr_var) = extract_variable @@ vb_pat.pat_desc in 
      let (select_kind,accessed_table,accessed_col,wh_clause) = extract_select old_vars vb_expr in
      begin match select_kind with
      |"select1" -> let new_stmt_col = (accessed_table,accessed_col, T.Int ,true) in  (*TODO column type is assumed to always be integer*)
                    let new_stmt = S.SELECT (new_stmt_col,curr_var,wh_clause,Fol.my_true) in 
                      convert_body_rec (old_vars@[(name,curr_var)])  
                                       (old_stmts@[new_stmt]) 
                                       body
      |"select" -> failwith "ERROR convert_body_rec: unhandled select kind (select)" 
      |"select_max" -> failwith "ERROR convert_body_rec: unhandled select kind (select_max)" 
      |"select_min" -> failwith "ERROR convert_body_rec: unhandled select kind (select min)" 
      |"select_count" -> failwith "ERROR convert_body_rec: unhandled select kind (select_count)" 
      |_ -> failwith "(encodeIR.ml) ERROR  convert_body_rec: unexpected select kind" 
      end
    


    (*final delete/update/insert cases*)
    |Texp_apply (app_exp,ae_list) -> 
      let Texp_ident (app_path,_,_) = app_exp.exp_desc in
      let Path.Pdot (_,op,_) = app_path in 
      let new_stmt = match op with
                      |"insert" -> failwith "ERROR convert_body_rec: insert is not handled yet"
                      |"update" ->  let (accessed_table,accessed_col_name,wh_c) = extract_update ae_list in
                                    let accessed_col = (accessed_table,accessed_col_name, T.Int ,true) in 
                                    S.UPDATE (accessed_col,Fol.my_const,wh_c,Fol.my_true)
                      |"delete" -> failwith "ERROR convert_body_rec :delete is not handled yet!"
                      |_ -> failwith "ERROR convert_body_rec: unexpected SQL operation"
    in (old_stmts@[new_stmt],old_vars)
    (*intermediate del/upt/ins*)
    |Texp_sequence (app_exp1,body_exps) -> 
        (convert_body_rec old_vars (fst @@ convert_body_rec old_vars old_stmts app_exp1) body_exps)
    |Texp_construct _ -> (old_stmts,old_vars)
    |_ -> Utils.print_helpful_expression_desc exp_desc;  failwith "ERROR convert_body_rec: unexpected case"

(*TODO*)
(*TODO*)


let convert_body_stmts: Typedtree.expression -> (S.st list*(string*V.t) list) =
  fun body -> 
  let (output_st,output_var) = convert_body_rec [] [] body in
  (*testing*)
  let _ = Utils.print_stmts_list output_st in 
  let _ = Utils.print_var_list @@ snd @@ List.split output_var in 
  (output_st,output_var)


let convert : G.t -> L.t = 
  fun (G.T {name;rec_flag;args_t;res_t;body}) -> 
    let t_name = remove_txn_tail name.name in
let t_params = List.map convert_param args_t in
    let (stmts,vars) = convert_body_stmts body in
    L.make t_name t_params stmts vars  

end
	
(*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)

let extract_program: App.t -> (Var.Table.t list * L.t list) = 
    fun (App.T {schemas; txns}) -> 
      let cv_schemas =  List.map (fun x -> Tables.convert x) schemas in
      let cv_txns = List.map (fun x -> Txn.convert x) txns in 
      (cv_schemas,cv_txns) 

































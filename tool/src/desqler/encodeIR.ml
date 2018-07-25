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
let to_cap = String.capitalize_ascii

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
    |Texp_ident _ -> "\nTexp_ident"
    |Texp_constant _ -> "\nTexp_constant"
    |Texp_let _ -> "\nTexp_let"
    |Texp_function _ -> "\nTexp_function"
    |Texp_apply _ -> "\nTepx_apply"
    |Texp_match _ -> "\nTexp_match"
    |Texp_try _ -> "\nTexp_try"
    |Texp_tuple _ -> "\nTexp_tuple"
    |Texp_construct _ -> "\nTexp_construct"
    |Texp_variant _ -> "\nTexp_variant"
    |Texp_record _ -> "\nTexp_record"
    |Texp_field _ -> "\nTexp_field"
    |Texp_setfield _ -> "\nTexp_setfield"
    |Texp_array _ -> "\nTexp_array"
    |Texp_ifthenelse _ -> "\nTexp_ifthenelse"
    |Texp_sequence _ -> "\nTexp_sequence"
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





let rec print_expression : F.L.expr -> string = fun exp -> 
let open F.L in
  match exp with
    |Cons i -> string_of_int i
    |Str s -> s
    |Var v -> V.name v
    |_ -> "not printing yet...."


let rec print_condition : F.t -> string = fun (condition) -> 
let open F.L in 
  match condition with 
    |Bool b -> "not printing yet...."
    |Gt (s1,s2) -> "("^(print_expression s1)^")>("^(print_expression s2)^")"
    |Eq (s1,s2) -> "("^(print_expression s1)^")("^(print_expression s2)^")"
    |Lt (s1,s2) -> "("^(print_expression s1)^")=("^(print_expression s2)^")"
    |Nq (s1,s2) -> "("^(print_expression s1)^")!=("^(print_expression s2)^")"
    |AND (s1,s2) -> (print_condition s1)^" && "^(print_condition s2)
    |OR (s1,s2) -> (print_condition s1)^" || "^(print_condition s2)
    |NOT s -> "~("^(print_condition s)^")"
    |_ -> "encodeIR.ml: print_condition ERROR: Unexpected condition"



(*helping print functions to see the extraction process*)
let print_stmt : S.st -> unit = fun st -> 
  let open S in 
  match st with
  |SELECT ((_,col_name,_,_),_,_,x) -> printf "\n %s: ꜱᴇʟᴇᴄᴛ %s" (print_condition x) col_name   
  |MAX_SELECT ((_,col_name,_,_),_,_,x) -> printf "\n %s: ꜱᴇʟᴇᴄᴛ MAX of %s"  (print_condition x) col_name   
  |MIN_SELECT ((_,col_name,_,_),_,_,x) -> printf "\n %s: ꜱᴇʟᴇᴄᴛ MIN of %s"  (print_condition x) col_name   
  |INSERT (t,_,x)  -> printf "\n %s: ɪɴꜱᴇʀᴛ %s "  (print_condition x) (Var.Table.name t) 
  |UPDATE (_,_,_,x) -> printf "\n %s: ᴜᴩᴅᴀᴛᴇ"  (print_condition x)  
  |DELETE (t,_,x) -> printf "\n %s: ᴅᴇʟᴇᴛᴇ %s" (print_condition x) (Var.Table.name t)  
  |RANGE_SELECT (_,_,_,x) -> printf "\n %s: SELECT RANGE"  (print_condition x)
  |CHOOSE (v1,v2,_,x) -> printf "\n %s: CHOOSE %s from %s" (print_condition x) (V.name v1) (V.name v2)
  |_ -> failwith "ERROR print_stmt: unexpected sql operation"

let print_var: V.t -> unit = let open V in 
      fun x -> printf "\n %s.%s of %s (%s)" (name x) (field x) (table x) (kind_to_string @@ kind x)

let print_var_list:  V.t list -> unit = fun var_list -> 
let _ = List.iter print_var var_list in
    print_string "\n-------"

let print_stmts_list : S.st list -> unit = fun st_list -> 
  let _ = List.iter print_stmt st_list in
    print_string "\n-------"

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
      | Tconstr (patht,[{desc=Tconstr (Pident x,_,_)}],_) -> 
        begin 
					match patht with
					|Pident {stamp;name;flags} -> 
          begin match name with "int" -> T.Int | "string" -> T.String | "bool" -> T.Bool |"list" -> T.Set x.name end
					end
      | Tconstr (patht,[],_) -> 
        begin 
					match patht with
					|Pident {stamp;name;flags} -> 
          begin match name with "int" -> T.Int | "string" -> T.String | "bool" -> T.Bool |"list" -> T.Set "salam" end
					end
			| Tlink {desc;level;id} -> convert_types desc
      | _ -> Utils.print_helpful_type_desc tp;  failwith "encodeIR: convert_types error"


let convert_param: (Ident.t * type_desc) -> V.t  = 
  fun (id,tp) ->  
    match convert_types tp with
    |T.Set table -> V.make id.name "salam" (Some (String.capitalize_ascii table)) (convert_types tp) V.RECORD
    |_ -> V.make id.name "salam" None (convert_types tp) V.PARAM

let rec extract_operands:  (string*V.t) list -> Typedtree.expression_desc -> (string * V.t) list -> (F.L.expr*(string * V.t) list) = 
  fun var_list -> fun desc -> fun already_extracted_vars -> match desc with
    |Texp_field ({exp_desc=Texp_ident (Pident before_dot,_,_)},_,{lbl_name}) ->  
    let open List in 
    let var_exists = List.filter (fun (v,_) -> before_dot.name = v) (var_list) in
    begin match var_exists with
          |[(v_name,v)] -> (F.L.Var (V.make before_dot.name lbl_name (Some (V.table v)) T.Int RECORD),already_extracted_vars@[(v_name,v)])
          |[] -> (F.L.Var (V.make lbl_name "salam" None T.Int FIELD),already_extracted_vars)
    end
    |Texp_ident (Pident {name},_,_) -> let open List in
                                       if mem name  @@ fst @@ split var_list
                                          then (F.L.Var (V.make name "salam" None T.Int LOCAL),
                                                    already_extracted_vars@[find (fun (vn,_) ->(name=vn)) var_list])
                                          else (F.L.Var (V.make name "salam" None T.Int PARAM),[])
    |Texp_constant (Const_int i) -> (F.L.Cons i,already_extracted_vars) (*integer constant*)
    |Texp_constant (Const_string (s,_)) -> (F.L.Str s,already_extracted_vars) (*string constant*)
    |Texp_apply ({exp_desc=Texp_ident (Pdot (_,op,_),_,_)},[(Nolabel,Some l);(Nolabel,Some r)]) ->
      let (lhs,l_ext_vars) = extract_operands var_list (l.exp_desc) already_extracted_vars in 
      let (rhs,r_ext_vars) = extract_operands var_list (r.exp_desc) already_extracted_vars in
      begin
      match op with
        |"-" -> (F.L.MINUS (lhs,rhs),l_ext_vars@r_ext_vars)
        |"+" -> (F.L.PLUS (lhs,rhs),l_ext_vars@r_ext_vars)
      end
    |_ -> let _ = Utils.print_helpful_expression_desc desc in failwith "ERROR extract_operands: case not handled yet"  
  

let rec extract_where_clause: (string*V.t) list -> Typedtree.expression -> (string * V.t) list -> (Fol.t*(string * V.t) list) =
  fun var_list -> fun exp  -> fun already_extracted_vars -> 
      match exp.exp_desc with
        |Texp_apply ({exp_desc = Texp_ident (Pdot (_,op,_),_,_) }, (*operator is extracted here. e.g. =*)
                        [(Nolabel,Some l_exp);(Nolabel,Some r_exp)] ) ->
          let r_desc = r_exp.exp_desc in
          let l_desc = l_exp.exp_desc in
          let (l_op,l_vars) = extract_operands var_list l_desc already_extracted_vars in
          let (r_op,r_vars) = extract_operands var_list r_desc already_extracted_vars in
          begin
          match op with 
            |"=" ->  (F.L.Eq (l_op,r_op),r_vars@l_vars)
            |">" ->  (F.L.Gt (l_op,r_op),r_vars@l_vars)
            |"<" ->  (F.L.Lt (l_op,r_op),r_vars@l_vars)
            |"!=" -> (F.L.Nq (l_op,r_op),r_vars@l_vars)
            |"&&" -> let (r_rec_call,r_rec_vars) = extract_where_clause var_list r_exp already_extracted_vars in
                     let (l_rec_call,l_rec_vars) = extract_where_clause var_list l_exp already_extracted_vars in
                     ((F.L.AND (r_rec_call, l_rec_call)),r_rec_vars@l_rec_vars)
            |"||" -> let (r_rec_call,r_rec_vars) = extract_where_clause var_list r_exp already_extracted_vars in
                     let (l_rec_call,l_rec_vars) = extract_where_clause var_list l_exp already_extracted_vars in
                     ((F.L.OR (r_rec_call, l_rec_call)),r_rec_vars@l_rec_vars)
            |_ -> failwith "ERROR extract_where_clause: the operation not handled yet" end
        |Texp_ident _ -> let (op_extd,var_rtnd) = extract_operands var_list exp.exp_desc already_extracted_vars in
                         (F.L.Bool op_extd, var_rtnd)
        |_ -> failwith "encodeIR.ml: extract_where_clause"
 
(*given the accessed variables, returns what statements initially sourced these variables*)
let find_accessed_statements: (string * V.t) list -> (S.st * string * F.t) list -> S.st list  = 
  fun accessed_vars_names -> fun all_stmts -> 
 (*   let _ = print_int @@ List.length all_stmts in*)
    let accessed_vars = List.map (fun (_,v) -> v) accessed_vars_names in
    List.fold_left  
      (fun old_l -> fun (curr_st,_,_) -> match curr_st with
          |S.SELECT (_,v,_,_) -> if List.mem v accessed_vars then [curr_st]@ old_l else old_l
          |S.RANGE_SELECT (_,v,_,_) -> if List.mem v accessed_vars then [curr_st]@ old_l else old_l
          |S.MAX_SELECT (_,v,_,_) -> if List.mem v accessed_vars then [curr_st]@ old_l else old_l
          |S.MIN_SELECT (_,v,_,_) -> if List.mem v accessed_vars then [curr_st]@ old_l else old_l
          |S.COUNT_SELECT (_,v,_,_) -> if List.mem v accessed_vars then [curr_st]@ old_l else old_l
          |_ -> old_l) [] all_stmts


       

(*handle the rhs of select*)
let extract_select: (string*V.t) list -> Typedtree.expression -> 
(S.st * string * F.t) list -> string*string*string*Fol.t*S.st list  =  
  fun var_list -> fun body -> fun old_stmt_list -> match body.exp_desc with
    |Texp_apply (e0,[(arg1,Some exp1);(arg3,Some exp3);(arg2,Some exp2)]) -> (*this is old version: before adding column support. should be eventually removed*)
      let open Utils in
      let Texp_construct (_,{cstr_name=table_name},_) = exp1.exp_desc in (*table name is extracted here*) (*the rest are not used for this case but I'm gonna keep them for future*)
      let Texp_construct (_,{cstr_name=column_name},_) = exp3.exp_desc in (*column name is extracted here*) 
      let Texp_function (_,[{c_lhs;c_guard=None;c_rhs}],_) = exp2.exp_desc in (*the rest contains the where funtion some where...*)
      let Tpat_var ({name},_) = c_lhs.pat_desc in (* the u in where clause/ for future use*)
      let Texp_ident (Pdot (_,select_kind,_) ,_,_) = e0.exp_desc in 
      let (wh_c,accessed_vars) = extract_where_clause var_list c_rhs [] in
      let accessed_stmts = find_accessed_statements accessed_vars old_stmt_list in
      (select_kind,table_name,column_name,wh_c,accessed_stmts)
    (*!!!  THE CHOOSE CASE*)
    |Texp_apply (e0,[(arg1,Some exp_func);(arg2,Some exp_vset)]) -> 
      let Texp_ident (Pident {name=v_name},_,_) = exp_vset.exp_desc in (*the list being chosen from*) 
      let Texp_function (_,[{c_lhs;c_guard=None;c_rhs}],_) = exp_func.exp_desc in
        let Tpat_var ({name},_) = c_lhs.pat_desc in (* the u in where clause/ for future use*)
      let Texp_ident (Pdot (_,choose_kind,_) ,_,_) = e0.exp_desc in 
      let (wh_c,accessed_vars) = extract_where_clause var_list c_rhs [] in
      let accessed_stmts = find_accessed_statements accessed_vars old_stmt_list in
      (choose_kind,v_name,"",wh_c,accessed_stmts) (*the second argument here is interpreted as the list being chosen from*)

    |_ -> Utils.print_helpful_expression_desc  body.exp_desc; 
          failwith "ERROR extract_select_table_name: unexpected case for handling select"



(*handle the rhs of update*)
let extract_update: (Asttypes.arg_label * Typedtree.expression option) list -> (string * V.t) list -> (S.st * string * F.t) list -> string*string*Fol.t*F.L.expr*S.st list = 
  fun [(_,Some exp1);(_,Some exp2);(_,Some exp3)] -> fun old_var_list ->  fun old_stmt_list ->
        let Texp_construct (_,{cstr_name=table_name},_) = exp1.exp_desc in (*already extracted... keeping the rest for the future*)
        let Texp_function (_,[{c_lhs=fun_lhs;c_guard=None;c_rhs=
                  {exp_desc=Texp_setfield(u_in_fun,{txt=Lident field_name},_,
                    {exp_desc=right_of_arrow})}}],_) = exp2.exp_desc in (*the updating function*)
        let (update_expression,op_accessed_var_list) = extract_operands old_var_list right_of_arrow [] in
        let Texp_ident (Pident uu,_,{val_type=record_type}) = u_in_fun.exp_desc in 
        let Texp_function (_,[{c_lhs;c_guard=None;c_rhs}],_) = exp3.exp_desc in (*the where clause*)
          let Tpat_var ({name},_) = c_lhs.pat_desc in 
        let (wh_c,wh_accessed_var_list) = extract_where_clause old_var_list c_rhs [] in 
        let accessed_stmts = find_accessed_statements (wh_accessed_var_list@op_accessed_var_list) old_stmt_list in
        let column_name = let open String in 
                          let prefix_size = index field_name '_' in
                          let prefix_name = uppercase @@ sub field_name 0 prefix_size in (*fine the prefix before _ and capitalize it*)
                          let postfix_name = sub field_name (prefix_size+1) (length field_name - prefix_size - 1) 
                          in prefix_name^"_"^postfix_name
                          in (table_name,column_name,wh_c,update_expression,accessed_stmts)


let extract_delete:(Asttypes.arg_label * Typedtree.expression option) list -> (string * V.t) list -> 
  (S.st * string * F.t) list -> string*Fol.t*S.st list = 
  fun  [(_,Some exp1);(_,Some exp2)] -> fun old_var_list -> fun old_stmt_list ->
    let Texp_construct (_,{cstr_name=table_name},_) = exp1.exp_desc in 
    let Texp_function (_,[{c_lhs;c_guard=None;c_rhs}],_) = exp2.exp_desc in (*the where clause*)
    let (wh_c,wh_accessed_var_list) = extract_where_clause old_var_list c_rhs [] in
    let accessed_stmts = find_accessed_statements wh_accessed_var_list old_stmt_list in
    (table_name,wh_c,accessed_stmts)


(*extract info on the lhs of selects*)
  let extract_variable: Typedtree.pattern_desc -> string -> (string*V.t) =
  fun pat_desc -> fun accessed_table -> 
  let Tpat_var ({name},{txt}) = pat_desc in
    (name,(V.make name "salam" (Some accessed_table) T.Int V.LOCAL)) (*TODO types must be extracted*)

(*extract info on the lhs of choose*)
  let extract_choose_variable: Typedtree.pattern_desc -> V.t -> (string*V.t) =
  fun pat_desc -> fun chosen_var -> 
  let Tpat_var ({name},{txt}) = pat_desc in
    (name,(V.make name (V.field chosen_var) (Some (V.table chosen_var)) T.Int RECORD))


let  extract_insert: (Asttypes.arg_label * Typedtree.expression option) list  -> (string * V.t) list -> 
(S.st * string * F.t) list -> (string*(string*F.L.expr) list*S.st list) = 
fun [(_,Some exp_cons);(_,Some exp_record)] -> fun var_list -> fun old_stmt_list ->
  let Texp_construct (_,{cstr_name=table_name},_) = exp_cons.exp_desc  in
  let Texp_record (v_list,_) = exp_record.exp_desc in
  let record = List.map (fun (_,{lbl_name},e) -> (lbl_name,(fst @@ extract_operands var_list e.exp_desc []))) v_list in
  let all_vars_accessed = List.fold_left (fun old_l -> fun (_,_,e) -> old_l@(snd@@extract_operands var_list e.exp_desc [])) [] v_list in
  let accessed_stmts = find_accessed_statements all_vars_accessed old_stmt_list in
  (table_name,record,accessed_stmts)


let eaxtract_condition: (string * V.t) list -> Typedtree.expression -> (F.t*(string * V.t) list)  =
  fun var_list -> fun exp ->
    match exp.exp_desc with
    |Texp_construct ({txt=Lident "true"},_,_) -> (F.L.Bool (F.L.Var V.true_var),[])
    |Texp_construct ({txt=Lident "false"},_,_) ->(F.L.Bool (F.L.Var V.false_var),[])
    |(Texp_apply _) -> extract_where_clause var_list exp []
    |Texp_ident _ ->  extract_where_clause var_list exp []
    |_ -> Utils.print_helpful_expression_desc exp.exp_desc;  failwith "enncodeIR.ml: eaxtract_condition error"




(*given a list of statements whose value is being used, the old statement list is updated with the current path condition*)
let update_statements: F.t -> S.st list ->  (S.st*string*F.t) list ->  (S.st*string*F.t) list =
  fun curr_cond -> fun accessed_stmts -> fun old_statements -> 
    List.fold_left (fun old_l -> fun (curr_st,st_type,old_cond) -> 
      let updated_cond = F.L.OR (old_cond,curr_cond) in
      let result = 
        if List.exists (fun st -> st=curr_st) accessed_stmts
        then old_l@[(curr_st,st_type,updated_cond)]
        else old_l@[(curr_st,st_type,old_cond)]
      in result) [] old_statements



let merge_statements: (S.st * string * F.t) -> (S.st * string * F.t) -> (S.st * string * F.t) =
  fun (st1,nm1,cd1) -> fun (st2,nm2,cd2) -> 
    if st1 = st2 && nm1=nm2 
    then (st1,nm1,F.L.OR (cd1,cd2))
    else failwith "ERROR (unexpected state): encodeIR.merge_statements"


(*merges the extracted statements from different program paths*)
let merge_lists: (S.st * string * F.t) list -> (S.st * string * F.t) list -> 
  (S.st * string * F.t) list -> (S.st * string * F.t) list = 
    fun l1 -> fun l2 -> fun ol -> 
      let open List in
      let o_name_list = map (fun (_,n,_) -> n) ol in
      let trimmed1 = fold_left (fun old_l -> fun (cst,cnm,ccd) -> 
          if mem cnm o_name_list then old_l else old_l@[(cst,cnm,ccd)] ) [] l1 in
      let trimmed2 = fold_left (fun old_l -> fun (cst,cnm,ccd) -> 
          if mem cnm o_name_list then old_l else old_l@[(cst,cnm,ccd)] ) [] l2 in
      let un_common_section = fold_left (fun old_l -> fun (curr_st,curr_nm,curr_cd) -> 
      let st_from1 = find (fun (_,n1,_) -> n1=curr_nm) l1 in
      let st_from2 = find (fun (_,n1,_) -> n1=curr_nm) l2 in
      let merged_statement = merge_statements st_from1 st_from2 in
      old_l@[merged_statement]) [] ol 
      in un_common_section@trimmed1@trimmed2
    




(**********)
(*The main extraction function*)
(**********)
let rec convert_body_rec:  string -> (int*int*int*int) -> F.t -> (string*V.t) list -> (S.st*string*F.t) list -> int -> 
                            Typedtree.expression  -> (S.st*string*F.t) list*(string*V.t) list = 
  fun txn_name -> fun (iter_s,iter_u,iter_d,iter_i) -> 
  fun curr_cond -> fun old_vars -> fun old_stmts ->  fun for_count ->
  fun {exp_desc;exp_loc;exp_extra;exp_type;exp_env;exp_attributes} ->
    match exp_desc with 
    (*select case*)
    |Texp_let (_,[{vb_pat;vb_expr}],body) ->  
      let (select_kind,accessed_table,accessed_col,wh_clause,accessed_stmts) = extract_select old_vars vb_expr old_stmts in
      let (name,curr_var) = extract_variable vb_pat.pat_desc accessed_table in 
      begin match select_kind with
      |"select1" -> let new_stmt_col = (accessed_table,accessed_col, T.Int ,true) in  (*TODO column type is assumed to always be integer*)
                    let new_stmt = S.SELECT (new_stmt_col,curr_var,wh_clause,curr_cond) in 
                    let new_type = txn_name^"_select_"^(string_of_int iter_s) in
                    let new_es_cond = F.my_false in
                    let updated_old_stmts = update_statements curr_cond accessed_stmts old_stmts in
                      convert_body_rec txn_name  (iter_s+1,iter_u,iter_d,iter_i) curr_cond (old_vars@[(name,curr_var)])  
                                       (updated_old_stmts@[(new_stmt,new_type,new_es_cond)]) for_count
                                       body
      |"select" ->  let new_stmt_col = (accessed_table,accessed_col, T.Int ,true) in  
                    let new_stmt = S.RANGE_SELECT (new_stmt_col,curr_var,wh_clause,curr_cond) in 
                    let new_type = txn_name^"_select_"^(string_of_int iter_s) in
                    let new_es_cond = F.my_false in
                    let updated_old_stmts = update_statements curr_cond accessed_stmts old_stmts in
                      convert_body_rec txn_name  (iter_s+1,iter_u,iter_d,iter_i) curr_cond (old_vars@[(name,curr_var)])  
                                       (updated_old_stmts@[(new_stmt,new_type,new_es_cond)]) for_count
                                       body
      |"select_max" -> let new_stmt_col = (accessed_table,accessed_col, T.Int ,true) in 
                       let new_stmt = S.MAX_SELECT (new_stmt_col,curr_var,wh_clause,curr_cond) in 
                       let new_type = txn_name^"_select_"^(string_of_int iter_s) in
                       let new_es_cond = F.my_false in
                       let updated_old_stmts = update_statements curr_cond accessed_stmts old_stmts in
                         convert_body_rec txn_name  (iter_s+1,iter_u,iter_d,iter_i) curr_cond (old_vars@[(name,curr_var)])  
                                       (updated_old_stmts@[new_stmt,new_type,new_es_cond]) for_count
                                       body
      |"select_min" -> let new_stmt_col = (accessed_table,accessed_col, T.Int ,true) in 
                       let new_stmt = S.MIN_SELECT (new_stmt_col,curr_var,wh_clause,curr_cond) in 
                       let new_type = txn_name^"_select_"^(string_of_int iter_s) in
                       let new_es_cond = F.my_false in
                       let updated_old_stmts = update_statements curr_cond accessed_stmts old_stmts in
                         convert_body_rec txn_name  (iter_s+1,iter_u,iter_d,iter_i) curr_cond (old_vars@[(name,curr_var)])  
                                       (updated_old_stmts@[new_stmt,new_type,new_es_cond]) for_count
                                       body
      |"choose" ->  let chosen_var = List.assoc accessed_table old_vars in (*accessed_table here is interpreted as the chosen var name*)
                    let (new_name,new_var) = extract_choose_variable vb_pat.pat_desc chosen_var  in
                    let new_stmt = S.CHOOSE (new_var,chosen_var,wh_clause,curr_cond) in
                    let new_es_cond = F.my_false in
                    let updated_old_stmts = update_statements curr_cond accessed_stmts old_stmts in
                    convert_body_rec txn_name  (iter_s,iter_u,iter_d,iter_i) curr_cond  
                                               (old_vars@[(new_name,new_var)]) 
                                               (updated_old_stmts@[new_stmt,"XX",new_es_cond]) for_count body
      

      |"select_count" -> failwith "ERROR convert_body_rec: unhandled select kind (select_count)" 
      |_ -> failwith "(encodeIR.ml) ERROR  convert_body_rec: unexpected select kind" 
      end
    
    (*final delete/update/insert cases*)
    |Texp_apply (app_exp,ae_list) -> 
      let Texp_ident (app_path,_,_) = app_exp.exp_desc in
      let Path.Pdot (_,op,_) = app_path in 
      let (new_stmt,new_var) = match op with 
                      |"insert" ->  let (table_name,var_list,accessed_stmts) = extract_insert ae_list old_vars old_stmts in 
                                    let inserted_table = Var.Table.make table_name [Var.my_col] in (*only table name matters. The actuall columns can be retrieved later*)
                                    let inserted_record = Fol.Record.T{name="test_record"; vars=var_list} in (*I'm gonna create test record for now*)
                                    let new_type = txn_name^"_insert_"^(string_of_int iter_i) in
                                    let updated_old_stmts = update_statements curr_cond accessed_stmts old_stmts in
                                    (updated_old_stmts@[(S.INSERT (inserted_table,inserted_record ,curr_cond),new_type,F.my_true)],old_vars)
 
                      |"update" ->  let (accessed_table,accessed_col_name,wh_c,update_expression,accessed_stmts) = extract_update ae_list old_vars old_stmts in
                                    let accessed_col = (accessed_table,accessed_col_name, T.Int ,true) in 
                                    let updated_old_stmts = update_statements curr_cond accessed_stmts old_stmts in
                                    let new_type = txn_name^"_update_"^(string_of_int iter_u) in
                                    (updated_old_stmts@[(S.UPDATE (accessed_col,update_expression,wh_c,curr_cond),new_type,F.my_true)],old_vars)
                      |"delete" ->  let (accessed_table_name,wh_c,accessed_stmts) = extract_delete ae_list old_vars old_stmts in
                                    let accessed_table = Var.Table.make accessed_table_name [] in
                                    let new_type = txn_name^"_delete_"^(string_of_int iter_d) in
                                    let updated_old_stmts = update_statements curr_cond accessed_stmts old_stmts in
                                    (updated_old_stmts@[(S.DELETE (accessed_table,wh_c,curr_cond),new_type,F.my_true)],old_vars)
                      |"foreach" -> let [(_,Some {exp_desc= (Texp_ident(Pident vname,_,_))});(_,Some loop_body)] = ae_list in 
                                    let iterated_var = List.assoc vname.name old_vars in
                                    let accessed_stmts = find_accessed_statements [(vname.name,iterated_var)] old_stmts in
                                    let updated_old_stmts = update_statements curr_cond accessed_stmts old_stmts in
                                    let new_name = "loop_var_"^(string_of_int for_count)  in
                                    let new_for_var = V.make new_name (V.field iterated_var) (Some (V.table iterated_var)) T.Int RECORD in
                                    let new_stmt = S.CHOOSE (new_for_var,iterated_var,F.my_true,curr_cond) in
                                    convert_body_rec txn_name (iter_s,iter_u,iter_d,iter_i) curr_cond (old_vars@[new_name,new_for_var]) 
                                                      (updated_old_stmts@[(new_stmt,"XX",F.my_true)]) (for_count+1) loop_body
                      |_ -> failwith "ERROR convert_body_rec: unexpected SQL operation"
    in (new_stmt,new_var)
    (*intermediate del/upt/ins*)
    |Texp_sequence (app_exp1,body_exps) ->
    let (s_list1,v_list1) = convert_body_rec txn_name  (iter_s,iter_u,iter_d,iter_i) curr_cond old_vars old_stmts for_count app_exp1 in
      (*depending on what the latest statement was, the ticker must be updated*)
      let open List in
      let open Sql.Statement in
        begin (*XX are we sure it is the head? needs to be verified*)
        match (hd @@ rev s_list1) with
          |(INSERT _,_,_) -> convert_body_rec txn_name (iter_s,iter_u,iter_d,iter_i+1) 
                        curr_cond v_list1 s_list1  for_count body_exps
          |(DELETE _,_,_) -> convert_body_rec txn_name (iter_s,iter_u,iter_d+1,iter_i) 
                        curr_cond v_list1 s_list1  for_count body_exps
          |(UPDATE _,_,_) -> convert_body_rec txn_name (iter_s,iter_u+1,iter_d,iter_i) 
                        curr_cond v_list1 s_list1  for_count body_exps
          |(CHOOSE _,_,_) -> convert_body_rec txn_name (iter_s,iter_u,iter_d,iter_i) 
                        curr_cond v_list1 s_list1  for_count body_exps
        end
    (*the unit ()*)
    |Texp_construct _ -> (old_stmts,old_vars)
    (*if then else*)
    |Texp_ifthenelse (condition,then_cls,Some else_cls) ->
      let then_cond = F.L.AND (curr_cond,fst @@ (eaxtract_condition old_vars condition)) in
      let then_path = convert_body_rec txn_name  (iter_s,iter_u,iter_d,iter_i) then_cond old_vars old_stmts for_count then_cls in
      let else_cond = F.L.AND (curr_cond,F.L.NOT(fst @@ eaxtract_condition old_vars condition)) in
      let else_path =  convert_body_rec txn_name   (iter_s,iter_u,iter_d,iter_i) else_cond old_vars old_stmts for_count else_cls in
      let merged_list = merge_lists (fst then_path) (fst else_path) old_stmts in
      (merged_list,(snd then_path)@(snd else_path))
    |Texp_ifthenelse (condition,then_cls,None) -> 
      let then_cond = F.L.AND (curr_cond,(fst @@ eaxtract_condition old_vars condition)) in
      let then_path = convert_body_rec txn_name  (iter_s,iter_u,iter_d,iter_i) then_cond old_vars old_stmts for_count then_cls
      in then_path

    |Texp_function (_,[{c_lhs;c_guard=None;c_rhs}],_) -> 
        convert_body_rec txn_name (iter_s,iter_u,iter_d,iter_i) curr_cond old_vars old_stmts for_count c_rhs
  
    |_ -> Utils.print_helpful_expression_desc exp_desc;  failwith "ERROR convert_body_rec: unexpected case"


let convert_body_stmts: string -> (string * V.t) list -> Typedtree.expression -> ((S.st*string*F.t) list*(string*V.t) list) =
  fun txn_name -> 
  fun init_param_vars -> fun body -> 
  let (output_st,output_var) = convert_body_rec txn_name (1,1,1,1) F.my_true init_param_vars [] 1 body in
  (*testing*)
  let temp_output = List.map (fun (x,_,_)->x) output_st in
  (*let _ = Utils.print_stmts_list temp_output in 
  let _ = Utils.print_var_list @@ snd @@ List.split output_var in *)
  (output_st,output_var)


let convert : G.t -> L.t = 
  fun (G.T {name;rec_flag;args_t;res_t;body}) -> 
    let t_name = remove_txn_tail name.name in
    let (t_params,old_vars) = List.fold_left 
      (fun (old_parms,old_vars) -> fun arg -> let conv = convert_param arg in 
                                              match V.kind conv with
                                              |V.RECORD -> (old_parms@[conv],old_vars@[(V.name conv,conv)])
                                              |_ -> (old_parms@[conv],old_vars) 
      ) ([],[]) args_t in
    
    let (stmts,vars) = convert_body_stmts (to_cap t_name) old_vars body in
    L.make t_name t_params stmts vars  

end
	
(*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)

let extract_program: App.t -> (Var.Table.t list * L.t list) = 
    fun (App.T {schemas; txns}) -> 
      let cv_schemas =  List.map (fun x -> Tables.convert x) schemas in
      let cv_txns = List.map (fun x -> Txn.convert x) txns in 
      (cv_schemas,cv_txns) 


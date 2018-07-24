open App
open Sql
open Speclang
open Constants
module M = Misc
module T = Sql.Transaction
module S = Sql.Statement
module F = Fol
module V = Var.Variable
let _CORRECTNESS = Constants._CORRECTNESS
let to_cap = String.capitalize_ascii
let space size = (String.make size ' ')
let _TAB_4 = "\n"^space 32
let _TAB_3 = "\n"^space 28

module Utils = 
  struct

    let rec expression_to_string: int -> string -> string -> string -> F.L.expr -> string = 
      fun t_i -> fun record_name -> fun txn_name -> fun table_name -> 
      fun e -> match e with
        (*vars*)
        | F.L.Var (V.T{name="my_true"}) -> "true"
        | F.L.Var (V.T{name;field;table=None; tp; kn=V.PARAM})               -> "("^txn_name^"_Param_"^name^" t"^(string_of_int t_i)^")"
        | F.L.Var (V.T{name;field;table=None; tp; kn=V.LOCAL})               -> "("^txn_name^"_Var_"^name^" t"^(string_of_int t_i)^")"
        | F.L.Var (V.T{name;field;table=None; tp; kn=V.FIELD})               -> "("^table_name^"_Proj_"^name^" "^record_name^")"
        | F.L.Var (V.T{name;field;table=Some record_table; tp; kn=V.RECORD}) ->"("^record_table^"_Proj_"^field^" ("^txn_name^"_Var_"^name^" t"^(string_of_int t_i)^"))"
        (*other cases: constants, etc*)
        | F.L.Cons c -> string_of_int c
        | F.L.Str s -> "\""^s^"\""
        | F.L.MINUS (e1,e2) -> let lhs = expression_to_string t_i record_name txn_name table_name e1 in
                               let rhs = expression_to_string t_i record_name txn_name table_name e2 in  
                               "(- "^lhs^" "^rhs^")"
        | F.L.PLUS (e1,e2) ->  let lhs = expression_to_string t_i record_name txn_name table_name e1 in
                               let rhs = expression_to_string t_i record_name txn_name table_name e2 in  
                               "(+ "^lhs^" "^rhs^")"
        | _ -> failwith "ERROR expression_to_string: expression case not handled yet"

    let return_where: S.st -> Fol.t =
      fun stmt -> match stmt with
        |(S.SELECT (_,_,(wh),_)) -> wh
        |(S.RANGE_SELECT (_,_,(wh),_)) -> wh
        |(S.MAX_SELECT (_,_,(wh),_)) -> wh
        |(S.MIN_SELECT (_,_,(wh),_)) -> wh
        |(S.COUNT_SELECT (_,_,(wh),_)) -> wh
        |S.UPDATE (_,_,wh,_) -> wh
        |S.DELETE (_,wh,_) -> wh

    let return_reach: S.st -> Fol.t =
      fun stmt -> match stmt with
        |S.SELECT (_,_,_,(wh)) -> wh
        |S.RANGE_SELECT (_,_,_,(wh)) -> wh
        |S.MAX_SELECT (_,_,_,(wh)) -> wh
        |S.MIN_SELECT (_,_,_,(wh)) -> wh
        |S.COUNT_SELECT (_,_,_,(wh)) -> wh
        |S.UPDATE (_,_,_,(wh)) -> wh
        |S.DELETE (_,_,(wh)) -> wh
        |S.INSERT (_,_,wh) -> wh


    let rec extract_where: int -> string  -> string -> string -> Fol.t -> string = 
      fun t_i -> fun record_name -> fun txn_name -> fun table_name -> fun fol ->
       match (fol) with
        |F.L.Eq (e1,e2) -> let lhs = expression_to_string t_i record_name txn_name table_name e1 in
                           let rhs = expression_to_string t_i record_name txn_name table_name e2 in
                           "(= "^lhs^" "^rhs^")"
        |F.L.Gt (e1,e2) -> let lhs = expression_to_string t_i record_name txn_name table_name e1 in
                           let rhs = expression_to_string t_i record_name txn_name table_name e2 in
                           "(> "^lhs^" "^rhs^")"
        |F.L.Lt (e1,e2) -> let lhs = expression_to_string t_i record_name txn_name table_name e1 in
                           let rhs = expression_to_string t_i record_name txn_name table_name e2 in
                           "(< "^lhs^" "^rhs^")"
        |F.L.Nq (e1,e2) -> let lhs = expression_to_string t_i record_name txn_name table_name e1 in
                           let rhs = expression_to_string t_i record_name txn_name table_name e2 in
                           "(not (= "^lhs^" "^rhs^"))"

        |F.L.Bool b -> expression_to_string t_i record_name txn_name table_name b
        |F.L.AND (c1,c2) -> let lhs = extract_where t_i record_name txn_name table_name  c1 in
                            let rhs = extract_where t_i record_name txn_name table_name  c2 in
                           "(and "^lhs^" "^rhs^")"
        |F.L.OR (c1,c2) -> let lhs = extract_where t_i record_name txn_name table_name  c1 in
                            let rhs = extract_where t_i record_name txn_name table_name  c2 in
                           "(or "^lhs^" "^rhs^")"
        |F.L.NOT c1 -> let inner = extract_where t_i record_name txn_name table_name  c1 in
                           "(not "^inner^")"

        |_ -> failwith "rules.ml ERROR extract_where: the where claus case not handled yet "
 
      let extract_i_expr: int -> string -> string -> (string * Fol.L.expr) -> string =
      fun t_i -> fun txn_name -> fun table_name -> fun (s,exp) ->
        let value = expression_to_string t_i "r" txn_name table_name exp in
        _TAB_4^"(= ("^table_name^"_Proj_"^s^" r) "^value^")"


    let extract_condition: int -> string -> string -> S.st -> string =    
       fun t_i -> fun txn_name -> fun table_name -> fun stmt ->
				 match stmt with
					|(S.INSERT (_,Fol.Record.T{vars=c_list},_)) ->    
							let i_conds = List.fold_left (fun old_s -> fun curr_c ->
                        old_s^""^(extract_i_expr t_i txn_name table_name curr_c)) ";insert" @@ c_list
							in i_conds^"  "^(extract_where t_i "r" txn_name table_name (return_reach stmt))

          |_ -> (extract_where t_i "r"  txn_name table_name (return_where stmt))^"  "^(extract_where t_i "r" txn_name table_name (return_reach stmt))



  
      let accessed_common_table : S.st -> S.st -> string option = 
      fun stmt1 -> fun stmt2 ->
        match (stmt1,stmt2) with
          |(S.SELECT ((t_name_s,c_name_s,_,_),_,_,_) , S.UPDATE ((t_name_u,c_name_u,_,_),_,_,_)) -> 
            if t_name_s = t_name_u && c_name_s = c_name_u
            then Some t_name_s
            else None
          |(S.RANGE_SELECT((t_name_s,c_name_s,_,_),_,_,_) , S.UPDATE ((t_name_u,c_name_u,_,_),_,_,_)) -> 
            if t_name_s = t_name_u (*no need to check for the equality of columns*)
            then Some t_name_s
            else None
          |( S.UPDATE ((t_name_u1,c_name_u1,_,_),_,_,_) , S.UPDATE ((t_name_u2,c_name_u2,_,_),_,_,_) ) -> 
            if t_name_u1 = t_name_u2 && c_name_u1 = c_name_u2
            then Some t_name_u1
            else None
          |(S.UPDATE ((t_name_u,c_name_u,_,_),_,_,_) , S.SELECT ((t_name_s,c_name_s,_,_),_,_,_)) -> 
            if t_name_s = t_name_u && c_name_s = c_name_u
            then Some t_name_s
            else None
          |(S.INSERT (Var.Table.T{name=t_name_i},_,_), S.SELECT ((t_name_s,_,_,_),_,_,_)) -> 
            if t_name_s = t_name_i 
            then Some t_name_s
            else None  
					|(S.SELECT ((t_name_s,_,_,_),_,_,_), S.INSERT (Var.Table.T{name=t_name_i},_,_)) ->
            if t_name_s = t_name_i
            then Some t_name_s
            else None          
					|(S.DELETE (Var.Table.T{name=t_name_d},_,_), S.SELECT ((t_name_s,_,_,_),_,_,_)) -> 
            if t_name_s = t_name_d
            then Some t_name_s
            else None  
        	|( S.SELECT ((t_name_s,_,_,_),_,_,_),S.DELETE (Var.Table.T{name=t_name_d},_,_)) -> 
            if t_name_s = t_name_d
            then Some t_name_s
            else None  
          |(S.DELETE (Var.Table.T{name=t_name_d},_,_), S.MIN_SELECT ((t_name_s,_,_,_),_,_,_)) -> 
            if t_name_s = t_name_d
            then Some t_name_s
            else None  
          |(S.DELETE (Var.Table.T{name=t_name_d},_,_), S.MAX_SELECT ((t_name_s,_,_,_),_,_,_)) -> 
            if t_name_s = t_name_d
            then Some t_name_s
            else None  
          |(S.UPDATE ((t_name_u,c_name_u,_,_),_,_,_),S.RANGE_SELECT((t_name_s,c_name_s,_,_),_,_,_)) -> 
            if t_name_s = t_name_u (*no need to check for the equality of columns*)
            then Some t_name_s
            else None
          |(S.UPDATE ((t_name_u,c_name_u,_,_),_,_,_),S.MAX_SELECT((t_name_s,c_name_s,_,_),_,_,_)) -> 
            if t_name_s = t_name_u && c_name_s = c_name_u (*no need to check for the equality of columns*)
            then Some t_name_s
            else None
          |(S.UPDATE ((t_name_u,c_name_u,_,_),_,_,_),S.MIN_SELECT((t_name_s,c_name_s,_,_),_,_,_)) -> 
            if t_name_s = t_name_u && c_name_s = c_name_u (*no need to check for the equality of columns*)
            then Some t_name_s
            else None
          |(S.DELETE (Var.Table.T{name=t_name_d},_,_), S.RANGE_SELECT ((t_name_s,_,_,_),_,_,_)) -> 
            if t_name_s = t_name_d
            then Some t_name_s
            else None  
          |(S.RANGE_SELECT ((t_name_s,_,_,_),_,_,_),S.DELETE (Var.Table.T{name=t_name_d},_,_)) -> 
            if t_name_s = t_name_d
            then Some t_name_s
            else None  
          |(S.INSERT (Var.Table.T{name=t_name_i},_,_), S.RANGE_SELECT ((t_name_s,_,_,_),_,_,_)) -> 
            if t_name_s = t_name_i 
            then Some t_name_s
            else None  
          |(S.RANGE_SELECT ((t_name_s,_,_,_),_,_,_),S.INSERT (Var.Table.T{name=t_name_i},_,_)) -> 
            if t_name_s = t_name_i 
            then Some t_name_s
            else None  

          |(S.INSERT (Var.Table.T{name=t_name_i},_,_), S.MAX_SELECT ((t_name_s,_,_,_),_,_,_)) -> 
            if t_name_s = t_name_i 
            then Some t_name_s
            else None  
          |(S.INSERT (Var.Table.T{name=t_name_i},_,_), S.MIN_SELECT ((t_name_s,_,_,_),_,_,_)) -> 
            if t_name_s = t_name_i 
            then Some t_name_s
            else None  

    end


(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
module Wrappers = 
struct 
    
    (*final: R->*)
    let rt_final_wrapper (rule,txn1_name,txn2_name,all_conds)=
      "\n\n(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^"))
                    (=> (and ("^rule^"_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        "^all_conds^" )))"^_TAB_4^":named "^txn1_name^"-"^txn2_name^"-"^(String.lowercase_ascii rule)^"-then))"


    (*final: ->R*)
    let tr_final_wrapper (rule,txn1_name,txn2_name,all_conds)=
      let conclusion = match rule with 
          "WW" -> "(or (WW_O o1 o2) (WW_O o2 o1))" | "WR" -> "(WR_O o1 o2)" in 
      "\n\n(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^") (not (= t1 t2)))
                    (=> "^all_conds^"
                        "^conclusion^" )))"^_TAB_4^":named "^txn1_name^"-"^txn2_name^"-"^"then-"^(String.lowercase_ascii rule)^"))"
      
    (*rule conditions*)
    let rule_wrapper (table_name,cond_list) =
      let conds = List.fold_left (fun old_s -> fun curr_cond -> old_s^_TAB_4^curr_cond) "" cond_list in
                _TAB_3^"(exists ((r "^(to_cap table_name)^"))"^_TAB_4^"(and "^conds^"))"
end 



(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*analyze statements according to the rules. If applicable, return the wrapped cnoditions as strings*)
module Analyze = 
struct
     (*WW->*)
     let analyze_stmts: string ->  string -> (S.st*string*F.t) -> (S.st*string*F.t) -> string -> string option = 
      fun txn_name1 -> fun txn_name2 -> fun (stmt1,sttyp1,esc1) -> fun (stmt2,sttyp2,esc2) -> fun dir -> 
        (*t1 and t2 are the same if the txns are the same*)
        let open Utils in 
        let open Wrappers in
        let es_conds_to_s1 = extract_where "" txn_name1 "" esc1 in
        let es_conds = match _CORRECTNESS with
                        |SERIALIZABILITY -> []
                        |EVENTUAL_SERIALIZABILITY -> [";ES conditions";"(or false "^es_conds_to_s1^")"] 
                        |_ -> failwith "ERROR (Unknown correctness criterion): analyze_stmts.rules.ml" in

        let type_conds = ["(= (otype o1) "^sttyp1^")";"(= (otype o2) "^sttyp2^")"] in
        match (stmt1,sttyp1,stmt2,sttyp2,dir) with
          
          (*-------------------*)
          (*WW*)
          (*1*)
          |(S.UPDATE _,_,S.UPDATE _,_,"->WW") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let u1_cond = extract_condition 1  (to_cap txn_name1) table stmt1 in
                             let u2_cond  = extract_condition 2 (to_cap txn_name2) table stmt2 in
                             Some (rule_wrapper (table, type_conds@["(IsAlive_"^table^" r t1)";"(IsAlive_"^table^" r t2)";u1_cond ; u2_cond]))
              |None -> None end
          
          (*2*)
          |(S.UPDATE _,_,S.UPDATE _,_,"WW->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let u1_cond = extract_condition 1  (to_cap txn_name1) table stmt1 in
                             let u2_cond  = extract_condition 2 (to_cap txn_name2) table stmt2 in
                             Some (rule_wrapper (table, type_conds@["(WW_"^table^"_O r o1 o2)";"(IsAlive_"^table^" r t1)";"(IsAlive_"^table^" r t2)";u1_cond ; u2_cond]))
              |None -> None end

          (*-------------------*)
          (*WR->*)
          (*3*)
          |(S.UPDATE _ ,_, S.SELECT(_,v,_,_),_,"WR->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 2  (to_cap txn_name2) table stmt2 in
                             let u_cond  = extract_condition 1 (to_cap txn_name1) table stmt1 in
                             let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              Some (rule_wrapper
                                      (table, es_conds@type_conds@["(IsAlive_"^table^" r t1)";"(WR_"^table^"_O r o1 o2)";null_cond;s_cond;u_cond]))
              |None -> None end 
 		      (*4*)
          |(S.INSERT (_,_,_) ,_, S.SELECT (_,v,_,_),_, "WR->")->
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond =  extract_condition 1 (to_cap txn_name1) table stmt1 in
															let wr_cond = "(WR_Alive_"^table^" r o1 o2)" in
															let alive_cond = "(IsAlive_"^table^" r t2)" in
                              Some (rule_wrapper (table,es_conds@type_conds@[s_cond;i_cond;alive_cond;null_cond;wr_cond]))
              |None -> None end
          (*5*)
          |(S.DELETE (_,_,_),_, S.SELECT (_,v,_,_),_, "WR->")->
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond =  extract_condition 1 (to_cap txn_name1) table stmt1 in
															let wr_cond = "(WR_Alive_"^table^" r o1 o2)" in
															let alive_cond_d = "(IsAlive_"^table^" r t1)" in
															let alive_cond_s = "(not (IsAlive_"^table^" r t2))" in
                              Some (rule_wrapper (table,es_conds@type_conds@[s_cond;i_cond;alive_cond_d;alive_cond_s;null_cond;wr_cond]))
              |None -> None end
          (*10*)
          |(S.DELETE (_,_,_),_, S.RANGE_SELECT (_,v,_,_),_, "WR->")->
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond =  extract_condition 1 (to_cap txn_name1) table stmt1 in
															let wr_cond = "(WR_Alive_"^table^" r o1 o2)" in
															let alive_cond_d = "(IsAlive_"^table^" r t1)" in
															let alive_cond_s = "(not (IsAlive_"^table^" r t2))" in
                              Some (rule_wrapper (table,es_conds@type_conds@[s_cond;i_cond;alive_cond_d;alive_cond_s;wr_cond]))
              |None -> None end

          (*6*)
          |(S.UPDATE _,_, S.RANGE_SELECT(_,v,_,_),_,"WR->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 2  (to_cap txn_name2) table stmt2 in
                             let u_cond  = extract_condition 1 (to_cap txn_name1) table stmt1 in
                             let null_cond = "("^(to_cap txn_name2)^"_SVar_"^(V.name v)^" t2 r)" in
                              Some (rule_wrapper
                                      (table, es_conds@type_conds@["(IsAlive_"^table^" r t1)";"(WR_"^table^"_O r o1 o2)";null_cond;s_cond;u_cond]))
              |None -> None end 
 		      
          (*7*)
          |(S.INSERT (_,_,_),_, S.RANGE_SELECT (_,v,_,_),_, "WR->")->
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond =  extract_condition 1 (to_cap txn_name1) table stmt1 in
															let wr_cond = "(WR_Alive_"^table^" r o1 o2)" in
															let alive_cond = "(IsAlive_"^table^" r t2)" in
                              Some (rule_wrapper (table,es_conds@type_conds@[s_cond;i_cond;alive_cond;wr_cond]))
              |None -> None end
 



          (*-------------------*)
          (*RW->*)
          (*12*)
          |(S.SELECT _,_,S.UPDATE _,_, "RW->") -> 
            begin
              match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 1  (to_cap txn_name1) table stmt1 in
                             let u_cond  = extract_condition 2 (to_cap txn_name2) table stmt2 in
                Some (rule_wrapper (table, es_conds@type_conds@["(IsAlive_"^table^" r t2)";"(RW_"^table^"_O r o1 o2)";s_cond;u_cond]))
              |None -> None end
          (*15*)
          |(S.RANGE_SELECT(_,v,_,_),_,S.UPDATE _,_,"RW->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 1  (to_cap txn_name1) table stmt1 in
                             let u_cond  = extract_condition 2 (to_cap txn_name2) table stmt2 in
                             let null_cond = "(not ("^(to_cap txn_name1)^"_SVar_"^(V.name v)^" t1 r))" in
                              Some (rule_wrapper
                                      (table, es_conds@type_conds@["(IsAlive_"^table^" r t2)";"(RW_"^table^"_O r o1 o2)";null_cond;s_cond;u_cond]))
              |None -> None end 
 		      (*14*)
          |(S.SELECT (_,v,_,_),_,S.INSERT (_,_,_),_, "RW->" )->
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "("^to_cap txn_name1^"_isN_"^(V.name v)^" t1)" in
                              let s_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              let i_cond =  extract_condition 2 (to_cap txn_name2) table stmt2 in
															let wr_cond = "(RW_Alive_"^table^" r o1 o2)" in
															let alive_cond = "(not (IsAlive_"^table^" r t1))" in
                              Some (rule_wrapper (table,es_conds@type_conds@[s_cond;i_cond;alive_cond;wr_cond]))
              |None -> None end

          (*16*)
          |(S.RANGE_SELECT (_,v,_,_),_,S.INSERT (_,_,_),_, "RW->" )->
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let s_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              let i_cond =  extract_condition 2 (to_cap txn_name2) table stmt2 in
															let wr_cond = "(RW_Alive_"^table^" r o1 o2)" in
															let alive_cond = "(not (IsAlive_"^table^" r t1))" in
                              Some (rule_wrapper (table,es_conds@type_conds@[s_cond;i_cond;alive_cond;wr_cond]))
              |None -> None end
          (*13*)
          |(S.SELECT (_,v,_,_),_,S.DELETE (_,_,_),_, "RW->" )->
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "(not ("^to_cap txn_name1^"_isN_"^(V.name v)^" t1))" in
                              let s_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              let i_cond =  extract_condition 2 (to_cap txn_name2) table stmt2 in
															let wr_cond = "(RW_Alive_"^table^" r o1 o2)" in
															let alive_cond = "(IsAlive_"^table^" r t2)" in
                              Some (rule_wrapper (table,es_conds@type_conds@[s_cond;i_cond;alive_cond;null_cond;wr_cond]))
              |None -> None end
          (*17*)
          |(S.RANGE_SELECT (_,v,_,_),_,S.DELETE (_,_,_),_, "RW->" )->
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let s_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              let i_cond =  extract_condition 2 (to_cap txn_name2) table stmt2 in
															let wr_cond = "(RW_Alive_"^table^" r o1 o2)" in
															let alive_cond = "(IsAlive_"^table^" r t2)" in
                              Some (rule_wrapper (table,es_conds@type_conds@[s_cond;i_cond;alive_cond;wr_cond]))
              |None -> None end

					(*-------------------*)
					(*->WR*)
  		    (*21*)
 	    		|(S.INSERT (_,_,_),_, S.SELECT (_,v,_,_),_, "->WR")->
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_condition 1 (to_cap txn_name1) table stmt1 in
															let alive_cond = "(IsAlive_"^table^" r t2)" in
															let wr_cond = "(WR_Alive_"^table^" r o1 o2)" in
                              Some (rule_wrapper (table,es_conds@type_conds@[s_cond;i_cond;null_cond;alive_cond;wr_cond]))
              |None -> None end
          (*22*)
 	    		|(S.INSERT (_,_,_),_, S.RANGE_SELECT (_,v,_,_),_, "->WR")->
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_condition 1 (to_cap txn_name1) table stmt1 in
															let alive_cond = "(IsAlive_"^table^" r t2)" in
															let wr_cond = "(WR_Alive_"^table^" r o1 o2)" in
                              Some (rule_wrapper (table,es_conds@type_conds@[s_cond;i_cond;alive_cond;wr_cond]))
              |None -> None end


          |_ -> None
  
    let extract_sub_rules: T.t -> T.t -> string -> string =
      fun txn1 -> fun txn2 -> fun dir -> 
        let name1 = T.name txn1 in
        let name2 = T.name txn2 in
        List.fold_left (fun old_s -> fun curr_stmt -> 
          List.fold_left (fun old_s2 -> fun curr_stmt2 -> 
                          match  (analyze_stmts name1 name2 curr_stmt curr_stmt2 dir) with       
                            |Some all_conds -> "(or "^old_s2^(all_conds)^")"
                            |None -> old_s2)
            old_s (T.stmts txn2)) "false" (T.stmts txn1)
   
end
















(*------------------------------------------- RW-> --------------------------------------------------*)
module RW = 
struct
    let extract_rules: T.t -> T.t -> string =
       let open Wrappers in  
       let open Analyze in 
       fun txn1 -> fun txn2 ->
          let name1 = T.name txn1 in
          let name2 = T.name txn2 in
          let all_conds =  extract_sub_rules txn1 txn2 "RW->" in
          rt_final_wrapper ("RW",name1,name2,all_conds)
end
(*------------------------------------------ WR-> ------------------------------------------------------*)
module WR_Then = 
struct
     let extract_rules: T.t -> T.t -> string =
       let open Wrappers in
       let open Analyze in 
        fun txn1 -> fun txn2 ->
          let name1 = T.name txn1 in
          let name2 = T.name txn2 in 
          let all_conds = extract_sub_rules txn1 txn2 "WR->" in 
          rt_final_wrapper ("WR",name1,name2,all_conds)
end
(*------------------------------------------ ->WR ------------------------------------------------------*)
module Then_WR = 
struct
     let extract_rules: T.t -> T.t -> string =
       let open Wrappers in
       let open Analyze in 
        fun txn1 -> fun txn2 ->
          let name1 = T.name txn1 in
          let name2 = T.name txn2 in 
          let all_conds = extract_sub_rules txn1 txn2 "->WR" in 
          tr_final_wrapper ("WR",name1,name2,all_conds)
end
(*------------------------------------------- ->WW ---------------------------------------------------*)
module Then_WW = 
struct
    let extract_rules: T.t -> T.t -> string =
        let open Wrappers in
       let open Analyze in 
        fun txn1 -> fun txn2 ->
          let name1 = T.name txn1 in
          let name2 = T.name txn2 in 
          let all_conds = extract_sub_rules txn1 txn2 "->WW" in 
          tr_final_wrapper ("WW",name1,name2,all_conds)
end
(*------------------------------------------  WW->   -------------------------------------------------*)
module WW_Then = 
struct
    let extract_rules: T.t -> T.t -> string =
        let open Wrappers in 
       let open Analyze in 
        fun txn1 -> fun txn2 ->
          let name1 = T.name txn1 in
          let name2 = T.name txn2 in 
          let all_conds = extract_sub_rules txn1 txn2 "WW->" in 
          rt_final_wrapper ("WW",name1,name2,all_conds)
end

(*----------------------------------------------------------------------------------------------------*)
let apply = print_string "applying the rules..."

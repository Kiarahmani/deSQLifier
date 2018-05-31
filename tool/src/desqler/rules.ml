open App
open Sql
open Speclang
module M = Misc
module T = Sql.Transaction
module S = Sql.Statement
module F = Fol
module V = Var.Variable
let to_cap = String.capitalize_ascii


module Utils = 
  struct
    let rec expression_to_string: int -> string -> string -> F.L.expr -> string = 
      fun t_i -> fun txn_name -> fun table_name -> 
      fun e -> match e with
        (*vars*)
        | F.L.Var (V.T{name; tp; kn=V.PARAM}) -> "("^txn_name^"_Param_"^name^" t"^(string_of_int t_i)^")"
        | F.L.Var (V.T{name; tp; kn=V.LOCAL}) -> "("^txn_name^"_Var_"^name^" t"^(string_of_int t_i)^")"
        | F.L.Var (V.T{name; tp; kn=V.FIELD}) -> "("^table_name^"_Proj_"^name^" r)"
        (*other cases: constants, etc*)
        | F.L.Cons c -> string_of_int c
        | F.L.Str s -> "\""^s^"\""
        | F.L.MINUS (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                               let rhs = expression_to_string t_i txn_name table_name e2 in  
                               "(- "^lhs^" "^rhs^")"
        | F.L.PLUS (e1,e2) ->  let lhs = expression_to_string t_i txn_name table_name e1 in
                               let rhs = expression_to_string t_i txn_name table_name e2 in  
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

    let extract_condition: int -> string -> string -> S.st -> string = 
      fun t_i -> fun txn_name -> fun table_name -> fun stmt ->
       match (F.cond @@ return_where stmt) with
        |F.L.Eq (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                           let rhs = expression_to_string t_i txn_name table_name e2 in
                           "(= "^lhs^" "^rhs^")"
        |F.L.Gt (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                           let rhs = expression_to_string t_i txn_name table_name e2 in
                           "(> "^lhs^" "^rhs^")"
        |F.L.Lt (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                           let rhs = expression_to_string t_i txn_name table_name e2 in
                           "(< "^lhs^" "^rhs^")"
        |F.L.Nq (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                           let rhs = expression_to_string t_i txn_name table_name e2 in
                           "(not (= "^lhs^" "^rhs^"))"

        |F.L.Bool b -> failwith "ERROR extract_s_condition: true/false are not accepted as the where claus"
        |_ -> failwith "rules.ml ERROR extract_s_condition: the where claus case not handled yet "
 
  
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
          |(S.DELETE (Var.Table.T{name=t_name_d},_,_), S.SELECT ((t_name_s,_,_,_),_,_,_)) -> 
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
          |(S.INSERT (Var.Table.T{name=t_name_i},_,_), S.RANGE_SELECT ((t_name_s,_,_,_),_,_,_)) -> 
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


      let extract_us_condition: string -> string -> S.st -> string -> S.st -> string -> string=
        fun op -> fun txn_name1 -> fun s_fun1 -> fun txn_name2 -> fun s_fun2 -> fun table_name -> 
          match (s_fun1,s_fun2) with
          |(S.UPDATE ((_,col_name,_,_),exp,_,_)  ,S.MAX_SELECT ((_,s_col,_,_),sv,_,_)) ->  
            "("^op^" "^(expression_to_string 1 txn_name1 table_name exp)^" ("^table_name^"_Proj_"^String.lowercase_ascii col_name^" r) )"
          |(S.UPDATE ((_,col_name,_,_),exp,_,_)  ,S.MIN_SELECT ((_,s_col,_,_),sv,_,_)) ->  
            "("^op^" "^(expression_to_string 1 txn_name1 table_name exp)^" ("^table_name^"_Proj_"^String.lowercase_ascii col_name^" r) )"
          |_-> failwith "rules.ml: ERROR extract_us_condition: Unexpected statements"
      
      let extract_i_expr: int -> string -> string -> (string * Fol.L.expr) -> string = 
      fun t_i -> fun txn_name -> fun table_name -> fun (s,exp) -> 
        let value = expression_to_string t_i txn_name table_name exp in
        "
                             (= ("^table_name^"_Proj_"^s^" r) "^value^")"

      let extract_i_condition: int -> string -> string -> S.st -> string = 
      fun t_i -> fun txn_name -> fun table_name -> fun (S.INSERT (_,Fol.Record.T{vars=c_list},_)) ->
        List.fold_left (fun old_s -> fun curr_c -> 
                        old_s^""^(extract_i_expr t_i txn_name table_name curr_c)) "" @@ c_list

    let extract_agg_condition: string -> string -> S.st -> string -> S.st -> string = 
      fun op -> fun txn_name1 -> fun s_fun1 -> 
        fun txn_name2 -> fun s_fun2 ->
        match (s_fun1,s_fun2) with 
          |((S.INSERT (_,Fol.Record.T{vars},_)),S.MAX_SELECT ((_,s_col,_,_),sv,_,_)) ->
            let rec_e = List.assoc (String.lowercase_ascii s_col) vars in
            "("^op^" ("^txn_name2^"_Var_"^(V.name sv)^" t2) "^(expression_to_string 1 txn_name1 "" rec_e)^")"
          |((S.INSERT (_,Fol.Record.T{vars},_)),S.MIN_SELECT ((_,s_col,_,_),sv,_,_)) ->
            let rec_e = List.assoc (String.lowercase_ascii s_col) vars in
            "("^op^" ("^txn_name2^"_Var_"^(V.name sv)^" t2) "^(expression_to_string 1 txn_name1 "" rec_e)^")"
          |(S.DELETE _ , S.MIN_SELECT ((t_name,s_col,_,_),sv,_,_)) -> 
            "("^op^" ("^t_name^"_Proj_"^(String.lowercase_ascii s_col)^" r)("^txn_name2^"_Var_"^V.name sv^" t2))"
          |(S.DELETE _ , S.MAX_SELECT ((t_name,s_col,_,_),sv,_,_)) -> 
            "("^op^" ("^t_name^"_Proj_"^(String.lowercase_ascii s_col)^" r)("^txn_name2^"_Var_"^V.name sv^" t2))"
          |_ -> failwith "rules.ml: extract_agg_condition: unexpected case"
    end

module Wrappers = 
struct 
    (*RW->*)
    let rwt_final_wrapper (txn1_name,txn2_name,all_conds)=
      "\n\n(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^"))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        "^all_conds^" ))))"

    let rwt_rule_wrapper_dmns (table_name,s_cond,d_conds,null_cond,min_cond) = "
                        (exists ((r "^table_name^"))
                        (and (IsAlive_"^table_name^" r t1)
                             (IsAlive_"^table_name^" r t2)
                             "^null_cond^s_cond^"
                             "^d_conds^"
                             (RW_Alive_"^table_name^" r t1 t2)"^min_cond^"))"

    let rwt_rule_wrapper_us (table_name,rw_s_cond,rw_u_cond) =
                "
                        (exists ((r "^(to_cap table_name)^"))
                        (and (IsAlive_"^table_name^" r t2)
                             (RW_"^table_name^" r t1 t2)
                             "^rw_s_cond^"
                             "^rw_u_cond^"))"
    
    let rwt_rule_wrapper_is (table_name,wr_s_cond,wr_i_conds,wr_null_cond) = "
                        (exists ((r "^table_name^"))
                        (and (not (IsAlive_"^table_name^" r t2))
                             "^wr_null_cond^"
                             "^wr_s_cond^"
                             (RW_Alive_"^table_name^" r t1 t2)"^wr_i_conds^" ))"
    
    let rwt_rule_wrapper_ds (table_name,s_cond,d_conds,null_cond) = "
                        (exists ((r "^table_name^"))
                        (and (IsAlive_"^table_name^" r t1)
                             "^null_cond^"
                             "^s_cond^"
                             "^d_conds^"
                             (RW_Alive_"^table_name^" r t1 t2)))"
    
    let rwt_rule_wrapper_ismx (table_name,wr_s_cond,wr_i_conds,wr_null_cond,max_cond) = "
                        (exists ((r "^table_name^"))
                        (and (not (IsAlive_"^table_name^" r t2))
                             "^wr_null_cond^wr_s_cond^wr_i_conds^"
                             "^max_cond^"))"

   (*WR->*)
   let wrt_rule_wrapper_ds (table_name,s_cond,d_conds,null_cond) = "
                        (exists ((r "^table_name^"))
                        (and (IsAlive_"^table_name^" r t1)
                             (not (IsAlive_"^table_name^" r t2))
                             "^null_cond^"
                             "^s_cond^"
                             "^d_conds^"
                             (WR_Alive_"^table_name^" r t1 t2)))"

   let wrt_rule_wrapper_dmns (table_name,s_cond,d_conds,null_cond,min_cond) = "
                        (exists ((r "^table_name^"))
                        (and (IsAlive_"^table_name^" r t1)
                             (not (IsAlive_"^table_name^" r t2))
                             "^null_cond^s_cond^"
                             "^d_conds^"
                             (WR_Alive_"^table_name^" r t1 t2)"^min_cond^"))"

    let wrt_final_wrapper (txn1_name,txn2_name,all_conds)=
      "\n\n(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^"))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        "^all_conds^" ))))"
    let wrt_rule_wrapper_su (table_name,wr_s_cond,wr_u_cond,wr_null_cond) =
                "
                        (exists ((r "^(to_cap table_name)^"))
                        (and (IsAlive_"^table_name^" r t1)
                             (WR_"^table_name^" r t1 t2)
                             "^wr_null_cond^"
                             "^wr_s_cond^"
                             "^wr_u_cond^"))"
    
    let wrt_rule_wrapper_smxu (table_name,wr_s_cond,wr_u_cond,wr_null_cond,max_cond) =
                "
                        (exists ((r "^(to_cap table_name)^"))
                        (and (IsAlive_"^table_name^" r t1)
                             (WR_"^table_name^" r t1 t2)
                             "^wr_null_cond^"
                             "^wr_s_cond^"
                             "^wr_u_cond^"
                             "^max_cond^"))"

    let rwt_rule_wrapper_smxu (table_name,wr_s_cond,wr_u_cond,wr_null_cond,max_cond) =
                "
                        (exists ((r "^(to_cap table_name)^"))
                        (and (IsAlive_"^table_name^" r t1)
                             (RW_"^table_name^" r t1 t2)
                             "^wr_null_cond^"
                             "^wr_s_cond^"
                             "^wr_u_cond^"
                             "^max_cond^"))"


    let wrt_rule_wrapper_is (table_name,wr_s_cond,wr_i_conds,wr_null_cond) = "
                        (exists ((r "^table_name^"))
                        (and (IsAlive_"^table_name^" r t2)
                             "^wr_null_cond^"
                             "^wr_s_cond^"
                             (WR_Alive_"^table_name^" r t1 t2)"^wr_i_conds^" ))"
    let wrt_rule_wrapper_ismx (table_name,wr_s_cond,wr_i_conds,wr_null_cond,max_cond) = "
                        (exists ((r "^table_name^"))
                        (and (IsAlive_"^table_name^" r t2)
                             "^wr_null_cond^wr_s_cond^wr_i_conds^"
                             "^max_cond^"))"

    (*->WR*)
    let twr_final_wrapper (txn1_name,txn2_name,all_conds)=
      "\n\n(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^") (not (= t1 t2)))
                    (=> "^all_conds^"
                        (WR t1 t2) ))))"

    let twr_rule_wrapper_is (table_name,wr_s_cond,wr_i_conds,wr_null_cond) = "
                        (exists ((r "^table_name^"))
                        (and (IsAlive_"^table_name^" r t2)
                             "^wr_null_cond^"
                             "^wr_s_cond^"
                             (WR_Alive_"^table_name^" r t1 t2)"^wr_i_conds^" ))"

    (*->WW*)
    let tww_final_wrapper (txn1_name,txn2_name,all_conds)=
      "\n\n(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^") (not (= t1 t2)))
                    (=> "^all_conds^"
                        (or (WW t1 t2) (WW t2 t1)) ))))"
    let tww_rule_wrapper (table_name,ww_s_cond,ww_u_cond) =
                "
                        (exists ((r "^(to_cap table_name)^"))
                        (and (IsAlive_"^table_name^" r t1)
                             (IsAlive_"^table_name^" r t2)
                             "^ww_s_cond^"
                             "^ww_u_cond^"))"
    
    (*WW->*)
    let wwt_final_wrapper (txn1_name,txn2_name,all_conds)=
      "\n\n(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^") (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        "^all_conds^"))))"
    let wwt_rule_wrapper (table_name,ww_s_cond,ww_u_cond) =
                "
                        (exists ((r "^(to_cap table_name)^"))
                        (and (IsAlive_"^table_name^" r t1)
                             (IsAlive_"^table_name^" r t2)
                             "^ww_s_cond^"
                             "^ww_u_cond^"))"

end 

(*analyze statements according to the rules. If applicable, return the wrapped cnoditions as strings*)
module Analyze = 
struct
     (*WW->*)
     let analyze_stmts: string ->  string -> S.st -> S.st -> string -> string option = 
      fun txn_name1 -> fun txn_name2 -> fun stmt1 -> fun stmt2 -> fun dir -> 
        (*t1 and t2 are the same if the txns are the same*)
        let open Utils in 
        let open Wrappers in
        match (stmt1,stmt2,dir) with
          
          (*-------------------*)
          (*WW*)
          (*1*)
          |(S.UPDATE _,S.UPDATE _,"->WW") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let u1_cond = extract_condition 1  (to_cap txn_name1) table stmt1 in
                             let u2_cond  = extract_condition 2 (to_cap txn_name2) table stmt2 in
                              Some (tww_rule_wrapper 
                                        (table, u1_cond , u2_cond))
              |None -> None end
          
          (*2*)
          |(S.UPDATE _,S.UPDATE _,"WW->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let u1_cond = extract_condition 1  (to_cap txn_name1) table stmt1 in
                             let u2_cond  = extract_condition 2 (to_cap txn_name2) table stmt2 in
                              Some (wwt_rule_wrapper 
                                        (table, u1_cond , u2_cond))
              |None -> None end

          (*-------------------*)
          (*WR->*)
          (*3*)
          |(S.UPDATE _ , S.SELECT(_,v,_,_),"WR->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 2  (to_cap txn_name2) table stmt2 in
                             let u_cond  = extract_condition 1 (to_cap txn_name1) table stmt1 in
                             let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              Some (wrt_rule_wrapper_su
                                        (table, s_cond , u_cond, null_cond))
              |None -> None end 
          (*4*)
          |(S.INSERT (_,_,_) , S.SELECT (_,v,_,_), "WR->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              Some (wrt_rule_wrapper_is (table,s_cond,i_cond,null_cond))
              |None -> None end
          (*5*)
          |(S.DELETE (_,_,_) , S.SELECT (_,v,_,_), "WR->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "("^to_cap txn_name2^"_isN_"^(V.name v)^" t2)" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let d_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              Some (wrt_rule_wrapper_ds (table,s_cond,d_cond,null_cond))
              |None -> None end
           
          (*6*)
          |(S.UPDATE _ , S.RANGE_SELECT(_,v,_,_),"WR->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 2  (to_cap txn_name2) table stmt2 in
                             let u_cond  = extract_condition 1 (to_cap txn_name1) table stmt1 in
                             let null_cond = "("^to_cap txn_name2^"_isI_"^(V.name v)^" t2 r)" in
                              Some (wrt_rule_wrapper_su
                                        (table, s_cond , u_cond, null_cond))
              |None -> None end
          (*7*)
          |(S.INSERT (_,_,_) , S.RANGE_SELECT (_,v,_,_), "WR->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let  null_cond = "("^to_cap txn_name2^"_isI_"^(V.name v)^" t2 r)" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              Some (wrt_rule_wrapper_is (table,s_cond,i_cond,null_cond))
              |None -> None end
          (*8*)
          |(S.INSERT (_,_,_) , S.MAX_SELECT (_,v,_,_), "WR->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let  null_cond = "" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              let max_cond = extract_agg_condition "<=" (to_cap txn_name1) stmt1 (to_cap txn_name2) stmt2 in
                              Some (wrt_rule_wrapper_ismx (table,s_cond,i_cond,null_cond,max_cond))
              |None -> None end
          
          (*25*)
          |(S.UPDATE _ , S.MAX_SELECT(_,v,_,_),"WR->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 2  (to_cap txn_name2) table stmt2 in
                             let u_cond  = extract_condition 1 (to_cap txn_name1) table stmt1 in
                             let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                             let max_cond = extract_us_condition "=" (to_cap txn_name1) stmt1 (to_cap txn_name2) stmt2 table in
                              Some (wrt_rule_wrapper_smxu
                                        (table, s_cond , u_cond, null_cond,max_cond))
              |None -> None end 
          
          (*27*)
          |(S.UPDATE _ , S.MIN_SELECT(_,v,_,_),"WR->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 2  (to_cap txn_name2) table stmt2 in
                             let u_cond  = extract_condition 1 (to_cap txn_name1) table stmt1 in
                             let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                             let max_cond = extract_us_condition "=" (to_cap txn_name1) stmt1 (to_cap txn_name2) stmt2 table in
                              Some (wrt_rule_wrapper_smxu
                                        (table, s_cond , u_cond, null_cond,max_cond))
              |None -> None end 

          
          (*9*)
          |(S.INSERT (_,_,_) , S.MIN_SELECT (_,v,_,_), "WR->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let  null_cond = "" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              let max_cond = extract_agg_condition ">=" (to_cap txn_name1) stmt1 (to_cap txn_name2) stmt2 in
                              Some (wrt_rule_wrapper_ismx (table,s_cond,i_cond,null_cond,max_cond))
              |None -> None end
          (*10*)
          |(S.DELETE (_,_,_) , S.RANGE_SELECT (_,v,_,_), "WR->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "(not ("^to_cap txn_name2^"_isI_"^(V.name v)^" t2 r))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let d_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              Some (wrt_rule_wrapper_ds (table,s_cond,d_cond,null_cond))
              |None -> None end
          (*11*)
          |(S.DELETE (_,_,_) , S.MIN_SELECT (_,v,_,_), "WR->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "" in
                              let min_cond = "" in 
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let d_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              Some (wrt_rule_wrapper_dmns (table,s_cond,d_cond,null_cond,min_cond))
              |None -> None end

          (*29*)
          |(S.DELETE (_,_,_) , S.MAX_SELECT (_,v,_,_), "WR->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "" in
                              let max_cond = "" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let d_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              Some (wrt_rule_wrapper_dmns (table,s_cond,d_cond,null_cond,max_cond))
              |None -> None end

          (*-------------------*)
          (*RW->*)
          (*12*)
          |(S.SELECT _,S.UPDATE _, "RW->") -> 
            begin
              match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 1  (to_cap txn_name1) table stmt1 in
                             let u_cond  = extract_condition 2 (to_cap txn_name2) table stmt2 in
                              Some (rwt_rule_wrapper_us
                                        (table, s_cond , u_cond))
              |None -> None end
          (*13*)
          |(S.DELETE (_,_,_) , S.SELECT (_,v,_,_), "RW->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let d_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              Some (rwt_rule_wrapper_ds (table,s_cond,d_cond,null_cond))
              |None -> None end
          (*14*)
          |(S.INSERT (_,_,_) , S.SELECT (_,v,_,_), "RW->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "("^to_cap txn_name2^"_isN_"^(V.name v)^" t2)" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              Some (rwt_rule_wrapper_is (table,s_cond,i_cond,null_cond))
              |None -> None end
          
          (*15*)
          |(S.RANGE_SELECT _,S.UPDATE _, "RW->") -> 
            begin
              match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 1  (to_cap txn_name1) table stmt1 in
                             let u_cond  = extract_condition 2 (to_cap txn_name2) table stmt2 in
                              Some (rwt_rule_wrapper_us
                                        (table, s_cond , u_cond))
              |None -> None end
          (*16*)
          |(S.INSERT (_,_,_) , S.RANGE_SELECT (_,v,_,_), "RW->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "(not ("^to_cap txn_name2^"_isI_"^(V.name v)^" t2 r))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              Some (rwt_rule_wrapper_is (table,s_cond,i_cond,null_cond))
              |None -> None end
          (*17*)
          |(S.DELETE (_,_,_) , S.RANGE_SELECT (_,v,_,_), "RW->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "("^to_cap txn_name2^"_isI_"^(V.name v)^" t2 r)" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let d_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              Some (rwt_rule_wrapper_ds (table,s_cond,d_cond,null_cond))
              |None -> None end
          (*18*)
          |(S.INSERT (_,_,_) , S.MAX_SELECT (_,v,_,_), "RW->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let  null_cond = "" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              let max_cond = extract_agg_condition ">" (to_cap txn_name1) stmt1 (to_cap txn_name2) stmt2 in
                              Some (rwt_rule_wrapper_ismx (table,s_cond,i_cond,null_cond,max_cond))
              |None -> None end
          (*19*)
          |(S.INSERT (_,_,_) , S.MIN_SELECT (_,v,_,_), "RW->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let  null_cond = "" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              let max_cond = extract_agg_condition ">" (to_cap txn_name1) stmt1 (to_cap txn_name2) stmt2 in
                              Some (rwt_rule_wrapper_ismx (table,s_cond,i_cond,null_cond,max_cond))
              |None -> None end
          (*20*)
          |(S.DELETE _, S.MIN_SELECT _, "RW->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "" in
                              let min_cond = "" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let d_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              Some (rwt_rule_wrapper_dmns (table,s_cond,d_cond,null_cond,min_cond))
              |None -> None end

          (*26*)
          |(S.UPDATE _ , S.MAX_SELECT(_,v,_,_),"RW->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 2  (to_cap txn_name2) table stmt2 in
                             let u_cond  = extract_condition 1 (to_cap txn_name1) table stmt1 in
                             let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                             let max_cond = extract_us_condition ">" (to_cap txn_name1) stmt1 (to_cap txn_name2) stmt2 table in
                              Some (rwt_rule_wrapper_smxu
                                        (table, s_cond , u_cond, null_cond,max_cond))
              |None -> None end 
          (*28*)
          |(S.UPDATE _ , S.MIN_SELECT(_,v,_,_),"RW->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 2  (to_cap txn_name2) table stmt2 in
                             let u_cond  = extract_condition 1 (to_cap txn_name1) table stmt1 in
                             let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                             let max_cond = extract_us_condition "<" (to_cap txn_name1) stmt1 (to_cap txn_name2) stmt2 table in
                              Some (rwt_rule_wrapper_smxu
                                        (table, s_cond , u_cond, null_cond,max_cond))
              |None -> None end 
          (*30*)
          |(S.DELETE (_,_,_) , S.MAX_SELECT (_,v,_,_), "RW->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "" in
                              let max_cond = "" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let d_cond =  extract_condition 1  (to_cap txn_name1) table stmt1 in
                              Some (rwt_rule_wrapper_dmns (table,s_cond,d_cond,null_cond,max_cond))
              |None -> None end



          (*-------------------*)
          (*->WR*)
          (*21*)
          |(S.INSERT (_,_,_) , S.SELECT (_,v,_,_), "->WR")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              Some (twr_rule_wrapper_is (table,s_cond,i_cond,null_cond))
              |None -> None end
          (*22*)
          |(S.INSERT (_,_,_) , S.RANGE_SELECT (_,v,_,_), "->WR")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "("^to_cap txn_name2^"_isI_"^(V.name v)^" t2 r)" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              Some (twr_rule_wrapper_is (table,s_cond,i_cond,null_cond))
              |None -> None end
          (*23*)
          |(S.INSERT (_,_,_) , S.MIN_SELECT (_,v,_,_), "->WR")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              Some (twr_rule_wrapper_is (table,s_cond,i_cond,null_cond))
              |None -> None end
          
          (*24*)
          |(S.INSERT (_,_,_) , S.MAX_SELECT (_,v,_,_), "->WR")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->  let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              Some (twr_rule_wrapper_is (table,s_cond,i_cond,null_cond))
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

module Rule = 
struct
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
          rwt_final_wrapper (name1,name2,all_conds)
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
          wrt_final_wrapper (name1,name2,all_conds)
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
          twr_final_wrapper (name1,name2,all_conds)
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
          tww_final_wrapper (name1,name2,all_conds)
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
          wwt_final_wrapper (name1,name2,all_conds)
end

(*----------------------------------------------------------------------------------------------------*)
let apply = print_string "applying the rules..."

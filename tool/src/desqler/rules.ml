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
        |S.UPDATE (_,_,wh,_) -> wh

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
        |F.L.Bool b -> failwith "ERROR extract_s_condition: true/false are not accepted as the where claus"
        |_ -> failwith "ERROR extract_s_condition: the where claus case not handled yet "
 
  
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
      
      let extract_i_expr: int -> string -> string -> (string * Fol.L.expr) -> string = 
      fun t_i -> fun txn_name -> fun table_name -> fun (s,exp) -> 
        let value = expression_to_string t_i txn_name table_name exp in
        "
                             (= ("^table_name^"_Proj_"^s^" r) "^value^")"

    let extract_i_condition: int -> string -> string -> S.st -> string = 
      fun t_i -> fun txn_name -> fun table_name -> fun (S.INSERT (_,Fol.Record.T{vars=c_list},_)) ->
        List.fold_left (fun old_s -> fun curr_c -> 
                        old_s^""^(extract_i_expr t_i txn_name table_name curr_c)) "" @@ c_list
    
    end


module Wrappers = 
struct 
    (*RW->*)
    let rwt_final_wrapper (txn1_name,txn2_name,all_conds)=
      "\n\n(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^"))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        "^all_conds^" ))))"
    
    let rwt_rule_wrapper_is (table_name,rw_s_cond,rw_u_cond) =
                "
                        (exists ((r "^(to_cap table_name)^"))
                        (and (IsAlive_"^table_name^" r t2)
                             (RW_"^table_name^" r t1 t2)
                             "^rw_s_cond^"
                             "^rw_u_cond^"))"


    (*WR->*)
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
    let wrt_rule_wrapper_is (table_name,wr_s_cond,wr_i_conds,wr_null_cond) = "
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


module Analyze = 
struct
     (*WW->*)
     let analyze_stmts: string ->  string -> S.st -> S.st -> string -> string option = 
      fun txn_name1 -> fun txn_name2 -> fun stmt1 -> fun stmt2 -> fun dir -> 
        (*t1 and t2 are the same if the txns are the same*)
        let open Utils in 
        let open Wrappers in
        match (stmt1,stmt2,dir) with
          |(S.UPDATE _,S.UPDATE _,"->WW") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let u1_cond = extract_condition 1  (to_cap txn_name1) table stmt1 in
                             let u2_cond  = extract_condition 2 (to_cap txn_name2) table stmt2 in
                              Some (tww_rule_wrapper 
                                        (table, u1_cond , u2_cond))
              |None -> None end
          
          |(S.UPDATE _,S.UPDATE _,"WW->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let u1_cond = extract_condition 1  (to_cap txn_name1) table stmt1 in
                             let u2_cond  = extract_condition 2 (to_cap txn_name2) table stmt2 in
                              Some (wwt_rule_wrapper 
                                        (table, u1_cond , u2_cond))
              |None -> None end

          |(S.UPDATE _ , S.SELECT(_,v,_,_),"WR->") -> 
            begin match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 2  (to_cap txn_name2) table stmt2 in
                             let u_cond  = extract_condition 1 (to_cap txn_name1) table stmt1 in
                             let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              Some (wrt_rule_wrapper_su
                                        (table, s_cond , u_cond, null_cond))
              |None -> None end 
          
          |(S.INSERT (_,_,_) , S.SELECT (_,v,_,_), "WR->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->
                              let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              Some (wrt_rule_wrapper_is (table,s_cond,i_cond,null_cond))
              |None -> None end
 
          |(S.INSERT (_,_,_) , S.SELECT (_,v,_,_), "WR->")-> 
            begin match (accessed_common_table stmt1 stmt2) with
              |Some table ->
                              let null_cond = "(not ("^to_cap txn_name2^"_isN_"^(V.name v)^" t2))" in
                              let s_cond =  extract_condition 2  (to_cap txn_name2) table stmt2 in
                              let i_cond = extract_i_condition 1 (to_cap txn_name1) table stmt1 in
                              Some (wrt_rule_wrapper_is (table,s_cond,i_cond,null_cond))
              |None -> None end
 



          |(S.SELECT _,S.UPDATE _, "RW->") -> 
            begin
              match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_condition 1  (to_cap txn_name1) table stmt1 in
                             let u_cond  = extract_condition 2 (to_cap txn_name2) table stmt2 in
                              Some (rwt_rule_wrapper_is
                                        (table, s_cond , u_cond))
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




(*-------------------------------------------RW THEN--------------------------------------------------*)
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
(*------------------------------------------ WR ------------------------------------------------------*)
module WR = 
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

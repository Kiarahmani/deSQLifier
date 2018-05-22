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
        | F.L.MINUS (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                               let rhs = expression_to_string t_i txn_name table_name e2 in  
                               "(- "^lhs^" "^rhs^")"
        | F.L.PLUS (e1,e2) ->  let lhs = expression_to_string t_i txn_name table_name e1 in
                               let rhs = expression_to_string t_i txn_name table_name e2 in  
                               "(+ "^lhs^" "^rhs^")"
        | _ -> failwith "ERROR expression_to_string: expression case not handled yet"
  end


module RW = 
  struct 
    
    let rw_final_wrapper (txn1_name,txn2_name,all_conds)=
      "\n\n(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^"))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        "^all_conds^" ))))"



    let rw_rule_wrapper (table_name,rw_s_cond,rw_u_cond) =
                "
                        (exists ((r "^(to_cap table_name)^"))
                        (and (RW_"^table_name^" r t1 t2)
                             "^rw_s_cond^"
                             "^rw_u_cond^"))"

(*auxiliary function to find the common accessed table*)
    let accessed_common_table : S.st -> S.st -> string option = 
      fun stmt1 -> fun stmt2 ->
        match (stmt1,stmt2) with
          |(S.SELECT ((t_name_s,c_name_s,_,_),_,_,_) , S.UPDATE ((t_name_u,c_name_u,_,_),_,_,_)) -> 
            if t_name_s = t_name_u && c_name_s = c_name_u
            then Some t_name_s
            else None
          |_ -> failwith "ERROR accessed_common_table: sql operation case not handled yet"

    
(*the select case in RW*)
    let extract_s_condition: int -> string -> string -> S.st -> string = 
      fun t_i -> fun txn_name -> fun table_name -> fun (S.SELECT (_,_,(wh),_)) ->
      let open Utils in 
      let res = 
       match (F.cond wh) with
        |F.L.Eq (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                           let rhs = expression_to_string t_i txn_name table_name e2 in
                           "(= "^lhs^" "^rhs^")"
        |F.L.Bool b -> failwith "ERROR extract_s_condition: true/false are not accepted as the where claus"
        |_ -> failwith "ERROR extract_s_condition: the where claus case not handled yet "
       in res  
      
(*The update statement in RW*)
    let extract_u_condition:  int -> string -> string -> S.st -> string = 
      fun t_i -> fun txn_name -> fun table_name -> fun (S.UPDATE (_,_,wh,_)) -> 
 			let open Utils in 
      let res = 
       match (F.cond wh) with
        |F.L.Eq (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                           let rhs = expression_to_string t_i txn_name table_name e2 in
                           "(= "^lhs^" "^rhs^")"
        |F.L.Bool b -> failwith "ERROR extract_u_condition: true/false are not accepted as the where claus"
        |_ -> failwith "ERROR extract_u_condition: the where claus case not handled yet "
       in res  


(*check for applicability of RW and perform the anlysis*)
    let analyze_stmts: string ->  string -> S.st -> S.st -> string option = 
      fun txn_name1 -> fun txn_name2 -> fun stmt1 -> fun stmt2 -> 
        (*t1 and t2 are the same if the txns are the same*)
        match (stmt1,stmt2) with
          |(S.SELECT _,S.UPDATE _) -> 
            begin
              match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_s_condition 1  (to_cap txn_name1) table stmt1 in
                             let u_cond  = extract_u_condition 2 (to_cap txn_name2) table stmt2 in
                              Some (rw_rule_wrapper 
                                        (table, s_cond , u_cond))
              |None -> None
            end
          |_ -> None


    let extract_sub_rules: T.t -> T.t -> string =
      fun txn1 -> fun txn2 -> 
        let name1 = T.name txn1 in
        let name2 = T.name txn2 in
        List.fold_left (fun old_s -> fun curr_stmt -> 
          List.fold_left (fun old_s2 -> fun curr_stmt2 -> 
                          match  (analyze_stmts name1 name2 curr_stmt curr_stmt2) with       
                            |Some all_conds -> "(or "^old_s2^(all_conds)^")"
                            |None -> old_s2)
            old_s (T.stmts txn2)) "false" (T.stmts txn1)

     let extract_rules: T.t -> T.t -> string =
        fun txn1 -> fun txn2 ->
          let name1 = T.name txn1 in
          let name2 = T.name txn2 in
          let all_conds =  extract_sub_rules txn1 txn2 in
          rw_final_wrapper (name1,name2,all_conds)
  end





(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*------------------------------------------ WR ------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)

module WR = 
struct
 
    let wr_final_wrapper (txn1_name,txn2_name,all_conds)=
      "\n\n(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^"))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        "^all_conds^" ))))"



    let wr_rule_wrapper (table_name,wr_s_cond,wr_u_cond,wr_null_cond) =
                "
                        (exists ((r "^(to_cap table_name)^"))
                        (and (WR_"^table_name^" r t1 t2)
                             "^wr_null_cond^"
                             "^wr_s_cond^"
                             "^wr_u_cond^"))"

(*auxiliary function to find the common accessed table*)
    let accessed_common_table : S.st -> S.st -> string option = 
      fun stmt1 -> fun stmt2 ->
        match (stmt1,stmt2) with
          |(S.SELECT ((t_name_s,c_name_s,_,_),_,_,_) , S.UPDATE ((t_name_u,c_name_u,_,_),_,_,_)) -> 
            if t_name_s = t_name_u && c_name_s = c_name_u
            then Some t_name_s
            else None
          |_ -> failwith "ERROR accessed_common_table: sql operation case not handled yet"




(*the select case in WR*)
    let extract_s_condition: int -> string -> string -> S.st -> string = 
      fun t_i -> fun txn_name -> fun table_name -> fun (S.SELECT (_,_,(wh),_)) ->
      let open Utils in 
      let res = 
       match (F.cond wh) with
        |F.L.Eq (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                           let rhs = expression_to_string t_i txn_name table_name e2 in
                           "(= "^lhs^" "^rhs^")"
        |F.L.Bool b -> failwith "ERROR extract_s_condition: true/false are not accepted as the where claus"
        |_ -> failwith "ERROR extract_s_condition: the where claus case not handled yet "
       in res  
      
(*The update statement in WR*)
    let extract_u_condition:  int -> string -> string -> S.st -> string = 
      fun t_i -> fun txn_name -> fun table_name -> fun (S.UPDATE (_,_,wh,_)) -> 
 			let open Utils in 
      let res = 
       match (F.cond wh) with
        |F.L.Eq (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                           let rhs = expression_to_string t_i txn_name table_name e2 in
                           "(= "^lhs^" "^rhs^")"
        |F.L.Bool b -> failwith "ERROR extract_u_condition: true/false are not accepted as the where claus"
        |_ -> failwith "ERROR extract_u_condition: the where claus case not handled yet "
       in res  



(*check for applicability of WR and perform the anlysis: SELECT/UPDATE is done so far*)
    let analyze_stmts: string ->  string -> S.st -> S.st -> string option = 
      fun txn_name1 -> fun txn_name2 -> fun stmt1 -> fun stmt2 -> 
        (*t1 and t2 are the same if the txns are the same*)
        match (stmt1,stmt2) with
          |(S.SELECT(_,v,_,_),S.UPDATE _) -> 
            begin
              match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let s_cond = extract_s_condition 2  (to_cap txn_name1) table stmt1 in
                             let u_cond  = extract_u_condition 1 (to_cap txn_name2) table stmt2 in
                             let null_cond = "(not ("^to_cap txn_name1^"_isN_"^(V.name v)^" t2))" in
                              Some (wr_rule_wrapper 
                                        (table, s_cond , u_cond, null_cond))
              |None -> None
            end
          |_ -> None

    let extract_sub_rules: T.t -> T.t -> string =
      fun txn1 -> fun txn2 -> 
        let name1 = T.name txn1 in
        let name2 = T.name txn2 in
        List.fold_left (fun old_s -> fun curr_stmt -> 
          List.fold_left (fun old_s2 -> fun curr_stmt2 -> 
                          match  (analyze_stmts name1 name2 curr_stmt curr_stmt2) with       
                            |Some all_conds -> "(or "^old_s2^(all_conds)^")"
                            |None -> old_s2)
            old_s (T.stmts txn2)) "false" (T.stmts txn1)



     let extract_rules: T.t -> T.t -> string =
        fun txn1 -> fun txn2 ->
          let name1 = T.name txn1 in
          let name2 = T.name txn2 in 
          let all_conds = extract_sub_rules txn1 txn2 in 
          wr_final_wrapper (name1,name2,all_conds)
end





(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)


module Then_WW = 
struct

    let ww_final_wrapper (txn1_name,txn2_name,all_conds)=
      "\n\n(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^") (not (= t1 t2)))
                    (=> "^all_conds^"
                        (or (WW t1 t2) (WW t2 t1)) ))))"



    let ww_rule_wrapper (table_name,ww_s_cond,ww_u_cond) =
                "
                        (exists ((r "^(to_cap table_name)^"))
                        (and "^ww_s_cond^"
                             "^ww_u_cond^"))"

(*auxiliary function to find the common accessed table*)
    let accessed_common_table : S.st -> S.st -> string option = 
      fun stmt1 -> fun stmt2 ->
        match (stmt1,stmt2) with
          |( S.UPDATE ((t_name_u1,c_name_u1,_,_),_,_,_) , S.UPDATE ((t_name_u2,c_name_u2,_,_),_,_,_) ) -> 
            if t_name_u1 = t_name_u2 && c_name_u1 = c_name_u2
            then Some t_name_u1
            else None
          |_ -> failwith "ERROR accessed_common_table: sql operation case not handled yet"


(*The update statement in WR*)
    let extract_u_condition:  int -> string -> string -> S.st -> string = 
      fun t_i -> fun txn_name -> fun table_name -> fun (S.UPDATE (_,_,wh,_)) -> 
 			let open Utils in 
      let res = 
       match (F.cond wh) with
        |F.L.Eq (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                           let rhs = expression_to_string t_i txn_name table_name e2 in
                           "(= "^lhs^" "^rhs^")"
        |F.L.Bool b -> failwith "ERROR extract_u_condition: true/false are not accepted as the where claus"
        |_ -> failwith "ERROR extract_u_condition: the where claus case not handled yet "
       in res  


(*check for applicability of WR and perform the anlysis: SELECT/UPDATE is done so far*)
    let analyze_stmts: string ->  string -> S.st -> S.st -> string option = 
      fun txn_name1 -> fun txn_name2 -> fun stmt1 -> fun stmt2 -> 
        (*t1 and t2 are the same if the txns are the same*)
        match (stmt1,stmt2) with
          |(S.UPDATE _,S.UPDATE _) -> 
            begin
              match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let u1_cond = extract_u_condition 1  (to_cap txn_name1) table stmt1 in
                             let u2_cond  = extract_u_condition 2 (to_cap txn_name2) table stmt2 in
                              Some (ww_rule_wrapper 
                                        (table, u1_cond , u2_cond))
              |None -> None
            end
          |_ -> None



    let extract_sub_rules: T.t -> T.t -> string =
      fun txn1 -> fun txn2 -> 
        let name1 = T.name txn1 in
        let name2 = T.name txn2 in
        List.fold_left (fun old_s -> fun curr_stmt -> 
          List.fold_left (fun old_s2 -> fun curr_stmt2 -> 
                          match  (analyze_stmts name1 name2 curr_stmt curr_stmt2) with       
                            |Some all_conds -> "(or "^old_s2^(all_conds)^")"
                            |None -> old_s2)
            old_s (T.stmts txn2)) "false" (T.stmts txn1)



    let extract_rules: T.t -> T.t -> string =
        fun txn1 -> fun txn2 ->
          let name1 = T.name txn1 in
          let name2 = T.name txn2 in 
          let all_conds = extract_sub_rules txn1 txn2 in 
          ww_final_wrapper (name1,name2,all_conds)
end



(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*------------------------------------------ WW then -------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)

module WW_Then = 
struct

    let ww_final_wrapper (txn1_name,txn2_name,all_conds)=
      "\n\n(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) "^(to_cap txn1_name)^") (= (type t2) "^(to_cap txn2_name)^") (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        "^all_conds^"))))"



    let ww_rule_wrapper (table_name,ww_s_cond,ww_u_cond) =
                "
                        (exists ((r "^(to_cap table_name)^"))
                        (and "^ww_s_cond^"
                             "^ww_u_cond^"))"

(*auxiliary function to find the common accessed table*)
    let accessed_common_table : S.st -> S.st -> string option = 
      fun stmt1 -> fun stmt2 ->
        match (stmt1,stmt2) with
          |( S.UPDATE ((t_name_u1,c_name_u1,_,_),_,_,_) , S.UPDATE ((t_name_u2,c_name_u2,_,_),_,_,_) ) -> 
            if t_name_u1 = t_name_u2 && c_name_u1 = c_name_u2
            then Some t_name_u1
            else None
          |_ -> failwith "ERROR accessed_common_table: sql operation case not handled yet"


(*The update statement in WR*)
    let extract_u_condition:  int -> string -> string -> S.st -> string = 
      fun t_i -> fun txn_name -> fun table_name -> fun (S.UPDATE (_,_,wh,_)) -> 
 			let open Utils in 
      let res = 
       match (F.cond wh) with
        |F.L.Eq (e1,e2) -> let lhs = expression_to_string t_i txn_name table_name e1 in
                           let rhs = expression_to_string t_i txn_name table_name e2 in
                           "(= "^lhs^" "^rhs^")"
        |F.L.Bool b -> failwith "ERROR extract_u_condition: true/false are not accepted as the where claus"
        |_ -> failwith "ERROR extract_u_condition: the where claus case not handled yet "
       in res  


(*check for applicability of WR and perform the anlysis: SELECT/UPDATE is done so far*)
    let analyze_stmts: string ->  string -> S.st -> S.st -> string option = 
      fun txn_name1 -> fun txn_name2 -> fun stmt1 -> fun stmt2 -> 
        (*t1 and t2 are the same if the txns are the same*)
        match (stmt1,stmt2) with
          |(S.UPDATE _,S.UPDATE _) -> 
            begin
              match (accessed_common_table stmt1 stmt2)  with 
              |Some table -> let u1_cond = extract_u_condition 1  (to_cap txn_name1) table stmt1 in
                             let u2_cond  = extract_u_condition 2 (to_cap txn_name2) table stmt2 in
                              Some (ww_rule_wrapper 
                                        (table, u1_cond , u2_cond))
              |None -> None
            end
          |_ -> None



    let extract_sub_rules: T.t -> T.t -> string =
      fun txn1 -> fun txn2 -> 
        let name1 = T.name txn1 in
        let name2 = T.name txn2 in
        List.fold_left (fun old_s -> fun curr_stmt -> 
          List.fold_left (fun old_s2 -> fun curr_stmt2 -> 
                          match  (analyze_stmts name1 name2 curr_stmt curr_stmt2) with       
                            |Some all_conds -> "(or "^old_s2^(all_conds)^")"
                            |None -> old_s2)
            old_s (T.stmts txn2)) "false" (T.stmts txn1)



    let extract_rules: T.t -> T.t -> string =
        fun txn1 -> fun txn2 ->
          let name1 = T.name txn1 in
          let name2 = T.name txn2 in 
          let all_conds = extract_sub_rules txn1 txn2 in 
          ww_final_wrapper (name1,name2,all_conds)
end








(*----------------------------------------------------------------------------------------------------*)
  type rule_type = WR_Update_Select | RW_Update_Select
  type t = T of {name: rule_type}
  let make ~name  = T {name=name}
  let name (T{name}) = name
  let to_string (T{name}) = match name with 
                            |WR_Update_Select -> "ᴡʀ-ᴜᴩᴅᴀᴛᴇ-ꜱᴇʟᴇᴄᴛ"
                            |RW_Update_Select -> "ʀᴡ-ᴜᴩᴅᴀᴛᴇ-ꜱᴇʟᴇᴄᴛ"
                            | _ -> "ᴜɴᴋɴᴏᴡɴ ʀᴜʟᴇ"

  let apply = print_string "applying the rules..."

open App
open Sql
open Var
open Speclang
open Rules
module M = Misc
module V = Var.Variable
module T = Sql.Transaction
module S = Sql.Statement
module RW = Rules.RW
let _HEADER_SIZE = 120
let to_cap = String.capitalize_ascii

(*----------------------------------------------------------------------------------------------------*)
module Constants = 
  struct
    type g = SER | CC | PSI
    
    let line = "\n;"^(String.make _HEADER_SIZE '-')

    let options =  "(set-option :produce-unsat-cores true)"
 
    let basic_relations =        "(declare-fun WR (T T) Bool)
(declare-fun RW (T T) Bool)
(declare-fun WW (T T) Bool)
(declare-fun vis (T T) Bool)
(declare-fun ar (T T) Bool)"

    let basic_assertions= "(assert (! (forall ((t T))       (not (or (WR t t) (RW t t) (WW t t))))     :named no_loops))
(assert (! (forall ((t1 T) (t2 T))   (=> (vis t1 t2) (not (vis t2 t1))))      :named acyc_vis))
(assert (! (forall ((t1 T) (t2 T) (t3 T))(=> (and (ar  t1 t2) (ar  t2 t3)) (ar  t1 t3)))  :named trans_ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (not (= t1 t2)) (xor (ar  t1 t2) (ar  t2 t1))))  :named total_ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (vis t1 t2) (ar t1 t2)))       :named vis_in_ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (WR t1 t2) (vis t1 t2)))       :named wr_then_vis))
(assert (! (forall ((t1 T) (t2 T))   (=> (WW t1 t2) (ar t1 t2)))        :named ww->ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (RW t1 t2) (not (vis t2 t1))))     :named rw_then_not_vis))
(assert (! (forall ((t T))     (not (ar t t)))          :named irreflx_ar))"


    let  gen_all_Types : string list -> string = 
      fun s_list ->
        List.fold_left (fun old_s -> fun curr_t -> old_s^" ("^(String.capitalize_ascii curr_t)^")") "" s_list


   	let primitive_types : string list -> string = fun s_list -> 
      let pr = (gen_all_Types s_list) in 
			String.concat "" ["(declare-datatypes () ((TType";pr;"))) \n(declare-sort T)\n(declare-fun type (T) TType)"] 


		let cycles_to_check = "(assert (exists ((t1 T) (t2 T)) (and (not (= t1 t2)) (RW t1 t2) (RW t2 t1))))"
  
    let guarantee : g -> string = 
      fun g -> match g with
        |SER -> "(assert (! (forall ((t1 T) (t2 T)) (=> (ar t1 t2) (vis t1 t2))):named ser )) ;SER"
        |PSI ->  "(assert (! (forall ((t1 T) (t2 T)) (=> (WW t1 t2) (vis t1 t2))):named psi)) ;PSI"
        |CC -> "(assert (! (forall ((t1 T) (t2 T) (t3 T))  (=> (and (vis  t1 t2) (vis  t2 t3)) (vis  t1 t3))):named cc)) ;CC"
    
    let requests = "(check-sat)"
end


module PrintUtils = 
struct
  let comment_header x1 = let open Constants in 
    let top = ";"^line in
    let bottom = ";"^line in 
    let empty_count = (_HEADER_SIZE - (String.length x1))/2 in 
    let empty_space = (String.make empty_count ' ') in
line^"\n;"^empty_space^x1^empty_space^""^line^"\n"

  let mkCond_equal x1 x2 = "(= ("^x1^") ("^x2^"))"  
  let mkCond_and : string list -> string = fun s_list ->
  let conds = String.concat "" s_list in
    "(and "^conds^")"
end



(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
module Encode =
struct

  let z3_init  = fun s_list -> let open Constants in 
    String.concat "\n\n" [PrintUtils.comment_header "Constants"; options; primitive_types s_list; basic_relations; basic_assertions]


  let z3_final = let open Constants in
    String.concat "\n\n" [PrintUtils.comment_header "Finalization";cycles_to_check;guarantee PSI; requests]


  let table_initialize: Var.Table.t -> string =
    fun table -> let open Var.Table in
    let tname = String.capitalize_ascii @@ name table in
    (*the pk conditions*)
    let cond_pk =  let open PrintUtils in 
      mkCond_and @@ List.map (fun (_,s,_,c) ->
        if c
        then  let proj_of_s = tname^"_Proj_"^s in
              (mkCond_equal (proj_of_s^" r1")(proj_of_s^" r2")) 
        else "") @@ cols table  in
    (*the assertion line regaring the PKs*)
    let dec_pk = "(assert (forall ((r1 "^tname^")(r2 "^
                 tname^")) (=>\n  "^cond_pk^"(= r1 r2))))" in
    let tcols = List.fold_left (fun s_prev -> fun (_,s_col,t_col,pk_col) -> 
      let s_dec = String.concat "" ["(declare-fun ";(tname^"_Proj_"^s_col);" (";tname;") "; (Var.Type.to_string t_col) ; ")"] in
      (String.concat "" [s_prev;"\n";s_dec])) ""  
      @@ cols table in
    String.concat "" ["\n(declare-sort ";tname;")";tcols;"\n";dec_pk]
 
  let all_table_initialize: Var.Table.t list -> string = 
    fun table_list -> (PrintUtils.comment_header"Table Declarations")^
      (List.fold_left (fun s -> fun t -> 
        String.concat "\n" [s; table_initialize t]) "" table_list)

(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(* vars *)
  
  let declare_vars tname vname vtype = let txn_cap = String.capitalize_ascii tname in 
     "(declare-fun "^txn_cap^"_Var_"^vname^" (T) "^vtype^")"


  let txn_declare_vars : (T.t * V.t list) -> string = 
    fun (txn,var_list) -> 
      List.fold_left (fun prev_s -> fun  (V.T{name;tp;_}) -> 
        let var_t = Var.Type.to_string tp in
        let txn_name = T.name txn in
        prev_s^"\n"^(declare_vars txn_name name var_t)) "" var_list


  let stmt_extract_var : Sql.Statement.st -> V.t option = 
    fun stmt -> match stmt with 
      |S.SELECT (_,v,_,_) -> Some v
      |_ -> None
  
  let txn_extract_vars : T.t -> V.t list = fun (T.T{name;params;stmts}) -> 
    List.fold_left (fun prev_l -> fun stmt -> match stmt_extract_var stmt with
                                                |Some curr_var -> prev_l@[curr_var]
                                                |None -> prev_l) [] stmts

(*params*)
  let declare_param tname vname vtype = let txn_cap = String.capitalize_ascii tname in
     "(declare-fun "^txn_cap^"_Param_"^vname^" (T) "^vtype^")"

  let txn_declare_param: (T.t * V.t list) -> string = fun (txn,var_list) ->
        List.fold_left (fun prev_s -> fun (V.T{name;tp;_}) -> 
          let var_t = Var.Type.to_string tp in
          let txn_name = T.name txn in
          prev_s^"\n"^(declare_param txn_name name var_t)) "" var_list

  let all_txn_initialize txn_list = 
    let params = 
      List.fold_left (fun prev_s -> fun curr_txn -> 
        let T.T{name; params; stmts} = curr_txn in 
        let curr_s = txn_declare_param (curr_txn,params) in   
          prev_s^curr_s) "" txn_list in
    let vars = 
      List.fold_left (fun prev_s -> fun curr_txn -> 
        let curr_s = txn_declare_vars @@ (curr_txn,txn_extract_vars curr_txn) in
          prev_s^curr_s) "" txn_list
    in params^"\n\n"^vars

end 

(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*Rules*)

let txns_to_wr = ""
let txns_to_ww = ""

let txns_to_rw: T.t -> T.t -> string = fun txn1 -> fun txn2 -> 
  RW.extract_rules txn1 txn2 

(*TODO*)
(*TODO*)

let all_rw: T.t list -> string = fun txn_list -> 
    List.fold_left (fun old_s -> fun curr_t -> 
      List.fold_left (fun old_s2 -> fun curr_t2 -> 
        old_s2^(txns_to_rw curr_t curr_t2)) old_s txn_list) "" txn_list


let all_wr = ""
let all_ww = "" 
let all_txns_all_rules: T.t list -> string = fun txn_list ->
    PrintUtils.comment_header "Rules"^"\n;~~~~RW\n"^all_rw txn_list^"\n;~~~~WR\n"^all_wr^"\n;~~~~WW\n"^all_ww


(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
  
  let write_to_file s=  
    let oc = open_out "z3-encoding.smt2" in 
    Printf.fprintf oc "%s" s;
    close_out oc


  let encode: Var.Table.t list -> T.t list -> unit = 
    fun table_list -> 
    fun txn_list -> 
      let open Encode in
      let txn_name_list = List.map T.name txn_list in
      write_to_file  @@ String.concat "\n\n" [z3_init txn_name_list;
                                              all_table_initialize table_list;
                                              all_txn_initialize txn_list;
                                              all_txns_all_rules txn_list;
                                              z3_final]

(*----------------------------------------------------------------------------------------------------*)

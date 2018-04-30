open App
open Sql
open Var
open Speclang
open Rules
module M = Misc
module V = Var.Variable
module L = Sql.Transaction

(*----------------------------------------------------------------------------------------------------*)
module Constants = 
  struct
    type g = SER | CC | PSI
    
    let line = "\n;"^(String.make 100 '-')

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

		(*reruens (P1) (P2) (P3)...*)
		let rec gen_all_Ps : int -> string -> string = 
			fun i -> fun old_s -> if i == 0
														then old_s
														else  let curr_i = string_of_int i in 
																	let curr_s = (String.concat "" [old_s;" (P";curr_i;")"]) in
																	gen_all_Ps (i-1) curr_s
	

   	let primitive_types : int -> string = fun count -> 
			let pr = (gen_all_Ps count "") in 
			String.concat "" ["(declare-datatypes () ((TType ";pr;"))) 
    										 (declare-sort T)
                         (declare-fun type (T) TType)"] 



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
    let empty_count = (100 - (String.length x1))/2 in 
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

  let z3_init  = let open Constants in 
String.concat "\n\n" [PrintUtils.comment_header "Constants"; options; primitive_types 5; basic_relations; basic_assertions]


  let z3_final = let open Constants in
											String.concat "\n\n" [cycles_to_check;guarantee PSI; requests]


  let table_initialize: Var.Table.t -> string =
    fun table -> let open Var.Table in
    let tname = String.capitalize_ascii @@ name table in
    (*the pk conditions*)
    let cond_pk =  let open PrintUtils in 
      mkCond_and @@ List.map (fun (s,_,c) ->
        if c
        then (mkCond_equal (s^" r1")(s^" r2")) 
        else "") @@ cols table  in
    (*the assertion line regaring the PKs*)
    let dec_pk = "(assert (forall ((r1 "^tname^")(r2 "^
                 tname^")) (=>\n  "^cond_pk^"(= r1 r2))))" in
    let tcols = List.fold_left (fun s_prev -> fun (s_col,t_col,pk_col) -> 
      let s_dec = String.concat "" ["(declare-fun ";s_col;" (";tname;") "; (Var.Type.to_string t_col) ; ")"] in
      (String.concat "" [s_prev;"\n";s_dec])) ""  
      @@ cols table in
    String.concat "" ["\n(declare-sort ";tname;")";tcols;"\n";dec_pk]
 
  let all_table_initialize: Var.Table.t list -> string = 
    fun table_list -> (PrintUtils.comment_header"Table Declarations")^
      (List.fold_left (fun s -> fun t -> 
        String.concat "\n" [s; table_initialize t]) "" table_list)

(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)

  let declare_param tname vname vtype = let txn_cap = String.capitalize_ascii tname in
     "(declare-fun "^txn_cap^"_Param_"^vname^" (T) "^vtype^")"

  let txn_declare_param: (L.t * V.t list) -> string = fun (txn,var_list) ->
        List.fold_left (fun prev_s -> fun (V.T{name;tp;_}) -> 
          let var_t = Var.Type.to_string tp in
          let txn_name = L.name txn in
          prev_s^"\n"^(declare_param txn_name name var_t)) "" var_list

  let all_txn_initialize txn_list = 
    List.fold_left (fun prev_s -> fun curr_txn -> 
    let L.T{name; params; stmts} = curr_txn in 
    let curr_s = txn_declare_param (curr_txn,params) in   
    prev_s^curr_s) "" txn_list

end 









(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
  
  let write_to_file s=  
    let oc = open_out "z3-encoding.smt2" in 
    Printf.fprintf oc "%s" s;
    close_out oc


  let encode: Var.Table.t list -> L.t list -> unit = 
    fun table_list -> 
    fun txn_list -> 
      let myInt = Var.Type.String in 
      let final_enc = "" in 
      let open Encode in
      write_to_file  @@ String.concat "\n\n" [z3_init;
                                              all_table_initialize table_list;
                                              all_txn_initialize txn_list;
                                              final_enc;z3_final]

(*----------------------------------------------------------------------------------------------------*)





























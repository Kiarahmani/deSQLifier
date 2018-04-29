open App
open Sql
open Var
open Speclang
open Rules
module M = Misc


(*----------------------------------------------------------------------------------------------------*)
module Constants = 
  struct
    type g = SER | CC | PSI
    
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







(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
module Encode =
struct

  let z3_init  = let open Constants in 
											String.concat "\n\n" [options; primitive_types 5; basic_relations; basic_assertions]


  let z3_final = let open Constants in
											String.concat "\n\n" [cycles_to_check;guarantee PSI; requests]


  let table_initialize: Var.Table.t -> string =
    fun table -> let open Var.Table in
    let tname = name table in
    let tcols = List.fold_left (fun s_prev -> fun (s_col,t_col) -> 
      let s_dec = String.concat "" ["(declare-fun ";s_col;" (";(String.capitalize_ascii tname);") "; (Var.Type.to_string t_col) ; ")"] in
      (String.concat "" [s_prev;"\n";s_dec])) ""  
      @@ cols table in
    String.concat "" ["\n(declare-sort ";(String.capitalize_ascii tname);")";tcols]
 
  let all_table_initialize: Var.Table.t list -> string = 
    fun table_list -> List.fold_left (fun s -> fun t -> 
      String.concat "\n" [s; table_initialize t]) "" table_list


  let txn_initialize record= 
    let p1_read_acc = "P1_read_acc" in
    String.concat "" ["
(declare-fun ";p1_read_acc;" (T) Int)
(declare-fun ";p1_read_acc;" (T ";record;") Bool)"]




end 









(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
  
  let write_to_file s=  
    let oc = open_out "z3-encoding.smt2" in 
    Printf.fprintf oc "%s" s;
    close_out oc


  let encode: Var.Table.t list -> Transaction.t list ->unit = 
    fun table_list -> 
    fun txn_list1 -> 
      let myInt = Var.Type.String in 
      let final_enc = "" in (*where the result of rule application goes*)
      write_to_file  @@ String.concat "\n\n" [Encode.z3_init;Encode.all_table_initialize table_list;
                                              Encode.txn_initialize "Bankaccount";
                                              final_enc;Encode.z3_final]

(*----------------------------------------------------------------------------------------------------*)













open App
open Sql
open Speclang
module M = Misc




(*----------------------------------------------------------------------------------------------------*)
module Rule =
struct
  type rule_type = WR_Update_Select | RW_Update_Select
  type t = T of {name: rule_type}
  let make ~name  = T {name=name}
  let name (T{name}) = name
  let to_string (T{name}) = match name with 
                            |WR_Update_Select -> "ᴡʀ-ᴜᴩᴅᴀᴛᴇ-ꜱᴇʟᴇᴄᴛ"
                            |RW_Update_Select -> "ʀᴡ-ᴜᴩᴅᴀᴛᴇ-ꜱᴇʟᴇᴄᴛ"
                            | _ -> "ᴜɴᴋɴᴏᴡɴ ʀᴜʟᴇ"
                            
end


(*----------------------------------------------------------------------------------------------------*)
module Encode =
struct

(*TODO: This is mildly hard-coded for the given application*)
  
  let z3_init_text = "(set-option :produce-unsat-cores true)
  ;=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    ; Primitive types
    (declare-datatypes () ((TType (P1)))) ;all extracted programs
    (declare-sort T)
    (declare-fun type (T) TType)
    
    ; Basic Relations 
    (declare-fun WR (T T) Bool)
    (declare-fun RW (T T) Bool)
    (declare-fun WW (T T) Bool)
    (declare-fun vis (T T) Bool)
    (declare-fun ar (T T) Bool)
    
    ; Basic Assertions on Basic Relations
    (assert (! (forall ((t T))       (not (or (WR t t) (RW t t) (WW t t))))     :named no_loops))
    (assert (! (forall ((t1 T) (t2 T))   (=> (vis t1 t2) (not (vis t2 t1))))      :named acyc_vis))
    (assert (! (forall ((t1 T) (t2 T) (t3 T))(=> (and (ar  t1 t2) (ar  t2 t3)) (ar  t1 t3)))  :named trans_ar))
    (assert (! (forall ((t1 T) (t2 T))   (=> (not (= t1 t2)) (xor (ar  t1 t2) (ar  t2 t1))))  :named total_ar))
    (assert (! (forall ((t1 T) (t2 T))   (=> (vis t1 t2) (ar t1 t2)))       :named vis_in_ar))
    (assert (! (forall ((t1 T) (t2 T))   (=> (WR t1 t2) (vis t1 t2)))       :named wr_then_vis))
    (assert (! (forall ((t1 T) (t2 T))   (=> (WW t1 t2) (ar t1 t2)))        :named ww->ar))
    (assert (! (forall ((t1 T) (t2 T))   (=> (RW t1 t2) (not (vis t2 t1))))     :named rw_then_not_vis))
    (assert (! (forall ((t T))     (not (ar t t)))          :named irreflx_ar))"




  let z3_end_text = ";---------------------------------------------------------------------------------------------------- 
  ; Cycles to Check
  (assert (exists ((t1 T) (t2 T))
      (and (not (= t1 t2)) (RW t1 t2) (RW t2 t1))))
  
  
  ;---------------------------------------------------------------------------------------------------- 
  ; Consistency and Isolation Guarantees
  
  
  ;(assert (! (forall ((t1 T) (t2 T)) (=> (ar t1 t2) (vis t1 t2))):named ser )) ;SER
  (assert (! (forall ((t1 T) (t2 T)) (=> (WW t1 t2) (vis t1 t2))):named psi)) ;PSI
  ;(assert (! (forall ((t1 T) (t2 T) (t3 T))  (=> (and (vis  t1 t2) (vis  t2 t3)) (vis  t1 t3))):named cc)) ;CC
  
  
  
  (check-sat)
  ;(get-unsat-core)
  ;(get-model)"



  let write_to_file s=  
    let oc = open_out "z3-encoding.smt2" in 
    Printf.fprintf oc "%s" s;
    close_out oc



  let env_init record = 
    let accID = "accID" in
    let accBal= "accBal" in
    let p1_read_acc = "P1_read_acc" in
    String.concat "" ["(declare-sort ";record;")
  (declare-fun ";accID;" (";record;") Int)
  (declare-fun ";accBal;" (";record;") Int)
  (assert (forall ((r1 ";record;")(r2 ";record;")) (=> (= (";accID;" r1) (";accID;" r2)) (= r1 r2))))
  (declare-fun ";p1_read_acc;" (T) Int)
  (declare-fun ";p1_read_acc;" (T ";record;") Bool)"]


  
  let rw_US record = 
    let accID = "accID" in
    let p1_read_acc = "P1_read_acc" in
  String.concat "" ["(assert (!
    (forall ((t1 T) (t2 T))
        (=> (and (RW t1 t2) (not (= t1 t2)))
            (exists ((b ";record;"))
            ";"(and (= ("; accID ; " b) (";p1_read_acc;" t1))
                           (= (";accID; " b) (";p1_read_acc;" t2))))))))"]
  
  
  let wr_US record = 
    let accID = "accID" in
    let p1_read_acc = "P1_read_acc" in
    String.concat "" ["(assert (!
    (forall ((t1 T) (t2 T) (b ";record;")) 
        (=> (and (not (= t1 t2))
               (= (";accID;" b) (";p1_read_acc;" t1))
                          (= (";accID;" b) (";p1_read_acc;" t2)) )
            (or (WW t1 t2) (WW t2 t1))))))"]



  let apply_rules: (Statement.t * Statement.t * Rule.t list)-> string -> string =
    fun (st1,st2,rlist) -> fun file_text ->  
      let apply_rule rule = 
      let open Rule in let open Statement in
      match name rule with
        (*TODO: This has to be generalized*)
        |WR_Update_Select -> let curr_assr = rw_US (get_table st1) in
                             printf "%s\n" curr_assr;
                             curr_assr
        |RW_Update_Select -> let curr_assr = wr_US (get_table st1) in
                             printf "%s\n" curr_assr;
                             curr_assr
      in
      let output_txt = List.fold_left (fun s -> fun r -> String.concat "\n\n" [s;(apply_rule r)]) file_text rlist in 
      output_txt



  let applicable_rules: Statement.t -> Statement.t -> Rule.t list = 
    fun st1 -> fun st2 -> let open Statement in 
                          match (get_type st1,get_type st2) with
                           |(UPDATE,SELECT) -> [Rule.make WR_Update_Select;Rule.make RW_Update_Select]
                           |(SELECT,UPDATE) -> [Rule.make WR_Update_Select;Rule.make RW_Update_Select]
                           |_ -> []

  let analyze_stmt: Statement.t -> Statement.t -> Rule.t list  =
    fun st1 -> fun st2 -> printf "\n";
                          Statement.print st1;
                          printf " ⁘";
                          Statement.print st2;
                          printf " ⇢  Applicable Rules: ";
                          let rules = applicable_rules st1 st2 in
                            List.iter (fun r -> printf "%s  " (Rule.to_string r)) rules;
                            rules

  let analyze_txn: Transaction.t -> Transaction.t -> string = 
    fun txn1 -> fun txn2 -> let open Transaction in
                              printf "⓵ Analyzing TXNs:\n(%s) VS (%s) ⇩ " (name txn1) (name txn2);
                              let st_list1 = stmts txn1 in
                              let st_list2 = stmts txn2 in
                              (*return all possibilities of (Statement.t,Statement.t,Rule.t)*)
                              let st_rule_list = List.fold_left 
                                                  (fun old_list -> fun st1 ->
                                                    List.append old_list 
                                                    (List.fold_left (fun old_list_in -> fun st2 -> 
                                                      let rules = analyze_stmt st1 st2 in
                                                      List.append old_list_in [(st1,st2,rules)]) [] st_list2)) 
                                                  []  st_list1 in   

                              printf "\n\n⓶ Z3 Encodings:\n";
                              printf "Env\n---------------------------------\n%s\n---------------------------------\n" (env_init "BankAccount"); (*TODO*)
                              let file_text = List.fold_left (fun str_in -> fun triple -> apply_rules triple str_in) "" st_rule_list in
                              printf "\n⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼⇼\n";
                              file_text


end 
  
  
  
  let encode_txns: (Transaction.t list) -> unit = 
    fun txn_list1 -> 
      let final_enc = 
      List.fold_left 
        (fun str_out -> fun txn1 -> List.fold_left 
                        (fun str_in -> fun txn2 -> 
                            String.concat "" [str_in;(Encode.analyze_txn txn1 txn2)]) 
                     str_out  
                     txn_list1) 
      ""
      txn_list1 
      in
      Encode.write_to_file  @@ String.concat "\n\n" [Encode.z3_init_text;(Encode.env_init "BankAccount");final_enc;Encode.z3_end_text] (*TODO*)


(*----------------------------------------------------------------------------------------------------*)


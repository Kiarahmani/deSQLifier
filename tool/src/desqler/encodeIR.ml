open App
open Speclang
module M = Misc

let printf = Printf.printf
let print_txn_name (Speclang.Fun.T app) = print_string app.name.name
let print_ident : Ident.t -> unit = fun ident -> print_string ident.name


(*----------------------------------------------------------------------------------------------------*)
module Print = 
struct 
   (*helping function to determine the case to catch*)
   let exp_to_stirng: Typedtree.expression -> unit = 
		fun exp -> let desc = exp.exp_desc in
			match desc with 
                        |Texp_ident (_,_,_) -> printf "Texp_ident"
                        |Texp_constant _ -> printf "Texp_constant"
                        |Texp_let (_,_,_) -> printf "Texp_let"
                        |Texp_function (_,_,_) -> printf "Texp_function"
                        |Texp_apply (_,_) -> printf "Texp_apply"
                        |Texp_match (_,_,_,_) -> printf "Texp_match"
                        |Texp_try (_,_) -> printf "Texp_try"
                        |Texp_tuple _ -> printf "Texp_try"
                        |Texp_construct (_,_,_) -> printf "Texp_try"
                        |Texp_variant (_,_) -> printf "Texp_try"
                        |_ -> printf "ERROR: Print Expression - case not implemented yet"

end

(*----------------------------------------------------------------------------------------------------*)
module FOL = 
struct
  type t = T of {name_l: string; name_r: string}
  let left  (T{name_l;name_r}) = name_l
  let right (T{name_l;name_r}) = name_r
  let make ~name_l ~name_r = T{name_l=name_l;name_r=name_r}
end

(*----------------------------------------------------------------------------------------------------*)
module Statement =
struct
	type stmt_type = SELECT | UPDATE | INSERT | DELETE
  type t = T of {stmt_tp: stmt_type;
								 acc_table: string;
								 acc_fields: string list;
								 phi: FOL.t;
								 psi: FOL.t}
	let make ~stmt_tp ~acc_table ~acc_fields ~phi ~psi = 
		T {stmt_tp=stmt_tp; acc_table=acc_table; acc_fields=acc_fields; phi=phi; psi=psi}
  
  let get_type (T{stmt_tp;}) = stmt_tp
  let get_table(T{acc_table})=acc_table
  
  let make_empty =
    T {stmt_tp=SELECT; acc_table="Empty Table"; acc_fields=["empty filed"]; phi=(FOL.T{name_l="empty";name_r="empty"}); psi=(FOL.T{name_l="empty";name_r="empty"})}


  let print (T{stmt_tp;acc_table}) = match stmt_tp with
    | SELECT -> printf " SELECT";
								printf "(%s)" (acc_table);
		| UPDATE -> printf " UPDATE";
								printf "(%s)"  (acc_table);
(*
  let print (T{stmt_tp;acc_table;acc_fields;phi;psi}) = match stmt_tp with
    | SELECT -> printf "IF (%s=%s"(FOL.left psi)(FOL.right psi) ;
                printf "):";
                printf " SELECT (";
								List.iter (fun field -> printf "%s " field) acc_fields;
								printf ") FROM %s WHERE %s=%s" (acc_table)(FOL.left phi)(FOL.right phi);
		| UPDATE -> printf "IF (%s=%s"(FOL.left psi)(FOL.right psi) ;
                printf "):";
                printf " UPDATE (";
								List.iter (fun field -> printf "%s " field) acc_fields;
								printf ") FROM %s WHERE %s=%s"  (acc_table)(FOL.left phi)(FOL.right phi);
		| INSERT -> printf "INSERT (";
								List.iter (fun field -> printf "%s," field) acc_fields;
								printf ") WHERE %s=%s" (FOL.left psi)(FOL.right psi);
		| DELETE -> printf "DELETE (";
								List.iter (fun field -> printf "%s," field) acc_fields;
								printf ") WHERE %s=%s" (FOL.left phi)(FOL.right phi);
*)
end

(*----------------------------------------------------------------------------------------------------*)
module Transaction = 
struct
  type t = T of {name: string;
                 stmts: (Statement.t) list}
  let make ~name ~stmts = T {name=name; stmts=stmts}
	let print (T{name;stmts}) = List.iter (fun st -> printf "op: "; Statement.print st; printf "\n") (List.rev stmts)
  let name (T{name}) = name
  let stmts (T{stmts}) = stmts
end




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


  let encode_txns: (Transaction.t list) -> unit = 
    fun txn_list1 -> 
      let final_enc = 
      List.fold_left 
        (fun str_out -> fun txn1 -> List.fold_left 
                        (fun str_in -> fun txn2 -> 
                            String.concat "" [str_in;(analyze_txn txn1 txn2)]) 
                     str_out  
                     txn_list1) 
      ""
      txn_list1 
      in
      write_to_file  @@ String.concat "\n\n" [z3_init_text;(env_init "BankAccount");final_enc;z3_end_text] (*TODO*)
end 


(*----------------------------------------------------------------------------------------------------*)
module Extract = 
struct
	
  let extract_single_exp:  Typedtree.expression -> Statement.t = 
    fun exp -> Statement.make_empty

  (*EXTRACTING THE WHERE CLAUSE*)
  let extract_where_fun: Typedtree.expression -> FOL.t = 
    fun exp -> match exp.exp_desc with
                 |Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"=",_),_,_)},
                                      [(Asttypes.Nolabel,Some e1);(Asttypes.Nolabel,Some e2)]) -> 
                                        match (e1.exp_desc,e2.exp_desc )with 
                                        |(Texp_field (l1,l2,l3) , Texp_ident (Pident r,_,_))->
                                            FOL.T{name_l=l3.lbl_name;name_r=r.name}

  let rec extract_exps_rec: (Statement.t list) -> Typedtree.expression -> (Statement.t list) =
    fun st_list exp -> match exp.exp_desc with
        									|Texp_let (_,b,e2) -> let st1 = extract_exps_rec st_list ((List.hd b).vb_expr) in 
																								extract_exps_rec (List.append st1 st_list) e2; 
                          
                          (*SELECT*)
													|Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"select1",_),_,_)},
                                      [(Asttypes.Nolabel,Some e1);(Asttypes.Nolabel,Some e2)])
                                      when (Ident.name id = "SQL") -> 
  																				 begin
 																		         match (e1.exp_desc,e2.exp_desc) with
																		          | (Texp_construct (_,{cstr_name="::"},
                             										[{exp_desc=Texp_construct (_,table_cons,[])};
                             	 									{exp_desc=Texp_construct (_,{cstr_name="[]"},[])}]),
																	              Texp_function (arg_label,[case],_)) ->
                                                  (*the where clause*)
                                                  let ([arg_id],body) = Astutils.extract_lambda case in 
                                                  let where = extract_where_fun body in 
                                                  let this = [Statement.T{stmt_tp=SELECT; acc_table=table_cons.cstr_name; acc_fields=[" field"]; 
                                                             phi=where; psi=(FOL.T{name_l="true";name_r="true"})}] in
                                          				List.append this st_list

																							| (Texp_construct (_,{cstr_name="::"},args), _) ->
																	              failwith "extract_exps_rec: Unimpl.\n"
                                           end

                          (*UPDATE*)
													|Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"update",_),_,_)},
 						                 						[(_,Some e1); (_,Some e2); (_,Some e3)])
        																when (Ident.name id = "SQL") ->
	 																       begin
																          match (e1.exp_desc, e2.exp_desc, e3.exp_desc) with
																          | (Texp_construct (_,table_cons,[]), (* Table being updated *)
																             Texp_function (_,[s_case],_), (* SET function g *)
																             Texp_function (_,[w_case],_)) (* WHERE function f *) ->
                                         let ([arg_id],body) = Astutils.extract_lambda w_case in 
                                         let where = extract_where_fun body in 
                                         let this = [Statement.T{stmt_tp=UPDATE; acc_table=table_cons.cstr_name; acc_fields=[" field"]; 
                                                         phi=where; psi=(FOL.T{name_l="true";name_r="true"})}] in
                                         List.append this st_list
																				 end
                          
                          |_ -> printf "\n"; Print.exp_to_stirng exp;
                                failwith "Not implemented"


	let extract_exps: Typedtree.expression -> (Statement.t list) = 
    fun exp -> extract_exps_rec [] exp




	let extract_txn:Speclang.Fun.t -> Transaction.t =
		fun app  -> let _ = printf "\n𝙸𝚁 𝙴𝚡𝚝𝚛𝚊𝚌𝚝𝚒𝚘𝚗:\n ";
			  	  				  	print_txn_name app; in
			    		  				let Speclang.Fun.T {name; rec_flag; args_t ; body} = app in
													printf " ---> ✅ \n";
                          Transaction.make (name.name) (extract_exps body)

end


(*----------------------------------------------------------------------------------------------------*)
let doIt (App.T a) = 
        let _ = printf "=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=\n|" in
        let _ = printf "                 Compilation Phase                   " in 
        let _ = printf "|\n=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=\n" in
        let ex_txn_list = List.fold_left (fun l -> fun t -> (List.cons t l)) [] 
            (List.map (fun tx -> Extract.extract_txn tx) a.txns) in
        printf "\n𝙴𝚗𝚌𝚘𝚍𝚒𝚗𝚐:\n";
        Encode.encode_txns ex_txn_list


open App
open Sql
open Speclang
module M = Misc


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

end
	

(*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)
  let extract_txn:Speclang.Fun.t -> Transaction.t =
		fun app  -> let _ = printf "\n𝙸𝚁 𝙴𝚡𝚝𝚛𝚊𝚌𝚝𝚒𝚘𝚗:\n ";
			  	  				  	print_txn_name app; in
			    		  				let Speclang.Fun.T {name; rec_flag; args_t ; body} = app in
													printf " ---> ✅ \n";
                          Transaction.make (name.name) (Extract.extract_exps body)




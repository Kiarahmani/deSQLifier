open Typedtree

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


   let rec print_fun_exp: Typedtree.expression_desc -> unit =
    fun desc -> match desc with
          (*SELECT FROM*)
          |Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"select1",_),_,_)},
                  [(Asttypes.Nolabel,Some e1);(Asttypes.Nolabel,Some e2)]) 
					        when (Ident.name id = "SQL") ->
					  begin
					  match (e1.exp_desc,e2.exp_desc) with
            |(Texp_construct (_,{cstr_name="::"},[{exp_desc=Texp_construct (_,table_cons,[])}; {exp_desc=Texp_construct (_,{cstr_name="[]"},[])}]),
						  Texp_function (arg_label,[case],_)) ->		
							  match case with 
							  |{c_lhs=n; c_rhs=o;} -> 
							  	printf "SELECT FROM %s WHERE \n\n\n" table_cons.cstr_name ;
                  print_exp o;
	      			  |_ -> printf "ERROR: SQL.SELECT- Unexpected case"
				 	  end
            (*WHERE BOOL FUNCTION*)
            |Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,f,_),_,_)},
                                  [(Asttypes.Nolabel,Some e1);(Asttypes.Nolabel,Some e2)])->
                                    Printf.printf "%s" f;
                                    exp_to_stirng e2

            |_ -> printf "ERROR: print_fun_exp - case not expected"


   and print_let_exp: Typedtree.value_binding -> unit = 
        fun let_exp -> match let_exp with 
          |{vb_pat={pat_desc=Tpat_var (x,_);pat_type=tye};vb_expr=y} -> 
              let _ = printf "LET " in
              let _ = print_ident x in 
							let _ = printf " = " in
            	print_exp y
					

   and print_exp:Typedtree.expression -> unit =
     fun exp -> let desc = exp.exp_desc in
	    match desc with 
        |Texp_let (_,b,e2) -> print_let_exp @@ List.hd b;
                              (*print_exp e2 *) (*TODO: Catch this!*)
        |Texp_apply (_,_) ->  print_fun_exp desc
        |_ -> printf "\n ERROR: print_exp - not implemented yet"
	




	let print_txn:Speclang.Fun.t -> unit =
		fun app  -> let _ = printf "\nExtracting: ";
			  	  				  print_txn_name app;
			  	    			  printf "\n------------------------\n"; in
			    		  let Speclang.Fun.T {name; rec_flag; args_t ; body} = app in
						      print_exp body
     
end



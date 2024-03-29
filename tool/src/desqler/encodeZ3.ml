open App
open Sql
open Var
open Speclang
open Rules
open Constants
module M = Misc
module V = Var.Variable
module T = Sql.Transaction
module S = Sql.Statement
module RW = Rules.RW
module TWW = Rules.Then_WW
module WWT = Rules.WW_Then
module WRT = Rules.WR_Then
module TWR = Rules.Then_WR
let _MAX_CYCLE_LENGTH = Constants._MAX_CYCLE_LENGTH
let _GUARANTEE = Constants._GUARANTEE
let _HEADER_SIZE = 120
let to_cap = String.capitalize_ascii

(*----------------------------------------------------------------------------------------------------*)
module Cons = 
  struct
    
    let line = "\n;"^(String.make _HEADER_SIZE '~')

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


    let gen_deps = "(declare-fun D (T T) Bool)\n(assert (! (forall ((t1 T)(t2 T)) (=> (D t1 t2) (or (WW t1 t2)(WR t1 t2)(RW t1 t2)))) :named gen-dep) )"

    let  gen_all_Types : string list -> string = 
      fun s_list ->
        List.fold_left (fun old_s -> fun curr_t -> old_s^" ("^(String.capitalize_ascii curr_t)^")") "" s_list


   	let primitive_types : string list -> string = fun s_list -> 
      let pr = (gen_all_Types s_list) in 
			String.concat "" ["(declare-datatypes () ((TType";pr;"))) \n(declare-sort T)\n(declare-fun type (T) TType)"] 
    
  
    
    (*creating the general form of cycles of length less than _MAX_CYCLE_LENGTH*)
    (*just helping to create a range list*)
    let range i j = let rec aux n acc = 
      if n < i then acc else aux (n-1) (n :: acc)
      in aux j []
    let max = string_of_int _MAX_CYCLE_LENGTH 
    let all_ts = List.fold_left (fun old_s -> fun curr_i -> old_s^" (t"^(string_of_int curr_i)^" T)") "" (range 1 _MAX_CYCLE_LENGTH)
    let all_ands = List.fold_left (fun old_s -> fun curr_i -> old_s^
                                              " (D t"^(string_of_int curr_i)^
                                              " t"^(string_of_int @@ curr_i+1)^
                                              ")") "" (range 1 (_MAX_CYCLE_LENGTH-1)) 
    let cycles_to_check = gen_deps^"\n(assert (! (exists ("^all_ts^") (and (not (= t1 t"^max^")) "^all_ands^" (D t"^max^" t1))) :named cycle))"
  
 

    let guarantee : (Constants.g*string option*string option) -> string = 
      fun (g,t1,t2) -> match (g,t1,t2) with
        |(SER,None,None) -> ";SER \n(assert (! (forall ((t1 T) (t2 T)) (=> (ar t1 t2) (vis t1 t2))):named ser ))"
        |(SER,Some t1,Some t2) -> ";Selective SER \n(assert (! (forall ((t1 T) (t2 T)) (=> (and (or (and (= (type t1) "^t1^")(= (type t2)"^t2^"))
                                                (and (= (type t1) "^t2^")(= (type t2)"^t1^"))) 
                                            (ar t1 t2))  (vis t1 t2))):named "^t1^"-"^t2^"-selective-ser ))"
        |(PSI,None,None) ->  ";PSI \n(assert (! (forall ((t1 T) (t2 T)) (=> (WW t1 t2) (vis t1 t2))):named psi))"
        |(CC,None,None) -> ";CC \n(assert (! (forall ((t1 T) (t2 T) (t3 T))  (=> (and (vis  t1 t2) (vis  t2 t3)) (vis  t1 t3))):named cc))"
        |(CC,Some t,_) -> ";Selective CC \n(assert (! (forall ((t1 T) (t2 T) (t3 T))  (=> (and (= (type t3) "^t^") (vis  t1 t2) (vis  t2 t3)) (vis  t1 t3))):named cc))"
        |(EC,_,_) -> ";EC"
 

let all_guarantees = "\n;Guarantees"^List.fold_left (fun old_s -> fun g -> old_s^"\n"^(guarantee g) ) "" _GUARANTEE




let requests = "\n(check-sat)\n;(get-unsat-core)"
end


module PrintUtils = 
struct
  let comment_header x1 = let open Cons in 
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

  let z3_init  = fun s_list -> let open Cons in 
    String.concat "\n\n" [PrintUtils.comment_header "Constants"; options; primitive_types s_list; basic_relations; basic_assertions]


  let z3_final = let open Cons in
String.concat "\n" [PrintUtils.comment_header "Finalization";cycles_to_check;all_guarantees; requests]

  let table_phi_deps :  string -> string = 
    fun table_name ->
    "\n(assert (! (forall ((r "^table_name^")(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_"^table_name^" r t2 t1)(RW_"^table_name^" r t1 t3))(WW_"^table_name^" r t2 t3))) :named "^String.lowercase_ascii table_name^"-lww-row))"^
    "\n(assert (! (forall ((r "^table_name^")(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_"^table_name^" r t2 t1)(RW_Alive_"^table_name^" r t1 t3))(WW_Alive_"^table_name^" r t2 t3))) :named "^String.lowercase_ascii table_name^"-lww-alive))"
  
  let table_deps_gen_deps : string -> string -> string = 
    fun dep_type -> fun table_name ->
      "\n(assert (! (forall ((r "^table_name^")(t1 T)(t2 T)) (=> ("^dep_type^"_"^table_name^" r t1 t2) ("^dep_type^" t1 t2)))       :named "^String.lowercase_ascii table_name^"-"^dep_type^"-then-row))"^
      "\n(assert (! (forall ((r "^table_name^")(t1 T)(t2 T)) (=> ("^dep_type^"_Alive_"^table_name^" r t1 t2) ("^dep_type^" t1 t2))) :named "^String.lowercase_ascii table_name^"-"^dep_type^"-then-alive))"


  let table_deps_funcs : string -> string -> string = 
    fun dep_type -> fun table_name ->
      "\n(declare-fun "^dep_type^"_"^table_name^" ("^table_name^" T T) Bool)"^
      "\n(declare-fun "^dep_type^"_Alive_"^table_name^" ("^table_name^" T T) Bool)"

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
    let dec_pk = "(assert (! (forall ((r1 "^tname^")(r2 "^
                 tname^")) (=>\n  "^cond_pk^"(= r1 r2))) :named pk-"^String.lowercase_ascii tname^") )" in
    let tcols = List.fold_left (fun s_prev -> fun (_,s_col,t_col,pk_col) -> 
      let s_dec = String.concat "" ["(declare-fun ";(tname^"_Proj_"^s_col);" (";tname;") "; (Var.Type.to_string t_col) ; ")"] in
      (String.concat "" [s_prev;"\n";s_dec])) ""  
      @@ cols table in
    (*the specific per table deps relations*)
    let deps = (table_deps_funcs "RW" tname)^(table_deps_funcs "WR" tname)^(table_deps_funcs "WW" tname) in
    let gen_deps = (table_deps_gen_deps "RW" tname)^(table_deps_gen_deps "WR" tname)^( table_deps_gen_deps "WW" tname) in
    let phi_deps = table_phi_deps tname in
    let is_alive = "\n(declare-fun IsAlive_"^tname^" ("^tname^" T) Bool)" in
    String.concat "" ["\n(declare-sort ";tname;")";tcols;"\n";dec_pk;deps;is_alive;gen_deps;phi_deps]
 
  


  let all_table_initialize: Var.Table.t list -> string = 
    fun table_list -> (PrintUtils.comment_header"Table Declarations")^
      (List.fold_left (fun s -> fun t -> 
        String.concat "\n" [s; table_initialize t]) "" table_list)

(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(* vars *)
  
  let declare_vars tname vname vtype table_name = let txn_cap = String.capitalize_ascii tname in 
    ";"^tname^"_"^vname^
    "\n(declare-fun "^txn_cap^"_isN_"^vname^" (T) Bool)"^ 
    "\n(declare-fun "^txn_cap^"_Var_"^vname^" (T) "^table_name^")"^
    "\n(assert (! (forall((t0 T))(and (=> (not ("^txn_cap^"_isN_"^vname^" t0)) (exists ((r "^table_name^"))(= ("^txn_cap^"_Var_"^vname^" t0) r))) 
                               (=> (exists ((r "^table_name^"))(= ("^txn_cap^"_Var_"^vname^" t0) r)) (not ("^txn_cap^"_isN_"^vname^" t0))))) :named "^tname^"-"^vname^"-isnull-prop) )"

  let vars_props tname vname table_name fol = 
    let txn_cap = String.capitalize_ascii tname in 
    let innser_record = "("^txn_cap^"_Var_"^vname^" t0)" in
    let inner_eq = Rules.Utils.extract_where 0 innser_record txn_cap table_name fol in
    "(assert (! (forall ((t0 T)) "^inner_eq^") :named "^tname^"-"^vname^"-select-prop))"
  
  let choose_vars_props tname vname table_name fol chosen_var = 
    let txn_cap = String.capitalize_ascii tname in 
    let innser_record = "("^txn_cap^"_Var_"^vname^" t0)" in
    let inner_eq = Rules.Utils.extract_where 0 innser_record txn_cap table_name fol in
    "(assert (! (forall ((t0 T)) "^inner_eq^") :named "^tname^"-"^vname^"-var-filter-prop))"^
    "\n(assert (! (forall ((t0 T))("^txn_cap^"_SVar_"^chosen_var^" t0 ("^txn_cap^"_Var_"^vname^" t0)))  :named "^tname^"-"^vname^"-var-chosen-prop))"


  let set_vars_props tname vname table_name fol = 
    let txn_cap = String.capitalize_ascii tname in 
    let inner_eq = Rules.Utils.extract_where 0 "r" txn_cap table_name fol in
  "(assert (! (forall ((t0 T)(r "^table_name^")) (=> ("^txn_cap^"_SVar_"^vname^" t0 r) "^inner_eq^")) :named "^tname^"-"^vname^"-var-prop))" 


  let declare_set_vars table_name tname vname vtype = let txn_cap = String.capitalize_ascii tname in 
    ";"^vname^"\n(declare-fun "^txn_cap^"_SVar_"^vname^" (T "^table_name^") Bool)"



  let txn_declare_vars : (T.t * (string*V.t*string*F.t*string) list) -> string = 
  fun (txn,var_list) -> 
    let vars = 
      List.fold_left (fun prev_s -> fun v ->
        match v with 
          |("v",V.T{name;tp;_},table_name,fol,_) -> 
            let var_t = Var.Type.to_string tp in
            let txn_name = T.name txn in
            let var_dec = declare_vars txn_name name var_t table_name in
            let props = vars_props txn_name name table_name fol in
            prev_s^"\n"^var_dec^"\n"^props

          |("s",V.T{name;tp;_},table_name, fol,_) -> 
            let var_t = Var.Type.to_string tp in
            let txn_name = T.name txn in
            let var_dec = declare_set_vars table_name txn_name name var_t in
            let props = set_vars_props txn_name name table_name fol  in
            prev_s^"\n"^var_dec^"\n"^props

          |("c",V.T{name;tp;_},table_name, fol,chosen_var) -> 
            let var_t = Var.Type.to_string tp in
            let txn_name = T.name txn in
            let var_dec = declare_vars txn_name name var_t table_name in
            let props = choose_vars_props txn_name name table_name fol chosen_var  in
            prev_s^"\n"^var_dec^"\n"^props) 
          "" var_list 
      in vars
  


  let stmt_extract_var : Sql.Statement.st -> V.t option * string * string * F.t *string=  (*the var, the type of the var normal/set, the name of the table being read*)
    fun stmt -> match stmt with 
      |S.SELECT ((tb_name,_,_,_),v,f,_) -> (Some v,"v",tb_name,f,"")
      |S.RANGE_SELECT ((s_tb_name,_,_,_),v,f,_) -> (Some v,"s",s_tb_name,f,"")
      |S.MAX_SELECT (_,v,f,_) ->  (Some v,"v","",f,"")
      |S.MIN_SELECT (_,v,f,_) ->  (Some v,"v","",f,"")
      |S.COUNT_SELECT (_,v,f,_) ->  (Some v,"v","",f,"")
      |S.CHOOSE (v,v2,f,_) -> (Some v, "c",(V.table v), f,(V.name v2))
      |_ -> (None,"","",F.my_true,"")

  let txn_extract_vars : T.t -> (string*V.t*string*F.t*string) list = 
  fun (T.T{name;params;stmts}) ->  (*first list is for normal vars the second is for set vars (result of select range)*)
  let vars = 
    List.fold_left (fun prev_l -> fun stmt -> match stmt_extract_var stmt with
                                                |(Some curr_var,"v",tb_name,fol,_) -> prev_l@[("v",curr_var,tb_name,fol,"")]
                                                |(Some curr_var,"s",tb_name,fol,_) -> prev_l@[("s",curr_var,tb_name,fol,"")]
                                                |(Some curr_var,"c",tb_name,fol,chosen_var) -> prev_l@[("c",curr_var,tb_name,fol,chosen_var)]
                                                |_ -> prev_l) [] stmts
  in (vars)
  
(*params*)
  let declare_param tname vname vtype = let txn_cap = String.capitalize_ascii tname in
     "(declare-fun "^txn_cap^"_Param_"^vname^" (T) "^vtype^")"
  
  let declare_param_list tname vname vtype = let txn_cap = String.capitalize_ascii tname in
     "(declare-fun "^txn_cap^"_SVar_"^vname^" (T "^String.capitalize_ascii vtype^") Bool)"


  let txn_declare_param: (T.t * V.t list) -> string = fun (txn,var_list) ->
    List.fold_left (fun prev_s -> fun (V.T{name;field;table;tp;kn}) -> 
          match kn with 
              |Var.Variable.RECORD -> 
                    let var_t = Var.Type.to_string tp in
                    let txn_name = T.name txn in
                    prev_s^"\n"^(declare_param_list txn_name name var_t)
              |_-> 
                    let var_t = Var.Type.to_string tp in
                    let txn_name = T.name txn in
                    prev_s^"\n"^(declare_param txn_name name var_t)
        ) "" var_list
  


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
          in ";params"^params^"\n"^vars
end 

(*----------------------------------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------------------------------*)
(*Rules*)


let txns_to_wr1: T.t -> T.t -> string = fun txn1 -> fun txn2 ->
  WRT.extract_rules txn1 txn2

let txns_to_wr2: T.t -> T.t -> string = fun txn1 -> fun txn2 ->
  TWR.extract_rules txn1 txn2

let txns_to_rw: T.t -> T.t -> string = fun txn1 -> fun txn2 -> 
  RW.extract_rules txn1 txn2 

let txns_to_ww1: T.t -> T.t -> string = fun txn1 -> fun txn2 ->
  TWW.extract_rules txn1 txn2

let txns_to_ww2: T.t -> T.t -> string = fun txn1 -> fun txn2 ->
  WWT.extract_rules txn1 txn2


let all_rw: T.t list -> string = fun txn_list -> 
    List.fold_left (fun old_s -> fun curr_t -> 
      List.fold_left (fun old_s2 -> fun curr_t2 -> 
        old_s2^(txns_to_rw curr_t curr_t2)) old_s txn_list) "" txn_list

let all_wr1: T.t list -> string = fun txn_list -> 
    List.fold_left (fun old_s -> fun curr_t -> 
      List.fold_left (fun old_s2 -> fun curr_t2 -> 
        old_s2^(txns_to_wr1 curr_t curr_t2)) old_s txn_list) "" txn_list

let all_wr2: T.t list -> string = fun txn_list -> 
    List.fold_left (fun old_s -> fun curr_t -> 
      List.fold_left (fun old_s2 -> fun curr_t2 -> 
        old_s2^(txns_to_wr2 curr_t curr_t2)) old_s txn_list) "" txn_list




let all_ww1: T.t list -> string = fun txn_list -> 
    List.fold_left (fun old_s -> fun curr_t -> 
      List.fold_left (fun old_s2 -> fun curr_t2 -> 
        old_s2^(txns_to_ww1 curr_t curr_t2)) old_s txn_list) "" txn_list
let all_ww2: T.t list -> string = fun txn_list -> 
    List.fold_left (fun old_s -> fun curr_t -> 
      List.fold_left (fun old_s2 -> fun curr_t2 -> 
        old_s2^(txns_to_ww2 curr_t curr_t2)) old_s txn_list) "" txn_list


let all_txns_all_rules: T.t list -> string = fun txn_list ->
    (PrintUtils.comment_header "RW-> Rules")^all_rw txn_list^"\n"^
    (PrintUtils.comment_header "WR-> Rules")^all_wr1 txn_list^"\n"^
    (PrintUtils.comment_header "WW-> Rules")^all_ww2 txn_list^"\n"^
    (PrintUtils.comment_header "->WR Rules")^all_wr2 txn_list^"\n"^
    (PrintUtils.comment_header "->WW Rules")^all_ww1 txn_list


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

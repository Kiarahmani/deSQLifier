let unimpl () = failwith "Unimpl"
let print x = ()

module U = Unix

type table_name = 
  | Bankaccount
  | Employee
  | Department

type column_name = 
  |B_all |B_id |B_bal
  |E_all |E_id |E_name |E_sal
 (* |DE_all|DE_id|DE_address|DE_budget *)


(* Definition of SimpSQL *)
module SQL : 
sig
  val select1:      table_name -> column_name  -> ('a -> bool) -> 'a
  val select:       table_name -> column_name -> ('a -> bool) -> 'a list
  val select_max:   table_name -> column_name -> ('a -> bool) -> 'a
  val select_min:   table_name -> column_name -> ('a -> bool) -> 'a
  val select_count: table_name -> column_name -> ('a -> bool) -> int
  val insert:       table_name  ->  'a -> unit
  val delete:       table_name  -> ('a -> bool) -> unit
  val update:       table_name  -> ('a -> unit) -> ('a -> bool) -> unit
  val choose:  ('a -> bool) -> 'a list -> 'a
  val foreach: 'a list -> ('a -> unit) -> unit
end = 
struct
  let select = unimpl ()
  let select1 = unimpl ()
  let select_max = unimpl ()
  let select_count = unimpl ()
  let select_min = unimpl ()
  let insert = unimpl ()
  let delete = unimpl ()
  let update = unimpl ()
  let choose = unimpl ()
  let foreach = unimpl ()
end


(*Tabel Definitions*)
type bankaccount = {b_id: int; mutable b_bal: int}
(*type department = {de_id: int; mutable de_address: string; mutable de_budget: int}
*)
type employee = {e_id: int; mutable e_name: string; mutable e_sal: int}

(*
(*TXN1*)
let txn1_txn (src_id:int) (dst_id:int) (amount:int) =  
  SQL.update Employee
     (fun u -> begin u.e_sal <- amount; end)          
     (fun u -> u.e_id != src_id)
 
  SQL.delete Employee (fun u -> u.e_id = src_id);
  SQL.insert Employee {e_id=src_id;e_name="David";e_sal=amount};
  let acc_src = SQL.select1 Bankaccount B_bal 
                  (fun u -> u.b_id = src_id) in 
  let acc_dst = SQL.select_max Employee E_sal 
                (fun u -> u.e_id = dst_id) in 
    SQL.update Bankaccount
    (*do:*)    (fun u -> begin u.b_bal <- amount; end)
    (*where:*) (fun u -> u.b_id = src_id); 
    SQL.update Employee
    (*do:*)    (fun u -> begin u.e_sal <- 400; end)
    (*where:*) (fun u -> u.e_id = dst_id)
*)

(*you cannot fix this with PSI, right?*)
(*TXN2*)
let deposit_txn (input:int) =  
 
  let v1 = SQL.select1 Employee E_sal
                   (fun u -> u.e_id = input) in 
  SQL.insert Employee {e_id=v1.e_id+1;e_name="Roger";e_sal=input};
  
  (*let v2 = SQL.choose (fun u -> u.e_id <300) v1 in
  *)
 (* SQL.foreach v1
   begin fun loop_var_1 -> 
    (*let vx = SQL.select1 Employee E_sal
   *)                (fun u -> u.e_id = loop_var_1.e_id) in *)
   (*end*)
  (*
  let w_read_all = SQL.select_min Employee E_sal
                   (fun u -> u.e_name = "Roger") in 

 SQL.delete Employee (fun u -> u.e_id = wsrc_id);
  
  SQL.insert Employee {e_id=wsrc_id;e_name="Roger";e_sal=wamount};
 SQL.delete Employee (fun u -> u.e_id = 100);
 
  let w_read_bal = SQL.select1 Employee E_sal
                   (fun u -> u.e_id = wsrc_id) in
  
  SQL.update Employee
    (*do:*)    (fun u -> begin u.e_sal <- wamount; end)    
      (*where:*) (fun u -> u.e_id = wsrc_id)
*)






























































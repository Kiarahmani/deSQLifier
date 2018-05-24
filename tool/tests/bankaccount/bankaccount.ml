let unimpl () = failwith "Unimpl"
let print x = ()

module U = Unix

type table_name = 
  | Bankaccount
  | Employee

type column_name = 
  |B_all
  |B_id
  |B_bal
  |E_all
  |E_id
  |E_name
  |E_sal

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
end


(*Tabel Definitions*)
type bankaccount = {b_id: int; mutable b_bal: int}
type employee = {e_id: int; mutable e_name: string; mutable e_sal: int}
(*
(*TXN1*)
let deposit_txn (src_id:int) (dst_id:int) (amount:int) =  
    let acc_src = SQL.select1 Bankaccount B_bal 
                  (fun u -> u.b_id = src_id) in
  let acc_dst = SQL.select1 Employee E_sal 
                (fun u -> u.e_id = dst_id) in 
    SQL.update Bankaccount
    (*do:*)    (fun u -> begin u.b_bal <- amount; end)
    (*where:*) (fun u -> u.b_id = src_id); 
    SQL.update Employee
    (*do:*)    (fun u -> begin u.e_sal <- 400; end)
    (*where:*) (fun u -> u.e_id = dst_id)
*)

(*TXN2*)
let withdraw_txn (wsrc_id:int) (wamount:int) =  
  let w_read_all = SQL.select1 Employee E_sal
                   (fun u -> u.e_id = wsrc_id) in 
  (*let w_read_bal = SQL.select1 Bankaccount B_bal
                   (fun u -> u.b_id = wsrc_id) in*)
  SQL.insert Employee {e_id=wsrc_id;e_name="David";e_sal=wamount}; 
 (* SQL.update Employee
      (*do:*)    (fun u -> begin u.e_sal <- wamount; end)    
      (*where:*) (fun u -> u.e_id > wsrc_id); 
*)


















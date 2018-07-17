let unimpl () = failwith "Unimpl"
let print x = ()

module U = Unix

type table_name = 
  | Bankaccount

type column_name = 
  |B_all |B_id |B_owner |B_bal
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
type bankaccount = {b_id: int; mutable b_owner: string; mutable b_bal: int}





let status_txn (ac_id:int) (ac_id2:int) =
  let v1 = SQL.select1 Bankaccount B_bal 
      (fun u -> (u.b_id = ac_id)) in
  let v2 = SQL.select1 Bankaccount B_bal 
      (fun u -> (u.b_id = ac_id2)) in
  ()




let deposit_txn (ac_id:int) = 
  SQL.update Bankaccount
    (fun u -> begin u.b_bal <- 100; end)
    (fun u -> (u.b_id = ac_id))












(*
(*TXN2*)
let deposit_txn (input:int) =  
 
  let v1 = SQL.select Employee E_sal
                   (fun u -> (u.e_id > 100) || (u.e_id < 200)) in 
  
  SQL.update Employee
    (*do:*)    (fun u -> begin u.e_sal <- 200; end)    
      (*where:*) (fun u -> u.e_id = 100)
      *)





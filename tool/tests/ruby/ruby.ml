let unimpl () = failwith "Unimpl"
let print x = ()

module U = Unix

type table_name = 
  | Account

type column_name = 
  |A_all |A_id |A_owner |A_balance


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
type account = {a_id: int; mutable a_owner: string; mutable a_balance: int}


(*TXN2*)
let withdraw_txn (input:int) =  
 
  let at__all_acs = SQL.select Account A_all
                   (fun a -> 1=1) in 
  let at__kia_acs = SQL.select Account A_all
                   (fun a -> a.a_owner = "Kia" ) in
  let at__ac1 = SQL.choose (fun a -> 1=1) at__kia_acs in
  
  SQL.update Account
    (*do:*)    (fun a -> begin a.a_balance <- a.a_balance - 100; end)
    (*where:*) (fun a -> a.a_id = at__ac1.a_id)





























































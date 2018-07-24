let unimpl () = failwith "Unimpl"
let print x = ()

module U = Unix

type table_name = 
  | Bankaccount

type column_name = 
  |B_all |B_id |B_owner |B_bal


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


(*TXN 1*)
let update_txn (ac_id:int) = 
  let v1 = SQL.select1 Bankaccount B_bal 
      (fun u -> (u.b_id = ac_id)) in
  SQL.update Bankaccount
        (fun u -> begin u.b_bal <- v1.b_bal; end)
        (fun u -> (u.b_id = v1.b_id));





















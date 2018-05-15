let unimpl () = failwith "Unimpl"
let print x = ()

module U = Unix

type table_name = 
  | Bankaccount

(* Definition of SimpSQL *)
module SQL : 
sig
  val select1: table_name list -> ('a -> bool) -> 'a
  val select: table_name list -> ('a -> bool) -> 'a list
  val insert: table_name -> 'a -> unit
  val delete: table_name -> ('a -> bool) -> unit
  val update: table_name -> ('a -> unit) -> ('a -> bool) -> unit
end = 
struct
  let select = unimpl ()
  let select1 = unimpl ()
  let insert = unimpl ()
  let delete = unimpl ()
  let update = unimpl ()
end

module S = struct
  include List
  let size = length
  let foreach = iter
  let max f l = unimpl ()
  let min f l = unimpl ()
  let sum f l = unimpl ()
end


(*Tabel Definitions*)
type bankaccount = {b_id: int; mutable b_bal: int}

(*TXN1*)
let deposit_txn (src_id:int) (dst_id:int) amount =  
           let acc_src = SQL.select1 [Bankaccount]  (fun u -> u.b_id = src_id) in
           let acc_dst = SQL.select1 [Bankaccount]  (fun u -> u.b_id = dst_id) in
           SQL.update Bankaccount
            (*do:*)    (fun u -> begin u.b_bal <- (acc_src.b_bal - amount); end)
            (*where:*) (fun u -> u.b_id = src_id);
           SQL.update Bankaccount
            (*do:*)    (fun u -> begin u.b_bal <- (acc_dst.b_bal + amount); end)
            (*where:*) (fun u -> u.b_id = dst_id)



        


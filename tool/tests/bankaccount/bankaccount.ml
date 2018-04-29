let unimpl () = failwith "Unimpl"
let print x = ()

module U = Unix

type table_name = 
  | Bankaccount
  | Student
  | Department
  | Habiba

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
type bankaccount = {mutable accID: int; mutable accBal: int}
type student = {mutable studentID: int; mutable studentName: string; mutable studentGrade: int; mutable studentIsNew: bool}
type department = {mutable departmentID: int; mutable departmentName: string; mutable departmentCode: int; mutable departmentAddress: string}
type habiba = {mutable habibaID: int; mutable habibaName: string; mutable habibaIsCute: bool; mutable habibaLevelofCuteness: int}

(*TXN1*)
let deposit_txn b_id amount =  
           let bal = SQL.select1 [Bankaccount]  (fun u -> u.accID = b_id) in
           SQL.update Bankaccount
           (fun u -> begin u.accBal <- (bal.accBal+amount); end)
           (fun u -> u.accID = b_id)


        


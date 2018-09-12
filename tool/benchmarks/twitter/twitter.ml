let unimpl () = failwith "Unimpl"

type table_name = 
  |User_profiles |Followers |Follows |Tweets |Added_tweets


type column_name = 
  |U_all |U_uid |U_name |U_email |U_partitionid |U_partitionid2  |U_followers
  |FR_all|FR_f1 |FR_f2
  |FS_all|FS_f1 |FS_f2
  |T_all |T_id  |T_uid  |T_text  |T_createdate
  |AT_all|AT_id |AT_uid |AT_text |AT_createdate

module SQL: 
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

(*----------------------------------------------------------------------------------------------------*)
type user_profiles = {uid:int; mutable name:string; mutable email:string; mutable partitionid:int; mutable partitionid2:int; mutable followers:int}
type followers = {f1:int; f2:int}
type follows = {f1:int; f2:int}
type tweets = {id:int; mutable uid:int; mutable text:string; mutable createdate:string}
type added_tweets = {id:int; mutable uid:int; mutable text:string; mutable createdate:string}
(*----------------------------------------------------------------------------------------------------*)


(*--------------------*)
(*TXN1*)
let get_followers_txn (input_uid:int) = 
  let v1 = SQL.select Followers FR_f2 (fun u->u.f1=input_uid) in 
  SQL.foreach v1
    begin fun v1_loop_var_1 ->
      (*get last names*)
      let v2 = SQL.select1 User_profiles U_name (fun u->u.uid=v1_loop_var_1.f2) in
      ()
    end

(*--------------------*)
(*TXN2*)
let get_tweet_txn (input_tweet_id:int) =
  let v1 = SQL.select1 Tweets T_all (fun u -> u.id=input_tweet_id) in
  ()

(*--------------------*)
(*TXN3*)
let get_tweet_from_following_txn (input_uid:int) =
  let v1 = SQL.select Follows FS_f2 (fun u -> u.f1 = input_uid ) in
  SQL.foreach v1
    begin fun v1_loop_var_1 -> 
      (*get tweet lists*)
      let v2 = SQL.select Tweets T_all (fun u-> u.uid = v1_loop_var_1.f2) in
      ()
    end

(*--------------------*)
(*TXN4*)
let get_user_tweets_txn (input_uid:int) =
  let v1 = SQL.select Tweets T_all (fun u -> u.uid = input_uid) in
  ()

(*--------------------*)
(*TXN5*)
let insert_tweet_txn (input_uid:int)(input_text:string)(input_time:string) =
  let v1 = SQL.select1 Tweets T_id (fun u -> 1=1) in
  SQL.insert Tweets {id=v1.id+1; uid=input_uid; text=input_text; createdate=input_time}
  

































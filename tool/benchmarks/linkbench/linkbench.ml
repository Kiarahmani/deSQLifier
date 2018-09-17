let unimpl () = failwith "Unimpl"

type table_name = 
  |Link_table |Count_table |Node_table


type column_name = 
  |L_all |L_id1 |L_id2 |L_linkType |L_visibility |L_data |L_time |L_version 
  |C_all |C_id |C_linkType |C_count |C_time |C_version 
  |N_all |N_id |N_type |N_version |N_time |N_data

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
type link_table = {l_id1:int; l_id2:int; l_link_type:int; mutable l_visibility:int; mutable l_data:string; mutable l_time:int; mutable
                    l_version:int; mutable l_exists:bool}
type count_table = {c_id:int; c_link_type:int; mutable c_count:int; mutable c_time:int; mutable c_version:int; mutable c_exists:bool}
type node_table = {n_id:int; mutable n_type:int; mutable n_version:int; mutable n_time:int; mutable n_data:string}
(*----------------------------------------------------------------------------------------------------*)



(*--------------------*)
(*TXN1*)
let add_link_txn (input_id1:int)(input_id2:int)(input_link_type:int)(input_visibility:int)(input_time:int)(input_version:int) = 
  let v1 = SQL.select1 Link_table L_all (fun u->u.l_id1=input_id1&&u.l_id2=input_id2&&u.l_link_type=input_link_type) in
  if (v1.l_exists=true)
  then (
      if (v1.l_visibility!=input_visibility)
      then (
        SQL.update Link_table
        (*do:*)    (fun u -> begin u.l_visibility <- input_visibility; end)
        (*where:*) (fun u -> u.l_id1=input_id1&&u.l_id2=input_id2&&u.l_link_type=input_link_type))
      else (
        SQL.update Link_table
        (*do:*)    (fun u -> begin u.l_data <- "HEXDATA"; end)
        (*where:*) (fun u -> u.l_id1=input_id1&&u.l_id2=input_id2&&u.l_link_type=input_link_type))
  )
  else (
    SQL.insert Link_table {l_id1=input_id1; l_id2=input_id2; l_link_type=input_link_type; l_visibility=input_visibility; l_data="HEXDATA";
                          l_time=input_time; l_version=input_version; l_exists=true};
    let v2 = SQL.select1 Count_table C_all (fun u->u.c_id=input_id1&&u.c_link_type=input_link_type) in
    if (v2.c_exists=true)
    then (
    SQL.update Count_table
      (*do:*)    (fun u -> begin u.c_version <- v2.c_version+1; end)
      (*where:*) (fun u -> u.c_id=input_id1&&u.c_link_type=input_link_type);
    SQL.update Count_table
      (*do:*)    (fun u -> begin u.c_count <- v2.c_count+1; end)
      (*where:*) (fun u -> u.c_id=input_id1&&u.c_link_type=input_link_type)
    )  
    else(
      SQL.insert Count_table {c_id=input_id1; c_link_type=input_link_type; c_count=1; c_time=input_time; c_version=0; c_exists=true}
    )
  )

(*--------------------*)
(*TXN2*)
let add_node_txn (input_type:int)(input_version:int)(input_time:int) = 
  let v1 = SQL.select1 Node_table N_id (fun u -> 1=1) in
  SQL.insert Node_table {n_id=v1.n_id+1; n_type=input_type; n_version=input_version; n_time=input_time; n_data="HEXDATA"}


(*--------------------*)
(*TXN3*)
let count_link_txn (input_id1:int)(input_link_type:int) = 
  let v1 = SQL.select Count_table C_all (fun u -> u.c_id=input_id1&&u.c_link_type=input_link_type) in
  ()

(*--------------------*)
(*TXN4*)
let delete_link_txn (input_id1:int)(input_id2:int)(input_link_type:int)(input_expunge:bool)(input_time:int) = 
  let v1 = SQL.select1 Link_table L_all (fun u -> u.l_id1=input_id1&&u.l_id2=input_id2&&u.l_link_type=input_link_type) in
  let v2 = SQL.select1 Count_table C_id (fun u -> u.c_id=input_id1&&u.c_link_type=input_link_type) in
  if (v1.l_visibility=1&&v1.l_exists=true)
  then (
    if (input_expunge=true)
    then (
      SQL.delete Link_table (fun u -> u.l_id1=input_id1&&u.l_id2=input_id2&&u.l_link_type=input_link_type));
    if (input_expunge=false)
    then (
      SQL.update Link_table 
        (fun u-> u.l_visibility<-0)
        (fun u-> u.l_id1=input_id1&&u.l_id2=input_id2&&u.l_link_type=input_link_type))
  );
  if (v2.c_exists=true)
  then (
    SQL.update Count_table 
      (fun u -> (u.c_version<-v2.c_version+1))
      (fun u -> u.c_id=input_id1&&u.c_link_type=input_link_type)
  )
  else (
    SQL.insert Count_table {c_id=input_id1; c_link_type=input_link_type; c_count=0; c_time=input_time; c_version=0; c_exists=true}
  )

(*--------------------*)
(*TXN5*)
let delete_node_txn (input_id:int)(input_type:int) = 
  SQL.delete Node_table (fun u -> u.n_id=input_id&&u.n_type=input_type)

(*--------------------*)
(*TXN6*)
let get_link_txn (input_id1:int)(input_link_type:int)(input_id2_list: int list) = 
  SQL.foreach input_id2_list 
    begin fun input_id2_list_loop_var_1 ->    
      let v1 = SQL.select1 Link_table L_all (fun u -> u.l_id1=input_id1&&u.l_link_type=input_link_type&&u.l_id2=input_id2_list_loop_var_1)
      in ()
    end

(*--------------------*)
(*TXN7*)
let get_link_list_txn (input_visibility:int)(input_minTimestamp:int)(input_maxTimestamp:int)(input_id:int)(input_type:int) = 
  let v = SQL.select Link_table L_all (fun u ->
      u.l_id1=input_id&&u.l_link_type=input_type&&u.l_time>input_minTimestamp&&u.l_time<input_maxTimestamp&&u.l_visibility=input_visibility)
  in ()
    
(*--------------------*)
(*TXN8*)
let get_node_txn (input_id:int)(input_type:int) = 
  let v1 = SQL.select1 Node_table N_all (fun u -> u.n_id=input_id&&u.n_type=input_type)
  in ()

(*--------------------*)
(*TXN9*)
let update_link_txn (input_:int) = 
  ()

(*--------------------*)
(*TXN10*)
let update_node_txn (input_id:int)(input_type:int)(input_version:int)(input_time:int) = 
  SQL.update Node_table
    (fun u -> u.n_data <- "HEXDATA")
    (fun u -> u.n_id = input_id && u.n_type=input_type);
  SQL.update Node_table
    (fun u -> u.n_version <- input_version)
    (fun u -> u.n_id = input_id && u.n_type=input_type);
  SQL.update Node_table
    (fun u -> u.n_time <- input_time)
    (fun u -> u.n_id = input_id && u.n_type=input_type)


































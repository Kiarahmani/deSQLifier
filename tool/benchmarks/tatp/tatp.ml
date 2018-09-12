let unimpl () = failwith "Unimpl"

type table_name = 
  |Subscriber |Access_info |Special_facility |Call_forwarding


type column_name = 
  |S_all |S_id |S_sub_nbr |S_bit1 |S_bit2 |S_bit3 |S_bit4 |S_bit5 |S_bit6 |S_bit7 |S_bit8 |S_bit9 |S_bit10 |S_hex1 |S_hex2 |S_hex3 |S_hex4 |S_hex5 |S_hex6
  |S_hex7 |S_hex8 |S_hex9 |S_hex10 |S_byte2_1 |S_byte2_2 |S_byte2_3 |S_byte2_4 |S_byte2_5 |S_byte2_6 |S_byte2_7 |S_byte2_8 |S_byte2_9 |S_byte2_10
  |S_msc_location |S_vlr_location
  |A_all |A_s_id |A_type |A_data1 |A_data2 |A_data3 |A_data4 
  |SF_all |SF_s_id |SF_type |SF_is_active |SF_error_cntrl |SF_data_a |SF_data_b
  |C_all |C_s_id |C_sf_type |C_start_time |C_end_time |C_numberx

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
type subscriber  = {s_id:int; mutable sub_nbr:string; mutable bit_1:int; mutable bit_2:int; mutable bit_3:int; mutable bit_4:int; mutable bit_5:int; 
                    mutable bit_6:int; mutable bit_7:int; mutable bit_8:int; mutable bit_9:int; mutable bit_10:int; mutable hex_1:int; 
                    mutable hex_2:int; mutable hex_3:int; mutable hex_4:int; mutable hex_5:int; mutable hex_6:int; mutable hex_7:int; 
                    mutable hex_8:int; mutable hex_9:int; mutable hex_10:int; mutable byte2_1:int; mutable byte2_2:int; mutable byte2_3:int; 
                    mutable byte2_4:int; mutable byte2_5:int; mutable byte2_6:int; mutable byte2_7:int; mutable byte2_8:int; mutable byte2_9:int; 
                    mutable byte2_10:int; mutable msc_location:int; mutable vlr_location:int; mutable exists:bool}
type access_info  = {ai_s_id:int; ai_type:int; mutable ai_data1:int; mutable ai_data2:int; mutable ai_data3:int; mutable ai_data4:int; }
type special_facility  = {sf_s_id:int; sf_type:int; mutable sf_is_active:int; mutable sf_error_cntrl:int; mutable sf_data_a:int; mutable
                           sf_data_b:string}
type call_forwarding  = {cf_s_id:int; cf_sf_type:int; cf_start_time:int; mutable cf_end_time:int; mutable cf_numberx:string}
(*----------------------------------------------------------------------------------------------------*)


(*--------------------*)
(*TXN1*)
let delete_call_forwarding_txn (input_sub_nbr:string)(input_sf_type:int)(input_start_time:int) =
  let v1 = SQL.select Subscriber S_id (fun u->u.sub_nbr=input_sub_nbr) in
  let result = SQL.choose (fun u-> 1=1) v1 in 
  if (result.exists=true)
  then (
    SQL.delete Call_forwarding (fun u -> u.cf_s_id=result.s_id && u.cf_sf_type=input_sf_type && u.cf_start_time=input_start_time)
  )

(*--------------------*)
(*TXN2*)
let get_access_data_txn (input_s_id:int) (input_ai_type:int) =
  let v1 = SQL.select1 Access_info A_all (fun u -> u.ai_s_id=input_s_id && u.ai_type=input_ai_type) in
  ()

(*--------------------*)
(*TXN3*)
let get_new_destination_txn (input_s_id:int) (input_sf_type:int) (input_start_time:int) (input_end_time:int) = 
  let v1 = SQL.select1 Special_facility S_all (fun u -> u.sf_s_id=input_s_id && u.sf_type=input_sf_type && u.sf_is_active = 1) in
  let v2 = SQL.select Call_forwarding C_numberx (fun u -> u.cf_s_id=input_s_id && u.cf_sf_type=input_sf_type && u.cf_start_time < input_start_time &&
                                                u.cf_end_time > input_end_time) in
  ()

(*--------------------*)
(*TXN4*)
let get_subscriber_data_txn (input_s_id:int) =
  let v1 = SQL.select1 Subscriber S_all (fun u -> u.s_id=input_s_id) in
  ()

(*--------------------*)
(*TXN5*)
let insert_call_forwarding_txn (input_sub_nbr:string)(input_sf_type:int)(input_start_time:int)(input_end_time:int)(input_numberx:string)  =
  let v1 = SQL.select Subscriber S_id (fun u->u.sub_nbr=input_sub_nbr) in
  let result = SQL.choose (fun u-> 1=1) v1 in 
  if (result.exists=true)
  then (
    let v2 = SQL.select Special_facility SF_type (fun u -> u.sf_s_id = result.s_id) in
    SQL.insert Call_forwarding {cf_s_id=result.s_id; cf_sf_type=input_sf_type; cf_start_time=input_start_time; cf_end_time=input_end_time;
                                cf_numberx=input_numberx}
  )

(*--------------------*)
(*TXN6*)
let update_location_txn (input_location:int) (input_sub_nbr:string) =
  let v1 = SQL.select Subscriber S_id (fun u->u.sub_nbr=input_sub_nbr) in
  let result = SQL.choose (fun u-> 1=1) v1 in 
  if (result.exists=true)
  then (
    SQL.update Subscriber
        (*do:*)    (fun u -> begin u.vlr_location <- input_location; end)
        (*where:*) (fun u -> u.s_id = result.s_id)
  )


(*--------------------*)
(*TXN7*)
let update_subscriber_data_txn (input_s_id:int) (input_bit_1:int)(input_data_a:int)(input_sf_type:int) =
    SQL.update Subscriber
        (*do:*)    (fun u -> begin u.bit_1 <- input_bit_1; end)
      (*where:*) (fun u -> u.s_id = input_s_id);
    SQL.update Special_facility
        (*do:*)    (fun u -> begin u.sf_data_a <- input_data_a; end)
      (*where:*) (fun u -> u.sf_s_id = input_s_id && u.sf_type = input_sf_type);
    






































let unimpl () = failwith "Unimpl"

type table_name = 
  | Country | Airport | Airport_distance
  | Airline | Customer| Frequent_flyer 
  | Flight  | Reservation

type column_name = 
  |C_id |C_name |C_code2 |C_code3 |C_all
  |A_id |A_code |A_name  |A_city |A_postalcode |A_cid |A_longitude |A_latitude |A_gmtoffset |A_wac |A_all
  |AD_id0 |AD_id1 |AD_distance |AD_all
  |AL_id |AL_iatacode |AL_icaocode |AL_callsign |AL_name |AL_cid |AL_info |AL_all
  |CU_id |CU_baseapid |CU_name |CU_balance |CU_info |CU_all
  |FF_cuid |FF_alid |FF_info |FF_all
  |F_id |F_alid |F_departapid |F_departtime |F_arriveapid |F_arrivetime |F_status |F_seatsleft |F_baseprice |F_seatstotal |F_all
  |R_id |R_cuid |R_fid |R_seat |R_info |R_reserved |R_all

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
type country = {c_id:int; mutable c_name:string; mutable c_code2:int;mutable c_code3:int}
type airport = {a_id:int; mutable a_code:int; mutable a_name:string; mutable a_city:string; mutable a_postalcode:int; mutable a_cid:int; mutable a_longitude:int; mutable a_gmtoffset:int; mutable a_wac:string}
type airport_distance = {ad_id0:int; ad_id1:int; mutable ad_distance:int}
type airline = {al_id:int; mutable al_iatacode:string; mutable al_icaocode:string; mutable al_callsign:string; mutable al_name:string; mutable al_cid:int; mutable al_info:string}
type customer = {cu_id:int; mutable cu_baseapid:int; mutable cu_name:string; mutable cu_balance:int; mutable cu_info:string}
type frequent_flyer = {ff_cuid:int; ff_alid:int; mutable ff_info:string}
type flight = {f_id:int; mutable f_alid:int; mutable f_departapid:int; mutable f_departtime:int; mutable f_arriveapid:int; mutable f_arrivetime:int; mutable f_status:string; mutable f_seatsleft:int; mutable f_baseprice:int; mutable f_seatstotal:int}
type reservation = {r_id:int; r_cuid:int; r_fid:int; mutable r_seat:string; mutable r_info:string; mutable r_reserved:bool}
(*----------------------------------------------------------------------------------------------------*)


(*--------------------*)
(*TXN1: UpdateReservation*)
let update_reservation_txn (input_r_id:int) (input_f_id:int) (input_cu_id:int) (input_seatnum:string) (input_attr_idx:int) (input_attr_val:string) = 
  (*pull the reservation from the database*)
  let v = SQL.select Reservation R_id (fun u -> (u.r_fid=input_f_id)&&(u.r_seat=input_seatnum)) in
  let v0 = SQL.choose (fun u -> 1=1) v in
  if (v0.r_reserved=true) (* make sure seat not already reserved *)
  then ()
  else
    let v1 = SQL.select Reservation R_id (fun u -> (u.r_fid=input_f_id)&&(u.r_cuid=input_cu_id)) in 
    let v4 = SQL.choose (fun u -> 2=2) v1 in
    if (v4.r_reserved=true) (* make sure customer already does not have a reservation *) 
    then 
      ()
    else  
      SQL.insert Reservation  {r_id=input_r_id; r_cuid=input_cu_id; r_fid=input_f_id; r_seat=input_seatnum; r_info=""; r_reserved=true}



(*--------------------*)
(*TXN2: UpdateCustomer*)
let update_customer_txn (input_cu_id:int) (input_cu_name:string) (input_cuid_given:bool) (input_ff_given:bool) (input_update_ff:int) (input_info:string) =
  if (input_cuid_given)
  then
   (let v1 = SQL.select1 Customer CU_id (fun u -> u.cu_id = input_cu_id) in (*customer*)
    let v2 = SQL.select1 Airport A_all (fun u -> u.a_cid = v1.cu_baseapid) in (*airport*)
    let v3 = SQL.select1 Country C_all (fun u -> u.c_id = v2.a_cid) in (*country*)
    SQL.update Customer
        (*do:*)    (fun u -> begin u.cu_info <- input_info; end)
        (*where:*) (fun u -> u.cu_id = input_cu_id);
    if (input_ff_given)
    then 
      let v4 = SQL.select Frequent_flyer F_alid (fun u -> u.ff_cuid = input_cu_id)  in
      let v5 = SQL.choose (fun u -> 1=1) v4 in
      SQL.update Frequent_flyer 
        (*do:*)    (fun u -> begin u.ff_info <- input_info; end)   
        (*where:*) (fun u -> u.ff_cuid = input_cu_id && u.ff_alid = v5.ff_alid)
   )
  else 
   (let ve0 = SQL.select Customer CU_id (fun u -> u.cu_name = input_cu_name) in
    let ve1 = SQL.choose (fun u -> 1=1) ve0 in
    let ve2 = SQL.select1 Airport A_all (fun u -> u.a_cid = ve1.cu_baseapid) in (*airport*)
    let ve3 = SQL.select1 Country C_all (fun u -> u.c_id = ve2.a_cid) in (*country*)
    SQL.update Customer
        (*do:*)    (fun u -> begin u.cu_info <- input_info; end)
        (*where:*) (fun u -> u.cu_id = ve1.cu_id);
    if (input_ff_given)
    then 
      let ve4 = SQL.select Frequent_flyer FF_alid (fun u -> u.ff_cuid = ve1.cu_id)  in
      let ve5 = SQL.choose (fun u -> 1=1) ve4 in
      SQL.update Frequent_flyer 
        (*do:*)    (fun u -> begin u.ff_info <- input_info; end)   
        (*where:*) (fun u -> u.ff_cuid = ve1.cu_id && u.ff_alid = ve5.ff_alid)
   )

(*--------------------*)
(*TXN3: FindOpenSeats*)  (*Read Only*)
let find_open_seats_txn (input_f_id:int) =
  let v1 = SQL.select1 Flight F_all (fun u -> u.f_id=input_f_id) in
  (*NO DB ACCESS: compute the price based on the availability*)
  let v2 = SQL.select Reservation R_all (fun u -> u.r_fid=input_f_id) in
  (*NO DB ACCESS: for each seat that is not reserved print the info *)
  ()
 

(*--------------------*)
(*TXN4: DeleteReservation*)
let delete_reservation_txn (input_f_id:int) (input_cu_id:int) (input_ff_alid:int) (input_cu_name:string) (input_cuname_given:bool) (input_cuid_given:bool) =
  if (input_cuid_given)
  then (
    let v1 = SQL.select1 Customer C_all (fun u -> u.cu_id = input_cu_id) in
    let v2 = SQL.select1 Flight F_all   (fun u -> u.f_id = input_f_id) in
    let v3 = SQL.select Reservation R_all (fun u -> u.r_fid = input_f_id && u.r_cuid = input_cu_id ) in
    let v4 = SQL.choose (fun u -> 1=1) v3 in
    if (v4.r_reserved=true)
    then 
      SQL.delete Reservation (fun u -> u.r_fid=input_f_id && u.r_cuid=input_cu_id && u.r_id=v4.r_id);
      SQL.update Flight   
              (*do:*)    (fun u -> begin u.f_seatsleft <- v2.f_seatsleft+1; end)
              (*where:*) (fun u -> u.f_id = input_f_id);
      SQL.update Customer
              (*do:*)    (fun u -> begin u.cu_balance <- v1.cu_balance - 1;end)
              (*where:*) (fun u -> u.cu_id = input_cu_id);
      SQL.update Customer
              (*do:*)    (fun u -> begin u.cu_info <- "update";end)
              (*where:*) (fun u -> u.cu_id = input_cu_id);
      SQL.update Frequent_flyer
              (*do:*)    (fun u -> begin u.ff_info <- "update";end)
              (*where:*) (fun u -> u.ff_cuid = input_cu_id && u.ff_alid = input_ff_alid)
  )
  else 
    if (input_cuname_given)
    then (
      let vn0 = SQL.select Customer C_all (fun u -> u.cu_name = input_cu_name) in
      let vn1 = SQL.choose (fun u -> 1=1) vn0 in
      let vn2 = SQL.select1 Flight F_all   (fun u -> u.f_id = input_f_id) in
      let vn3 = SQL.select Reservation R_all (fun u -> u.r_fid = input_f_id && u.r_cuid =  vn1.cu_id) in
      let vn4 = SQL.choose (fun u -> 1=1) vn3 in
      if (vn4.r_reserved=true)
      then 
        SQL.delete Reservation (fun u -> u.r_fid=input_f_id && u.r_cuid=vn1.cu_id && u.r_id=vn4.r_id);
        SQL.update Flight   
                (*do:*)    (fun u -> begin u.f_seatsleft <- vn2.f_seatsleft+1; end)
                (*where:*) (fun u -> u.f_id = input_f_id);
        SQL.update Customer
                (*do:*)    (fun u -> begin u.cu_balance <- vn1.cu_balance - 1;end)
                (*where:*) (fun u -> u.cu_id = vn1.cu_id);
        SQL.update Customer
                (*do:*)    (fun u -> begin u.cu_info <- "update";end)
                (*where:*) (fun u -> u.cu_id = vn1.cu_id);
        SQL.update Frequent_flyer
                (*do:*)    (fun u -> begin u.ff_info <- "update";end)
                (*where:*) (fun u -> u.ff_cuid = vn1.cu_id && u.ff_alid = input_ff_alid)
    )
    else () (*similar: does not affect the DB access*)
          



(*--------------------*)
(*TXN5: FindFlights*) (*Read Only*)
let find_flights_txn (input_distance:int) (input_depart_aid:int) (input_start_date:int) (input_end_date:int) =
  let v1 = SQL.select Airport_distance AD_all (fun u -> u.ad_id1 = input_depart_aid && u.ad_distance < input_distance)  in
  let v2 = SQL.choose (fun u -> 1=1) v1 in (*arbitrarily selected nearby airport*) 
  let v3 = SQL.select Flight F_all (fun u -> u.f_departapid = input_depart_aid && u.f_departtime > input_start_date && u.f_arrivetime < input_end_date
                                    && u.f_arriveapid = v2.ad_id1) in 
  SQL.foreach v3
    begin fun loop_var_1 -> 
      let v4 = SQL.select1 Airline AL_all (fun u -> u.al_id = loop_var_1.f_alid) in
      (*departure info*)
      let v5 = SQL.select1 Airport A_all (fun u -> u.a_id = loop_var_1.f_departapid) in
      let v6 = SQL.select1 Country C_all (fun u -> u.c_id = v5.a_cid) in 
      (*arrival info*)
      let v7 = SQL.select1 Airport A_all (fun u -> u.a_id = loop_var_1.f_arriveapid) in
      let v8 = SQL.select1 Country C_all (fun u -> u.c_id = v7.a_cid) in 
      ()
    end




(*--------------------*)
(*TXN6: NewReservation*)
let new_reservation_txn (input_f_id:int) (input_seatnum:string) (input_cu_id:int) (input_r_id:int)= 
  let v1  = SQL.select1 Flight F_seatsleft (fun u -> u.f_id=input_f_id) in
  let v2  = SQL.select1 Flight F_alid (fun u -> u.f_id=input_f_id) in
  let v3  = SQL.select1 Airline AL_all (fun u -> u.al_id=v2.f_alid) in
  if (v1.f_seatsleft>0)
  then 
    let checkseats = SQL.select Reservation R_reserved (fun u -> u.r_fid = input_f_id && u.r_seat = input_seatnum) in
    let checkseat = SQL.choose (fun u -> 1=1) checkseats in
    if (checkseat.r_reserved=true)
    then ()
    else 
      let checkcusts = SQL.select Reservation R_reserved (fun u -> u.r_fid = input_f_id && u.r_cuid = input_cu_id) in
      let checkcust = SQL.choose (fun u -> 1=1) checkcusts in
      if (checkcust.r_reserved=true)
      then ()
      else
        let cust = SQL.select1 Customer CU_all (fun u -> u.cu_id = input_cu_id) in
        SQL.insert Reservation {r_id=input_r_id; r_cuid=input_cu_id; r_fid=input_f_id; r_seat=input_seatnum; r_info=""; r_reserved=true};
        let vs2 = SQL.select1 Flight F_seatsleft (fun u -> u.f_id=input_f_id) in
        SQL.update Flight   
                (*do:*)    (fun u -> begin u.f_seatsleft <- vs2.f_seatsleft-1; end)
                (*where:*) (fun u -> u.f_id = input_f_id);
        SQL.update Customer
                (*do:*)    (fun u -> begin u.cu_info <- "update";end)
                (*where:*) (fun u -> u.cu_id = cust.cu_id);
        let vff1 = SQL.select1 Frequent_flyer FF_info (fun u -> u.ff_cuid=input_cu_id && u.ff_alid = v2.f_alid) in
        SQL.update Frequent_flyer
                (*do:*)    (fun u -> begin u.ff_info <- "update";end)
                (*where:*) (fun u -> u.ff_cuid = input_cu_id && u.ff_alid = v2.f_alid)

    
  










































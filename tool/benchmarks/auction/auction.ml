let unimpl () = failwith "Unimpl"

type table_name = 
  |Region |Global_attribute_group
  |Global_attribute_value |Category
  |User |User_attributes |Item
  |Item_image |Item_comment |Item_bid
  |Item_feedback |Item_max_bid
  |Item_purchase |User_items |Post_auction_args


type column_name = 
  |R_id |R_name  |R_all
  |AG_id|AG_cid  |AG_name |AG_all
  |AV_id|AV_agid |AV_name |AV_all
  |C_id |C_name  |C_parentid |C_all
  |U_id |U_rating|U_balance |U_created |U_rid |U_all
  |UA_id|UA_uid  |UA_name |UA_value |UA_created |UA_all
  |I_id |I_uid   |I_cid |I_name |I_description |I_initprice |I_currprice |I_numbids |I_numimages |I_numgattrs |I_startdate |I_enddate |I_status |I_all
  |II_id|II_iid  |II_uid |II_path |II_all
  |IC_id|IC_iid  |IC_uid |IC_buyerid |IC_date |IC_question |IC_response |IC_all
  |IF_id|IF_iid  |IF_uid |IF_buyerid |IF_rating |IF_date |IF_comment |IF_all
  |IB_id|IB_iid  |IB_uid |IB_buyerid |IB_bid |IB_maxbid |IB_created |IB_updated |IB_all
  |MB_iid |MB_uid|MB_ibid|MB_ibiid |MB_ibuid |MB_created |MB_updated|MB_all
  |IP_id|IP_ibid |IP_iid |IP_uid |IP_date |IP_all 
  |UI_uid |UI_iid|UI_sellerid |UI_created |UI_all
  |PA_iid |PA_sellerid |PA_buyerid |PA_ibid |PA_all

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
type region  = {r_id:int; mutable r_name:string}
type global_attribute_group  = {ag_id:int; mutable ag_cid:int; mutable ag_name:string}
type global_attribute_value  = {av_id:int; av_agid:int; mutable av_name:string}
type category  = {c_id:int; mutable c_name:string; mutable c_parentid:int}
type user  = {u_id:int; mutable u_rating:int; mutable u_balance:int; mutable u_created:int; mutable u_rid:int}
type user_attributes = {ua_id:int; ua_uid:int; mutable ua_name:string; mutable ua_value:int; mutable ua_created:string}
type item = {i_id:int; i_uid:int; mutable i_cid:int; mutable i_name:string; mutable i_description:string; mutable i_initprice:int; mutable i_currprice:int; mutable i_numbids:int; mutable i_numimages:int; mutable i_numgattrs:int; mutable i_startdate:string; mutable
              i_enddate:string; mutable i_status:bool}
type item_image = {ii_id:int; ii_iid:int; ii_uid:int; mutable ii_path:string}
type item_comment = {ic_id:int; ic_iid:int; ic_uid:int; mutable ic_buyerid:int; mutable ic_date:string; mutable ic_question:string; mutable ic_response:string}
type user_feedback  = {uf_uid:int; uf_iid:int; uf_iuid:int; uf_fromid:int; mutable uf_rating:int; mutable uf_date:string; mutable uf_comment:string}
type item_bid = {ib_id:int; ib_iid:int; ib_uid:int; mutable ib_buyerid:int; mutable ib_bid:int; mutable ib_maxbid:int; mutable ib_created:string; mutable ib_updated:string}
type item_max_bid = {mb_iid:int; mb_uid:int; mutable mb_ibiid:int; mutable mb_ibuid:int; mutable mb_created:string; mutable mb_updated:string}
type item_purchase = {ip_id:int; ip_ibid:int; ip_iid:int; ip_uid:int; mutable ip_date:string}
type user_items = {ui_uid:int; ui_iid:int; mutable ui_sellerid:int; mutable ui_created:string}
type post_auction_args = {pa_iid:int; pa_sellerid:int; pa_buyerid:int; mutable pa_ibid:int}
(*----------------------------------------------------------------------------------------------------*)


(*--------------------*)
(*TXN1: NewUser*)
let new_user_txn (input_uid:int) (input_rid:int) =
  SQL.insert User {u_id=input_uid; u_rating=0; u_balance=0; u_created=0; u_rid=input_rid}




(*--------------------*)
(*TXN2: NewItem*)
let new_item_txn (input_i_id:int)(input_u_id:int)(input_c_id:int)(input_ag_ids: int list)(input_name:string)(input_init_price:int)(input_num_images:int)
    (input_ag_ids_length:int ) (input_image_paths:string list) (input_start_date:string) (input_end_date:string) = 
  SQL.foreach input_ag_ids
    begin fun loop_var_1 -> 
      let v1 = SQL.select1 Global_attribute_group AG_name (fun u -> u.ag_id = loop_var_1) in
      ()
    end;
(*  SQL.insert Item {i_id=input_i_id; i_uid=input_u_id; i_cid=input_c_id; i_name=input_name; i_description="description"; i_initprice=input_init_price;
                   i_currprice=input_init_price; i_numbids=0; i_numimages=input_num_images; i_numgattrs=input_ag_ids_length; i_startdate=input_start_date; 
                    i_enddate=input_end_date; i_status=true};
   
  SQL.foreach input_image_paths
    begin fun loop_var_2 ->
      ()
    end
*)

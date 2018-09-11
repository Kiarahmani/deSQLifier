let unimpl () = failwith "Unimpl"

type table_name = 
  |Region |Global_attribute_group
  |Global_attribute_value |Category
  |User |User_attributes |Item
  |Item_image |Item_comment |Item_bid
  |User_feedback |Item_max_bid
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
  |UF_id|UF_iid  |UF_uid |UF_buyerid |UF_rating |UF_date |UF_comment |UF_all
  |IB_id|IB_iid  |IB_uid |IB_buyerid |IB_bid |IB_maxbid |IB_created |IB_updated |IB_all
  |MB_iid |MB_uid|MB_ibid|MB_ibiid |MB_ibuid |MB_created |MB_updated|MB_exists |MB_all
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
type item = {i_id:int; i_uid:int; mutable i_cid:int; mutable i_name:string; mutable i_description:string; mutable i_initprice:int; mutable i_currprice:int; mutable i_numbids:int; mutable i_numimages:int; mutable i_numgattrs:int; mutable i_startdate:int; mutable
              i_enddate:int; mutable i_status:bool}
type item_image = {ii_id:int; ii_iid:int; ii_uid:int; mutable ii_path:string}
type item_comment = {ic_id:int; ic_iid:int; ic_uid:int; mutable ic_buyerid:int; mutable ic_date:string; mutable ic_question:string; mutable ic_response:string}
type user_feedback  = {uf_uid:int; uf_iid:int; uf_iuid:int; uf_fromid:int; mutable uf_rating:int; mutable uf_date:string; mutable uf_comment:string}
type item_bid = {ib_id:int; ib_iid:int; ib_uid:int; mutable ib_buyerid:int; mutable ib_bid:int; mutable ib_maxbid:int; mutable ib_created:string; mutable ib_updated:string; mutable ib_exists:bool}
type item_max_bid = {mb_iid:int; mb_uid:int; mutable mb_ibid:int; mutable mb_ibiid:int; mutable mb_ibuid:int; mutable mb_created:string; mutable mb_updated:string; mutable mb_exists:bool}
type item_purchase = {ip_id:int; ip_ibid:int; ip_iid:int; ip_uid:int; mutable ip_date:string}
type user_items = {ui_uid:int; ui_iid:int; mutable ui_sellerid:int; mutable ui_created:string}
type post_auction_args = {pa_iid:int; pa_sellerid:int; pa_buyerid:int; mutable pa_ibid:int; mutable pa_exists:bool}
(*----------------------------------------------------------------------------------------------------*)


(*--------------------*)
(*TXN1: NewUser*)
let new_user_txn (input_uid:int) (input_rid:int) =
  SQL.insert User {u_id=input_uid; u_rating=0; u_balance=0; u_created=0; u_rid=input_rid}


(*--------------------*)
(*TXN2: NewItem*)
let new_item_txn (input_i_id:int)(input_u_id:int)(input_c_id:int)(input_ag_ids: int list)(input_name:string)(input_init_price:int)(input_num_images:int)
    (input_ii_id:int) (input_ag_ids_length:int ) (input_image_paths:string list) (input_start_date:int) (input_end_date:int) = 
  SQL.foreach input_ag_ids
    begin fun input_ag_ids_loop_var_1 -> 
      let v1 = SQL.select1 Global_attribute_group AG_name (fun u -> u.ag_id = input_ag_ids_loop_var_1) in
      ()
    end;
  SQL.insert Item {i_id=input_i_id; i_uid=input_u_id; i_cid=input_c_id; i_name=input_name; i_description="description"; i_initprice=input_init_price;
                   i_currprice=input_init_price; i_numbids=0; i_numimages=input_num_images; i_numgattrs=input_ag_ids_length; i_startdate=input_start_date; 
                    i_enddate=input_end_date; i_status=true};
   
  SQL.foreach input_image_paths
    begin fun input_image_paths_loop_var_1 ->
      SQL.insert Item_image {ii_id=input_ii_id; ii_iid=input_i_id; ii_uid=input_u_id; ii_path=input_image_paths_loop_var_1}
    end;
  let v2 = SQL.select1 User U_balance  (fun u -> (u.u_id = input_u_id)) in
  SQL.update User
        (*do:*)    (fun u -> begin u.u_balance <- v2.u_balance-1; end)
        (*where:*) (fun u -> u.u_id = input_u_id)



(*--------------------*)
(*TXN3: NewBid*)
let new_bid_txn (input_id:int) (input_uid:int) (input_buyer_id:int) (input_bid:int) (input_max_bid:int) =
  let v1 = SQL.select1 Item I_numbids (fun u -> u.i_id=input_id && u.i_uid = input_uid && u.i_status=false) in
  SQL.update Item
        (*do:*)    (fun u -> begin u.i_numbids <- v1.i_numbids ; end)
        (*where:*) (fun u -> u.i_id=input_id && u.i_uid = input_uid && u.i_status=false);
  let v2 = SQL.select Item_bid IB_id (fun u -> u.ib_iid=input_id && u.ib_uid=input_uid) in
  let b_id = SQL.choose (fun u -> 1=1) v2 in
  let v3 = SQL.select1 Item_max_bid MB_ibid (fun u -> u.mb_iid=input_id && u.mb_uid=input_uid) in
  if (v3.mb_exists=true)
  then (
    let v4 = SQL.select1 Item_bid IB_bid (fun u -> u.ib_id=v3.mb_ibiid && u.ib_iid=input_id && u.ib_uid=input_uid) in
    let v5 = SQL.select1 Item_bid IB_maxbid (fun u -> u.ib_id=v3.mb_ibiid && u.ib_iid=input_id && u.ib_uid=input_uid) in
    SQL.insert Item_bid {ib_id=b_id.ib_id; ib_iid=input_id; ib_uid=input_uid; ib_buyerid=input_buyer_id; ib_bid=input_bid; ib_maxbid=input_max_bid; ib_created="0"; ib_updated="0"; ib_exists=true};
    if (input_max_bid > v5.ib_maxbid)
    then (
      SQL.update Item_max_bid
        (*do:*)    (fun u -> begin u.mb_ibid <- input_id ; end)
        (*where:*) (fun u -> u.mb_iid=input_id && u.mb_uid=input_uid);
      SQL.update Item_max_bid
        (*do:*)    (fun u -> begin u.mb_ibiid <- b_id.ib_iid ; end)
        (*where:*) (fun u -> u.mb_iid=input_id && u.mb_uid=input_uid);
      SQL.update Item_max_bid
        (*do:*)    (fun u -> begin u.mb_ibuid <- input_uid; end)
        (*where:*) (fun u -> u.mb_iid=input_id && u.mb_uid=input_uid);
    )
    else (
      if (input_bid<v4.ib_bid)
      then( 
        SQL.update Item_bid
          (*do:*)    (fun u -> begin u.ib_bid <- input_bid; end)
          (*where:*) (fun u -> u.ib_id=v3.mb_ibid && u.ib_iid=input_id && u.ib_uid=input_uid);
      )
    )
  )
  else ( 
    SQL.insert Item_bid {ib_id=b_id.ib_id; ib_iid=input_id; ib_uid=input_uid; ib_buyerid=input_buyer_id; ib_bid=input_bid; ib_maxbid=input_max_bid; ib_created="0"; ib_updated="0"; ib_exists=true};
    SQL.insert Item_max_bid {mb_iid=input_id; mb_uid=input_uid; mb_ibid=input_id; mb_ibiid=b_id.ib_iid; mb_ibuid=input_uid; mb_created="0"; mb_updated="0"; mb_exists=true}
  )


(*--------------------*)
(*TXN4: NewComment*)
let new_comment_txn (input_i_id:int) (input_seller_id:int) (input_buyer_id:int) (input_question:string) =
  let v1 = SQL.select Item_comment IC_id (fun u -> u.ic_iid=input_i_id && u.ic_uid = input_seller_id) in
  let cid = SQL.choose (fun u -> 1=1) v1 in 
  SQL.insert Item_comment {ic_id=cid.ic_id+1; ic_iid=input_i_id; ic_uid=input_seller_id; ic_buyerid=input_buyer_id; ic_date=""; ic_question=input_question; ic_response=""} 



(*--------------------*)
(*TXN5: NewCommentResponse*)
let new_comment_response_txn (input_i_id:int) (input_ic_id:int) (input_seller_id:int) (input_response:string)= 
  SQL.update Item_comment
      (*do:*)    (fun u -> begin u.ic_response <- input_response; end)
      (*where:*) (fun u -> u.ic_id=input_ic_id && u.ic_iid=input_i_id && u.ic_uid=input_seller_id)


(*--------------------*)
(*TXN6: NewPurchase*)
let new_purchase_txn (input_b_id:int) (input_id:int) (input_u_id:int) (input_buyer_id:int) =
  let mb_id = SQL.select1 Item_max_bid MB_ibid (fun u -> u.mb_iid=input_id && u.mb_uid=input_u_id) in 
  let ib_buyer_id  = SQL.select1 Item_bid IB_buyerid (fun u -> u.ib_id=mb_id.mb_ibid && u.ib_iid=input_id && u.ib_uid=input_u_id) in
  if (mb_id.mb_ibid=input_b_id && ib_buyer_id.ib_buyerid=input_buyer_id)
  then (
    let v1 = SQL.select Item_purchase IP_id (fun u -> u.ip_ibid=input_id && u.ip_uid=input_u_id) in
    let p_id = SQL.choose (fun u -> 1=1) v1 in
    SQL.insert Item_purchase {ip_id=p_id.ip_id+1; ip_ibid=input_b_id; ip_iid=input_id; ip_uid=input_u_id; ip_date=""};
    SQL.update Item
      (*do:*)    (fun u -> begin u.i_status <- true; end)
      (*where:*) (fun u -> u.i_id = input_id && u.i_uid=input_u_id)
  )


(*--------------------*)
(*TXN7: NewFeedback*)
let new_feedback_txn (input_rating:int) (input_comment:string) (input_id:int) (input_buyer_id:int) (input_seller_id:int) =
  let v1 = SQL.select User_feedback UF_id (fun u -> u.uf_iid=input_id && u.uf_uid=input_seller_id+1) in
  let f_id = SQL.choose (fun u -> 1=1) v1 in
  SQL.insert User_feedback {uf_uid=f_id.uf_uid; uf_iid=input_id; uf_iuid=f_id.uf_iuid; uf_fromid=input_buyer_id; uf_rating=input_rating; uf_date="9/10/2018";uf_comment=input_comment}



(*--------------------*)
(*TXN8: GetItem*)
let get_item_txn (input_id:int) (input_u_id:int)=
  let v1 = SQL.select1 Item I_all (fun u -> u.i_uid=input_u_id && u.i_id=input_id) in
  ()

(*--------------------*)
(*TXN9: UpdateItem*)
let update_item_txn (input_id:int) (input_u_id:int) (input_description:string)=
    SQL.update Item
      (*do:*)    (fun u -> begin u.i_description <- input_description; end)
      (*where:*) (fun u -> u.i_id = input_id && u.i_uid=input_u_id)


(*--------------------*)
(*TXN10: CheckWinningBids*)
let check_winning_bids_txn (input_start:int) (input_end:int) =
  let v1 = SQL.select Item I_all (fun u -> u.i_startdate > input_start && u.i_enddate < input_end && u.i_status=false) in
  SQL.foreach v1
    begin fun v1_loop_var_1 ->
      let max_bid_id = SQL.select1 Item_max_bid MB_ibid (fun u -> u.mb_iid=v1_loop_var_1.i_id && u.mb_uid=v1_loop_var_1.i_uid) in
      if (max_bid_id.mb_exists = true)
      then (
        let buyer_id = SQL.select1 Item_bid IB_buyerid (fun u -> u.ib_id=max_bid_id.mb_ibid && u.ib_iid = v1_loop_var_1.i_id && u.ib_uid = v1_loop_var_1.i_uid) in
        ()
      )
    end


(*--------------------*)
(*TXN11: PostAuction*)
let post_auction_txn (input_args:post_auction_args list) =
  SQL.foreach input_args 
    begin fun input_args_loop_var_1 ->
      if (input_args_loop_var_1.pa_exists=false)
      then (
        SQL.update Item
        (*do:*)    (fun u -> begin u.i_status <- true; end)
        (*where:*) (fun u -> u.i_id = input_args_loop_var_1.pa_iid && u.i_uid=input_args_loop_var_1.pa_sellerid)
      )
      else (
        SQL.update Item
          (*do:*)    (fun u -> begin u.i_status <- false; end)
          (*where:*) (fun u -> u.i_id = input_args_loop_var_1.pa_iid && u.i_uid=input_args_loop_var_1.pa_sellerid);
        SQL.insert  User_items {ui_uid=input_args_loop_var_1.pa_buyerid; ui_iid=input_args_loop_var_1.pa_iid; ui_sellerid=input_args_loop_var_1.pa_sellerid; ui_created=""}
      )
    end


(*--------------------*)
(*TXN12: GetComment*)
let get_comment_txn (input_seller_id:int) =
  let v1 = SQL.select Item_comment IC_all (fun u -> u.ic_uid = input_seller_id && u.ic_response != "") in 
  ()























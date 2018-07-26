let unimpl () = failwith "Unimpl"
type table_name = 
  | District | Customer | Warehouse
  | Orders   | Orderline| Stock
  | Neworder | History  | Item
type column_name = 
  |D_all |D_id  |D_wid |D_name|D_address |D_ytd |D_tax |D_nextoid
  |C_all |C_id  |C_did |C_wid |C_name |C_address |C_balance| C_discount |C_credit |C_paymentcount |C_ytd |C_deliverycnt
  |W_all |W_id  |W_name|W_address |W_tax |W_ytd
  |O_all |O_id  |O_cid |O_did |O_wid |O_carrierid |O_entrydate
  |OL_all|OL_oid|OL_did|OL_wid|OL_number|OL_iid |OL_delivdate |OL_info
  |S_all |S_iid |S_wid |S_ytd |S_quant|S_ordercnt|S_info
  |N_all |N_oid |N_did |N_wid
  |H_all |H_id  |H_info
  |I_all |I_id  |I_info
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

type district = {d_id:int; d_wid:int; mutable d_name:string; 
                 mutable d_address:string; mutable d_ytd:int; 
                 mutable d_nextoid: int}
type customer = {c_id:int; c_did:int; c_wid:int; mutable c_name:string; mutable c_address:string; 
                 mutable c_balance:int; mutable c_discount:int; mutable c_credit:int;
                 mutable c_paymentcount:int; mutable c_ytd:int; mutable c_deliverycnt:int}
type warehouse= {w_id:int; mutable w_name:string; mutable w_address:string; mutable w_tax:int; mutable w_ytd:int}
type orders= {o_id:int; mutable o_cid:int; o_did:int; o_wid:int; mutable o_carrierid:int; mutable o_entrydate:string}
type orderline= {ol_oid:int; ol_did:int; ol_wid:int; ol_number:int; mutable ol_iid:int; mutable ol_delivdate:string;  mutable ol_info:string}
type stock = {s_iid:int; s_wid:int; mutable s_ytd:int; mutable s_quant:int; mutable s_ordercnt:int; mutable s_info:int }
type neworder = {n_oid:int; n_did:int; n_wid:int}
type history = {h_id:int; mutable h_info:string}
type item = {i_id:int; mutable i_info: string}



(*--------------------*)
(*--------------------*)
(*TXN1: NewOrder*)
let new_order_txn (input_w_id:int) (input_d_id:int) (input_c_id:int) (input_o_id:int) (input_ol_qnt:int) (input_item_list: item list) =   
  (*read warehouse and district tax rates*)
  let v1 = SQL.select1 Warehouse W_tax
                         (fun r -> r.w_id = input_w_id) in
  let v2 = SQL.select1 District D_tax
                         (fun r -> r.d_id = input_d_id) in
  (*update district next order id*)
  let v3 = SQL.select1 District D_nextoid
                         (fun r -> (r.d_id=input_d_id)&&(r.d_wid = input_w_id) ) in
  SQL.update District
          (*do:*)    (fun u -> begin u.d_nextoid <- v3.d_nextoid+1; end)
          (*where:*) (fun u -> u.d_id = input_d_id &&(u.d_wid = input_w_id) );

  (*read customer*)
  let v4 = SQL.select1 Customer C_discount
                         (fun r -> r.c_id = input_c_id) in
  let v5 = SQL.select1 Customer C_name
                         (fun r -> r.c_id = input_c_id) in
  let v6 = SQL.select1 Customer C_credit
                         (fun r -> r.c_id = input_c_id) in
  (*insert the new order specs*)
  SQL.insert Orders   
    {o_id= input_o_id; o_cid=input_c_id; o_did=input_d_id; o_wid=input_w_id; o_carrierid=0; o_entrydate="06/05/2018"};
  SQL.insert Neworder 
    {n_oid=input_o_id; n_did=input_d_id; n_wid=input_w_id};
  
  SQL.foreach input_item_list
     begin fun loop_var_1 -> 
      let v7 = SQL.select1 Item I_info (*read corresponding item*)
                            (fun r -> r.i_id = loop_var_1.i_id) in
      (*read and update stock*)
      let v8 = SQL.select1 Stock S_ytd
                            (fun r -> (r.s_iid = loop_var_1.i_id) && (r.s_wid = input_w_id)) in
      let v9 = SQL.select1 Stock S_ordercnt
                            (fun r -> (r.s_iid = loop_var_1.i_id) && (r.s_wid = input_w_id)) in
      SQL.update Stock
          (*do:*)    (fun u -> begin u.s_ordercnt <- v9.s_ordercnt+1; end)
          (*where:*) (fun r -> (r.s_iid = loop_var_1.i_id) && (r.s_wid = input_w_id));
      SQL.update Stock
          (*do:*)    (fun u -> begin u.s_ytd <- v8.s_ytd+input_ol_qnt; end)
          (*where:*) (fun r -> (r.s_iid = loop_var_1.i_id) && (r.s_wid = input_w_id));
      
      let v10 = SQL.select1 Stock S_quant
                            (fun r -> (r.s_iid = loop_var_1.i_id) && (r.s_wid = input_w_id)) in
      (*conditional update*)
      if v10.s_quant-input_ol_qnt>10
      then SQL.update Stock
            (*do:*)    (fun r -> begin r.s_quant <- v10.s_quant - input_ol_qnt; end)
            (*where:*) (fun r -> (r.s_iid = loop_var_1.i_id) && (r.s_wid = input_w_id))
      else SQL.update Stock
            (*do:*)    (fun r -> begin r.s_quant <- v10.s_quant - input_ol_qnt + 91; end)
            (*where:*) (fun r -> (r.s_iid = loop_var_1.i_id) && (r.s_wid = input_w_id))
     end


(*--------------------*)
(*--------------------*)
(*TXN2*)
let payment_txn (input_w_id:int) (input_d_id:int) (input_c_name:string) (input_c_id:int) (input_h_amount:int) (input_cid_is_given: bool)=  
  
  (*update warehouse and district ytds*)
  let v1 = SQL.select1 Warehouse W_ytd
                         (fun r -> r.w_id=input_w_id) in
  SQL.update Warehouse
          (*do:*)    (fun u -> begin u.w_ytd <- v1.w_ytd+input_h_amount; end)
          (*where:*) (fun r -> r.w_id=input_w_id);
  let v2 = SQL.select1 District D_ytd
                         (fun r -> r.d_id=input_d_id && r.d_wid = input_w_id) in
  SQL.update District
          (*do:*)    (fun u -> begin u.d_ytd <- v2.d_ytd+input_h_amount; end)
          (*where:*) (fun r ->  r.d_id=input_d_id && r.d_wid = input_w_id);


  if input_cid_is_given 
  then  
    let v3 = SQL.select1 Customer C_balance
                         (fun r -> r.c_id=input_c_id  && r.c_did = input_d_id && r.c_wid = input_w_id) in
    SQL.update Customer
          (*do:*)    (fun u -> begin u.c_balance <- v3.c_balance+input_h_amount; end)
          (*where:*) (fun r ->  r.c_id=input_c_id  && r.c_did = input_d_id && r.c_wid = input_w_id);
 
    let v4 = SQL.select1 Customer C_ytd
                         (fun r -> r.c_id=input_c_id  && r.c_did = input_d_id && r.c_wid = input_w_id) in
    SQL.update Customer
          (*do:*)    (fun u -> begin u.c_ytd <- v4.c_ytd+input_h_amount; end)
          (*where:*) (fun r ->  r.c_id=input_c_id  && r.c_did = input_d_id && r.c_wid = input_w_id);

    let v5 = SQL.select1 Customer C_paymentcount
                         (fun r -> r.c_id=input_c_id  && r.c_did = input_d_id && r.c_wid = input_w_id) in
    SQL.update Customer
          (*do:*)    (fun u -> begin u.c_paymentcount <- v5.c_paymentcount+input_h_amount; end)
          (*where:*) (fun r ->  r.c_id=input_c_id  && r.c_did = input_d_id && r.c_wid = input_w_id);

  else 
    let v6 = SQL.select Customer C_all
                         (fun r -> r.c_name=input_c_name  && r.c_did = input_d_id && r.c_wid = input_w_id) in
    let v7 = SQL.choose (fun u -> u.c_id=50) v6 in (*the customer in the middle*)
    SQL.update Customer
          (*do:*)    (fun u -> begin u.c_balance <- v7.c_balance+input_h_amount; end)
          (*where:*) (fun r ->  r.c_id=input_c_id  && r.c_did = input_d_id && r.c_wid = input_w_id);
    SQL.update Customer
          (*do:*)    (fun u -> begin u.c_ytd <- v7.c_ytd+input_h_amount; end)
          (*where:*) (fun r ->  r.c_id=input_c_id  && r.c_did = input_d_id && r.c_wid = input_w_id);
    SQL.update Customer
          (*do:*)    (fun u -> begin u.c_paymentcount <- v7.c_paymentcount+input_h_amount; end)
          (*where:*) (fun r ->  r.c_id=input_c_id  && r.c_did = input_d_id && r.c_wid = input_w_id)



(*--------------------*)
(*TXN3*)
let order_status_txn (input_w_id:int) (input_d_id:int) (input_c_name:string) (input_c_id:int) (input_cid_is_given: bool) =  
  if input_cid_is_given
  (*case 1*)
  then 
    let v1 = SQL.select1 Customer C_balance
                  (fun r -> r.c_id=input_c_id  && r.c_did = input_d_id && r.c_wid = input_w_id) in
    let v4 = SQL.select Orders O_all
                  (fun r -> r.o_did = input_d_id && r.o_wid = input_w_id && r.o_cid = v1.c_id) in
    let v7 = SQL.choose (fun u -> u.o_id=50) v4 in (*the biggest order*)
    let v9 = SQL.select Orderline OL_all
                  (fun r -> r.ol_oid = v7.o_id && r.ol_did = input_d_id && r.ol_wid = input_w_id) in
    ()
  (*case 2*)
  else 
    let v2 = SQL.select Customer C_all
                  (fun r -> r.c_name=input_c_name  && r.c_did = input_d_id && r.c_wid = input_w_id) in
    let v3 = SQL.choose (fun u -> u.c_id=50) v2 in (*let's assume this is the middle one*) 
    let v5 = SQL.select Orders O_all
                  (fun r -> r.o_did = input_d_id && r.o_wid = input_w_id && r.o_cid = v3.c_id) in
    let v6 = SQL.choose (fun u -> u.o_id=50) v5 in (*the biggest order*)
    let v8 = SQL.select Orderline OL_all
                  (fun r -> r.ol_oid = v6.o_id && r.ol_did = input_d_id && r.ol_wid = input_w_id) in

    ()


(*--------------------*)
(*--------------------*)
(*TXN4*)
let stock_level_txn (input_w_id:int) (input_d_id:int) =  
  let v1 = SQL.select1 District D_nextoid
                         (fun r -> r.d_id=input_d_id && r.d_wid = input_w_id) in
  let v2 = SQL.select Orderline OL_iid 
                         (fun r -> r.ol_did=input_d_id && r.ol_wid = input_w_id && 
                                   r.ol_oid<v1.d_nextoid && r.ol_oid>v1.d_nextoid-20) in
  SQL.foreach v2
    begin fun loop_var_1 ->
      let v3 = SQL.select Stock S_all
                         (fun r -> r.s_wid=input_w_id && r.s_iid = loop_var_1.ol_iid) in
      ()(*print v3*)
    end
  

(*--------------------*)
(*--------------------*)
(*TXN5*)
let delivery_txn  (input_w_id:int) (input_d_id:int) (input_temp:int) (input_temp2:int) (input_carrier_id:int) =  
  let v1 = SQL.select Neworder N_oid
                         (fun r -> r.n_did=input_d_id && r.n_wid = input_w_id) in
  let v2 = SQL.choose (fun u -> u.n_oid=input_temp) v1 (*picking the oldest one*) in

  SQL.delete Neworder (fun r -> r.n_did=input_d_id && r.n_wid = input_w_id &&  r.n_oid=input_temp);
  let v3 = SQL.select1 Orders O_cid
                         (fun r -> r.o_did=input_d_id && r.o_wid = input_w_id && r.o_id = v2.n_oid) in
  SQL.update Orders
          (*do:*)    (fun u -> begin u.o_carrierid <- input_carrier_id; end)
          (*where:*) (fun r ->  r.o_did=input_d_id && r.o_wid = input_w_id && r.o_id = v2.n_oid);
  SQL.update Orderline
          (*do*)     (fun u -> begin u.ol_delivdate <- "06/05/2018"; end)
          (*where:*) (fun r ->  r.ol_did=input_d_id && r.ol_wid = input_w_id && r.ol_oid = v3.o_id);
  let v4 = SQL.select Orderline OL_info 
                     (fun r ->  r.ol_did=input_d_id && r.ol_wid = input_w_id && r.ol_oid = v3.o_id) in
 
  let v5 = SQL.select1 Customer C_balance
                         (fun r -> r.c_id=v3.o_cid  && r.c_did = input_d_id && r.c_wid = input_w_id) in
  SQL.update Customer
          (*do:*)    (fun u -> begin u.c_balance <- v5.c_balance+input_temp2; end) (*temp: let's assume temp2 is the sum for now*)
          (*where:*) (fun r ->  r.c_id=v3.o_cid  && r.c_did = input_d_id && r.c_wid = input_w_id);
  SQL.update Customer
          (*do:*)    (fun u -> begin u.c_deliverycnt <- v5.c_deliverycnt+1; end)
          (*where:*) (fun r ->  r.c_id=v3.o_cid  && r.c_did = input_d_id && r.c_wid = input_w_id)




















































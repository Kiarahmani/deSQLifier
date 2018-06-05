let unimpl () = failwith "Unimpl"
type table_name = 
  | District | Customer | Warehouse
  | Orders   | OrderLine| Stock
  | NewOrder | History  | Item
type column_name = 
  |D_all |D_id  |D_wid |D_name|D_address |D_ytd |D_tax |D_nextoid
  |C_all |C_id  |C_did |C_wid |C_name |C_address |C_balance| C_discount |C_credit |C_paymentcount |C_ytd |C_deliverycnt
  |W_all |W_id  |W_name|W_address |W_tax |W_ytd
  |O_all |O_id  |O_cid |O_did |O_wid |O_carrierid |O_entrydate
  |OL_all|OL_oid|OL_did|OL_wid|OL_number|OL_info
  |S_all |S_iid |S_wid |S_quant|S_orders|S_info
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
type orders= {o_id:int; o_cid:int; o_did:int; o_wid:int; mutable o_carrierid:int; mutable o_entrydate:string}
type orderline= {ol_oid:int; ol_did:int; ol_wid:int; mutable ol_number:int; mutable ol_info:string}
type stock = {s_iid:int; s_wid:int; mutable s_quant:int; mutable s_orders:string; mutable s_info:int }
type neworder = {n_oid:int; n_did:int; n_wid:int}
type history = {h_id:int; mutable h_info:string}
type item = {i_id:int; mutable i_info: string}




(*--------------------*)
(*TXN1: NewOrder*)
let new_order_txn (input_w_id:int) (input_d_id:int) (input_c_id:int) (input_o_id:int) (input_item_list: item list) =   
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
  SQL.insert NewOrder 
    {n_oid=input_o_id; n_did=input_d_id; n_wid=input_w_id};
  (*
  SQL.foreach input_item_list
     begin fun loop_var_1 -> 
       ()
     end;
*)

  ()


(*--------------------*)
(*TXN2*)
let payment_txn (input:int) =  
()


(*--------------------*)
(*TXN3*)
let order_status_txn (input:int) =  
()


(*--------------------*)
(*TXN4*)
let stock_level_txn (input:int) =  
()



(*--------------------*)
(*TXN5*)
let delivery_txn (input:int) =  
()



















































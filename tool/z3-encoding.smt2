
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       Constants                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(set-option :produce-unsat-cores true)

(declare-datatypes () ((TType (Delivery) (Stock_level) (Order_status) (Payment) (New_order)))) 
(declare-sort T)
(declare-fun type (T) TType)

(declare-fun WR (T T) Bool)
(declare-fun RW (T T) Bool)
(declare-fun WW (T T) Bool)
(declare-fun vis (T T) Bool)
(declare-fun ar (T T) Bool)

(assert (! (forall ((t T))       (not (or (WR t t) (RW t t) (WW t t))))     :named no_loops))
(assert (! (forall ((t1 T) (t2 T))   (=> (vis t1 t2) (not (vis t2 t1))))      :named acyc_vis))
(assert (! (forall ((t1 T) (t2 T) (t3 T))(=> (and (ar  t1 t2) (ar  t2 t3)) (ar  t1 t3)))  :named trans_ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (not (= t1 t2)) (xor (ar  t1 t2) (ar  t2 t1))))  :named total_ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (vis t1 t2) (ar t1 t2)))       :named vis_in_ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (WR t1 t2) (vis t1 t2)))       :named wr_then_vis))
(assert (! (forall ((t1 T) (t2 T))   (=> (WW t1 t2) (ar t1 t2)))        :named ww->ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (RW t1 t2) (not (vis t2 t1))))     :named rw_then_not_vis))
(assert (! (forall ((t T))     (not (ar t t)))          :named irreflx_ar))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                   Table Declarations                                                   
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(declare-sort District)
(declare-fun District_Proj_d_id (District) Int)
(declare-fun District_Proj_d_wid (District) Int)
(declare-fun District_Proj_d_name (District) String)
(declare-fun District_Proj_d_address (District) String)
(declare-fun District_Proj_d_ytd (District) Int)
(declare-fun District_Proj_d_nextoid (District) Int)
(assert (! (forall ((r1 District)(r2 District)) (=>
  (and (= (District_Proj_d_id r1) (District_Proj_d_id r2))(= (District_Proj_d_wid r1) (District_Proj_d_wid r2)))(= r1 r2))) :named pk-district) )
(declare-fun RW_District (District T T) Bool)
(declare-fun RW_Alive_District (District T T) Bool)
(declare-fun WR_District (District T T) Bool)
(declare-fun WR_Alive_District (District T T) Bool)
(declare-fun WW_District (District T T) Bool)
(declare-fun WW_Alive_District (District T T) Bool)
(declare-fun IsAlive_District (District T) Bool)
(assert (! (forall ((r District)(t1 T)(t2 T)) (=> (RW_District r t1 t2) (RW t1 t2)))       :named district-RW-then-row))
(assert (! (forall ((r District)(t1 T)(t2 T)) (=> (RW_Alive_District r t1 t2) (RW t1 t2))) :named district-RW-then-alive))
(assert (! (forall ((r District)(t1 T)(t2 T)) (=> (WR_District r t1 t2) (WR t1 t2)))       :named district-WR-then-row))
(assert (! (forall ((r District)(t1 T)(t2 T)) (=> (WR_Alive_District r t1 t2) (WR t1 t2))) :named district-WR-then-alive))
(assert (! (forall ((r District)(t1 T)(t2 T)) (=> (WW_District r t1 t2) (WW t1 t2)))       :named district-WW-then-row))
(assert (! (forall ((r District)(t1 T)(t2 T)) (=> (WW_Alive_District r t1 t2) (WW t1 t2))) :named district-WW-then-alive))
(assert (! (forall ((r District)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_District r t2 t1)(RW_District r t1 t3))(WW_District r t2 t3))) :named district-lww-row))
(assert (! (forall ((r District)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_District r t2 t1)(RW_Alive_District r t1 t3))(WW_Alive_District r t2 t3))) :named district-lww-alive))

(declare-sort Customer)
(declare-fun Customer_Proj_c_id (Customer) Int)
(declare-fun Customer_Proj_c_did (Customer) Int)
(declare-fun Customer_Proj_c_wid (Customer) Int)
(declare-fun Customer_Proj_c_name (Customer) String)
(declare-fun Customer_Proj_c_address (Customer) String)
(declare-fun Customer_Proj_c_balance (Customer) Int)
(declare-fun Customer_Proj_c_discount (Customer) Int)
(declare-fun Customer_Proj_c_credit (Customer) Int)
(declare-fun Customer_Proj_c_paymentcount (Customer) Int)
(declare-fun Customer_Proj_c_ytd (Customer) Int)
(declare-fun Customer_Proj_c_deliverycnt (Customer) Int)
(assert (! (forall ((r1 Customer)(r2 Customer)) (=>
  (and (= (Customer_Proj_c_id r1) (Customer_Proj_c_id r2))(= (Customer_Proj_c_did r1) (Customer_Proj_c_did r2))(= (Customer_Proj_c_wid r1) (Customer_Proj_c_wid r2)))(= r1 r2))) :named pk-customer) )
(declare-fun RW_Customer (Customer T T) Bool)
(declare-fun RW_Alive_Customer (Customer T T) Bool)
(declare-fun WR_Customer (Customer T T) Bool)
(declare-fun WR_Alive_Customer (Customer T T) Bool)
(declare-fun WW_Customer (Customer T T) Bool)
(declare-fun WW_Alive_Customer (Customer T T) Bool)
(declare-fun IsAlive_Customer (Customer T) Bool)
(assert (! (forall ((r Customer)(t1 T)(t2 T)) (=> (RW_Customer r t1 t2) (RW t1 t2)))       :named customer-RW-then-row))
(assert (! (forall ((r Customer)(t1 T)(t2 T)) (=> (RW_Alive_Customer r t1 t2) (RW t1 t2))) :named customer-RW-then-alive))
(assert (! (forall ((r Customer)(t1 T)(t2 T)) (=> (WR_Customer r t1 t2) (WR t1 t2)))       :named customer-WR-then-row))
(assert (! (forall ((r Customer)(t1 T)(t2 T)) (=> (WR_Alive_Customer r t1 t2) (WR t1 t2))) :named customer-WR-then-alive))
(assert (! (forall ((r Customer)(t1 T)(t2 T)) (=> (WW_Customer r t1 t2) (WW t1 t2)))       :named customer-WW-then-row))
(assert (! (forall ((r Customer)(t1 T)(t2 T)) (=> (WW_Alive_Customer r t1 t2) (WW t1 t2))) :named customer-WW-then-alive))
(assert (! (forall ((r Customer)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Customer r t2 t1)(RW_Customer r t1 t3))(WW_Customer r t2 t3))) :named customer-lww-row))
(assert (! (forall ((r Customer)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Customer r t2 t1)(RW_Alive_Customer r t1 t3))(WW_Alive_Customer r t2 t3))) :named customer-lww-alive))

(declare-sort Warehouse)
(declare-fun Warehouse_Proj_w_id (Warehouse) Int)
(declare-fun Warehouse_Proj_w_name (Warehouse) String)
(declare-fun Warehouse_Proj_w_address (Warehouse) String)
(declare-fun Warehouse_Proj_w_tax (Warehouse) Int)
(declare-fun Warehouse_Proj_w_ytd (Warehouse) Int)
(assert (! (forall ((r1 Warehouse)(r2 Warehouse)) (=>
  (and (= (Warehouse_Proj_w_id r1) (Warehouse_Proj_w_id r2)))(= r1 r2))) :named pk-warehouse) )
(declare-fun RW_Warehouse (Warehouse T T) Bool)
(declare-fun RW_Alive_Warehouse (Warehouse T T) Bool)
(declare-fun WR_Warehouse (Warehouse T T) Bool)
(declare-fun WR_Alive_Warehouse (Warehouse T T) Bool)
(declare-fun WW_Warehouse (Warehouse T T) Bool)
(declare-fun WW_Alive_Warehouse (Warehouse T T) Bool)
(declare-fun IsAlive_Warehouse (Warehouse T) Bool)
(assert (! (forall ((r Warehouse)(t1 T)(t2 T)) (=> (RW_Warehouse r t1 t2) (RW t1 t2)))       :named warehouse-RW-then-row))
(assert (! (forall ((r Warehouse)(t1 T)(t2 T)) (=> (RW_Alive_Warehouse r t1 t2) (RW t1 t2))) :named warehouse-RW-then-alive))
(assert (! (forall ((r Warehouse)(t1 T)(t2 T)) (=> (WR_Warehouse r t1 t2) (WR t1 t2)))       :named warehouse-WR-then-row))
(assert (! (forall ((r Warehouse)(t1 T)(t2 T)) (=> (WR_Alive_Warehouse r t1 t2) (WR t1 t2))) :named warehouse-WR-then-alive))
(assert (! (forall ((r Warehouse)(t1 T)(t2 T)) (=> (WW_Warehouse r t1 t2) (WW t1 t2)))       :named warehouse-WW-then-row))
(assert (! (forall ((r Warehouse)(t1 T)(t2 T)) (=> (WW_Alive_Warehouse r t1 t2) (WW t1 t2))) :named warehouse-WW-then-alive))
(assert (! (forall ((r Warehouse)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Warehouse r t2 t1)(RW_Warehouse r t1 t3))(WW_Warehouse r t2 t3))) :named warehouse-lww-row))
(assert (! (forall ((r Warehouse)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Warehouse r t2 t1)(RW_Alive_Warehouse r t1 t3))(WW_Alive_Warehouse r t2 t3))) :named warehouse-lww-alive))

(declare-sort Orders)
(declare-fun Orders_Proj_o_id (Orders) Int)
(declare-fun Orders_Proj_o_cid (Orders) Int)
(declare-fun Orders_Proj_o_did (Orders) Int)
(declare-fun Orders_Proj_o_wid (Orders) Int)
(declare-fun Orders_Proj_o_carrierid (Orders) Int)
(declare-fun Orders_Proj_o_entrydate (Orders) String)
(assert (! (forall ((r1 Orders)(r2 Orders)) (=>
  (and (= (Orders_Proj_o_id r1) (Orders_Proj_o_id r2))(= (Orders_Proj_o_cid r1) (Orders_Proj_o_cid r2))(= (Orders_Proj_o_did r1) (Orders_Proj_o_did r2))(= (Orders_Proj_o_wid r1) (Orders_Proj_o_wid r2)))(= r1 r2))) :named pk-orders) )
(declare-fun RW_Orders (Orders T T) Bool)
(declare-fun RW_Alive_Orders (Orders T T) Bool)
(declare-fun WR_Orders (Orders T T) Bool)
(declare-fun WR_Alive_Orders (Orders T T) Bool)
(declare-fun WW_Orders (Orders T T) Bool)
(declare-fun WW_Alive_Orders (Orders T T) Bool)
(declare-fun IsAlive_Orders (Orders T) Bool)
(assert (! (forall ((r Orders)(t1 T)(t2 T)) (=> (RW_Orders r t1 t2) (RW t1 t2)))       :named orders-RW-then-row))
(assert (! (forall ((r Orders)(t1 T)(t2 T)) (=> (RW_Alive_Orders r t1 t2) (RW t1 t2))) :named orders-RW-then-alive))
(assert (! (forall ((r Orders)(t1 T)(t2 T)) (=> (WR_Orders r t1 t2) (WR t1 t2)))       :named orders-WR-then-row))
(assert (! (forall ((r Orders)(t1 T)(t2 T)) (=> (WR_Alive_Orders r t1 t2) (WR t1 t2))) :named orders-WR-then-alive))
(assert (! (forall ((r Orders)(t1 T)(t2 T)) (=> (WW_Orders r t1 t2) (WW t1 t2)))       :named orders-WW-then-row))
(assert (! (forall ((r Orders)(t1 T)(t2 T)) (=> (WW_Alive_Orders r t1 t2) (WW t1 t2))) :named orders-WW-then-alive))
(assert (! (forall ((r Orders)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Orders r t2 t1)(RW_Orders r t1 t3))(WW_Orders r t2 t3))) :named orders-lww-row))
(assert (! (forall ((r Orders)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Orders r t2 t1)(RW_Alive_Orders r t1 t3))(WW_Alive_Orders r t2 t3))) :named orders-lww-alive))

(declare-sort Orderline)
(declare-fun Orderline_Proj_ol_oid (Orderline) Int)
(declare-fun Orderline_Proj_ol_did (Orderline) Int)
(declare-fun Orderline_Proj_ol_wid (Orderline) Int)
(declare-fun Orderline_Proj_ol_number (Orderline) Int)
(declare-fun Orderline_Proj_ol_info (Orderline) String)
(assert (! (forall ((r1 Orderline)(r2 Orderline)) (=>
  (and (= (Orderline_Proj_ol_oid r1) (Orderline_Proj_ol_oid r2))(= (Orderline_Proj_ol_did r1) (Orderline_Proj_ol_did r2))(= (Orderline_Proj_ol_wid r1) (Orderline_Proj_ol_wid r2)))(= r1 r2))) :named pk-orderline) )
(declare-fun RW_Orderline (Orderline T T) Bool)
(declare-fun RW_Alive_Orderline (Orderline T T) Bool)
(declare-fun WR_Orderline (Orderline T T) Bool)
(declare-fun WR_Alive_Orderline (Orderline T T) Bool)
(declare-fun WW_Orderline (Orderline T T) Bool)
(declare-fun WW_Alive_Orderline (Orderline T T) Bool)
(declare-fun IsAlive_Orderline (Orderline T) Bool)
(assert (! (forall ((r Orderline)(t1 T)(t2 T)) (=> (RW_Orderline r t1 t2) (RW t1 t2)))       :named orderline-RW-then-row))
(assert (! (forall ((r Orderline)(t1 T)(t2 T)) (=> (RW_Alive_Orderline r t1 t2) (RW t1 t2))) :named orderline-RW-then-alive))
(assert (! (forall ((r Orderline)(t1 T)(t2 T)) (=> (WR_Orderline r t1 t2) (WR t1 t2)))       :named orderline-WR-then-row))
(assert (! (forall ((r Orderline)(t1 T)(t2 T)) (=> (WR_Alive_Orderline r t1 t2) (WR t1 t2))) :named orderline-WR-then-alive))
(assert (! (forall ((r Orderline)(t1 T)(t2 T)) (=> (WW_Orderline r t1 t2) (WW t1 t2)))       :named orderline-WW-then-row))
(assert (! (forall ((r Orderline)(t1 T)(t2 T)) (=> (WW_Alive_Orderline r t1 t2) (WW t1 t2))) :named orderline-WW-then-alive))
(assert (! (forall ((r Orderline)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Orderline r t2 t1)(RW_Orderline r t1 t3))(WW_Orderline r t2 t3))) :named orderline-lww-row))
(assert (! (forall ((r Orderline)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Orderline r t2 t1)(RW_Alive_Orderline r t1 t3))(WW_Alive_Orderline r t2 t3))) :named orderline-lww-alive))

(declare-sort Stock)
(declare-fun Stock_Proj_s_iid (Stock) Int)
(declare-fun Stock_Proj_s_wid (Stock) Int)
(declare-fun Stock_Proj_s_quant (Stock) Int)
(declare-fun Stock_Proj_s_orders (Stock) String)
(declare-fun Stock_Proj_s_info (Stock) Int)
(assert (! (forall ((r1 Stock)(r2 Stock)) (=>
  (and (= (Stock_Proj_s_iid r1) (Stock_Proj_s_iid r2))(= (Stock_Proj_s_wid r1) (Stock_Proj_s_wid r2)))(= r1 r2))) :named pk-stock) )
(declare-fun RW_Stock (Stock T T) Bool)
(declare-fun RW_Alive_Stock (Stock T T) Bool)
(declare-fun WR_Stock (Stock T T) Bool)
(declare-fun WR_Alive_Stock (Stock T T) Bool)
(declare-fun WW_Stock (Stock T T) Bool)
(declare-fun WW_Alive_Stock (Stock T T) Bool)
(declare-fun IsAlive_Stock (Stock T) Bool)
(assert (! (forall ((r Stock)(t1 T)(t2 T)) (=> (RW_Stock r t1 t2) (RW t1 t2)))       :named stock-RW-then-row))
(assert (! (forall ((r Stock)(t1 T)(t2 T)) (=> (RW_Alive_Stock r t1 t2) (RW t1 t2))) :named stock-RW-then-alive))
(assert (! (forall ((r Stock)(t1 T)(t2 T)) (=> (WR_Stock r t1 t2) (WR t1 t2)))       :named stock-WR-then-row))
(assert (! (forall ((r Stock)(t1 T)(t2 T)) (=> (WR_Alive_Stock r t1 t2) (WR t1 t2))) :named stock-WR-then-alive))
(assert (! (forall ((r Stock)(t1 T)(t2 T)) (=> (WW_Stock r t1 t2) (WW t1 t2)))       :named stock-WW-then-row))
(assert (! (forall ((r Stock)(t1 T)(t2 T)) (=> (WW_Alive_Stock r t1 t2) (WW t1 t2))) :named stock-WW-then-alive))
(assert (! (forall ((r Stock)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Stock r t2 t1)(RW_Stock r t1 t3))(WW_Stock r t2 t3))) :named stock-lww-row))
(assert (! (forall ((r Stock)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Stock r t2 t1)(RW_Alive_Stock r t1 t3))(WW_Alive_Stock r t2 t3))) :named stock-lww-alive))

(declare-sort Neworder)
(declare-fun Neworder_Proj_n_oid (Neworder) Int)
(declare-fun Neworder_Proj_n_did (Neworder) Int)
(declare-fun Neworder_Proj_n_wid (Neworder) Int)
(assert (! (forall ((r1 Neworder)(r2 Neworder)) (=>
  (and (= (Neworder_Proj_n_oid r1) (Neworder_Proj_n_oid r2))(= (Neworder_Proj_n_did r1) (Neworder_Proj_n_did r2))(= (Neworder_Proj_n_wid r1) (Neworder_Proj_n_wid r2)))(= r1 r2))) :named pk-neworder) )
(declare-fun RW_Neworder (Neworder T T) Bool)
(declare-fun RW_Alive_Neworder (Neworder T T) Bool)
(declare-fun WR_Neworder (Neworder T T) Bool)
(declare-fun WR_Alive_Neworder (Neworder T T) Bool)
(declare-fun WW_Neworder (Neworder T T) Bool)
(declare-fun WW_Alive_Neworder (Neworder T T) Bool)
(declare-fun IsAlive_Neworder (Neworder T) Bool)
(assert (! (forall ((r Neworder)(t1 T)(t2 T)) (=> (RW_Neworder r t1 t2) (RW t1 t2)))       :named neworder-RW-then-row))
(assert (! (forall ((r Neworder)(t1 T)(t2 T)) (=> (RW_Alive_Neworder r t1 t2) (RW t1 t2))) :named neworder-RW-then-alive))
(assert (! (forall ((r Neworder)(t1 T)(t2 T)) (=> (WR_Neworder r t1 t2) (WR t1 t2)))       :named neworder-WR-then-row))
(assert (! (forall ((r Neworder)(t1 T)(t2 T)) (=> (WR_Alive_Neworder r t1 t2) (WR t1 t2))) :named neworder-WR-then-alive))
(assert (! (forall ((r Neworder)(t1 T)(t2 T)) (=> (WW_Neworder r t1 t2) (WW t1 t2)))       :named neworder-WW-then-row))
(assert (! (forall ((r Neworder)(t1 T)(t2 T)) (=> (WW_Alive_Neworder r t1 t2) (WW t1 t2))) :named neworder-WW-then-alive))
(assert (! (forall ((r Neworder)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Neworder r t2 t1)(RW_Neworder r t1 t3))(WW_Neworder r t2 t3))) :named neworder-lww-row))
(assert (! (forall ((r Neworder)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Neworder r t2 t1)(RW_Alive_Neworder r t1 t3))(WW_Alive_Neworder r t2 t3))) :named neworder-lww-alive))

(declare-sort History)
(declare-fun History_Proj_h_id (History) Int)
(declare-fun History_Proj_h_info (History) String)
(assert (! (forall ((r1 History)(r2 History)) (=>
  (and (= (History_Proj_h_id r1) (History_Proj_h_id r2)))(= r1 r2))) :named pk-history) )
(declare-fun RW_History (History T T) Bool)
(declare-fun RW_Alive_History (History T T) Bool)
(declare-fun WR_History (History T T) Bool)
(declare-fun WR_Alive_History (History T T) Bool)
(declare-fun WW_History (History T T) Bool)
(declare-fun WW_Alive_History (History T T) Bool)
(declare-fun IsAlive_History (History T) Bool)
(assert (! (forall ((r History)(t1 T)(t2 T)) (=> (RW_History r t1 t2) (RW t1 t2)))       :named history-RW-then-row))
(assert (! (forall ((r History)(t1 T)(t2 T)) (=> (RW_Alive_History r t1 t2) (RW t1 t2))) :named history-RW-then-alive))
(assert (! (forall ((r History)(t1 T)(t2 T)) (=> (WR_History r t1 t2) (WR t1 t2)))       :named history-WR-then-row))
(assert (! (forall ((r History)(t1 T)(t2 T)) (=> (WR_Alive_History r t1 t2) (WR t1 t2))) :named history-WR-then-alive))
(assert (! (forall ((r History)(t1 T)(t2 T)) (=> (WW_History r t1 t2) (WW t1 t2)))       :named history-WW-then-row))
(assert (! (forall ((r History)(t1 T)(t2 T)) (=> (WW_Alive_History r t1 t2) (WW t1 t2))) :named history-WW-then-alive))
(assert (! (forall ((r History)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_History r t2 t1)(RW_History r t1 t3))(WW_History r t2 t3))) :named history-lww-row))
(assert (! (forall ((r History)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_History r t2 t1)(RW_Alive_History r t1 t3))(WW_Alive_History r t2 t3))) :named history-lww-alive))

(declare-sort Item)
(declare-fun Item_Proj_i_id (Item) Int)
(declare-fun Item_Proj_i_info (Item) String)
(assert (! (forall ((r1 Item)(r2 Item)) (=>
  (and (= (Item_Proj_i_id r1) (Item_Proj_i_id r2)))(= r1 r2))) :named pk-item) )
(declare-fun RW_Item (Item T T) Bool)
(declare-fun RW_Alive_Item (Item T T) Bool)
(declare-fun WR_Item (Item T T) Bool)
(declare-fun WR_Alive_Item (Item T T) Bool)
(declare-fun WW_Item (Item T T) Bool)
(declare-fun WW_Alive_Item (Item T T) Bool)
(declare-fun IsAlive_Item (Item T) Bool)
(assert (! (forall ((r Item)(t1 T)(t2 T)) (=> (RW_Item r t1 t2) (RW t1 t2)))       :named item-RW-then-row))
(assert (! (forall ((r Item)(t1 T)(t2 T)) (=> (RW_Alive_Item r t1 t2) (RW t1 t2))) :named item-RW-then-alive))
(assert (! (forall ((r Item)(t1 T)(t2 T)) (=> (WR_Item r t1 t2) (WR t1 t2)))       :named item-WR-then-row))
(assert (! (forall ((r Item)(t1 T)(t2 T)) (=> (WR_Alive_Item r t1 t2) (WR t1 t2))) :named item-WR-then-alive))
(assert (! (forall ((r Item)(t1 T)(t2 T)) (=> (WW_Item r t1 t2) (WW t1 t2)))       :named item-WW-then-row))
(assert (! (forall ((r Item)(t1 T)(t2 T)) (=> (WW_Alive_Item r t1 t2) (WW t1 t2))) :named item-WW-then-alive))
(assert (! (forall ((r Item)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Item r t2 t1)(RW_Item r t1 t3))(WW_Item r t2 t3))) :named item-lww-row))
(assert (! (forall ((r Item)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Item r t2 t1)(RW_Alive_Item r t1 t3))(WW_Alive_Item r t2 t3))) :named item-lww-alive))

;params
(declare-fun Delivery_Param_input (T) Int)
(declare-fun Stock_level_Param_input (T) Int)
(declare-fun Order_status_Param_input (T) Int)
(declare-fun Payment_Param_input (T) Int)
(declare-fun New_order_Param_input_w_id (T) Int)
(declare-fun New_order_Param_input_d_id (T) Int)
(declare-fun New_order_Param_input_c_id (T) Int)
(declare-fun New_order_Param_input_o_id (T) Int)
(declare-fun New_order_Param_input_item_list (T Item) Bool)

;v1
(declare-fun New_order_isN_v1 (T) Bool)
(declare-fun New_order_Var_v1 (T) Warehouse)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v1 t0)) (exists ((r Warehouse))(= (New_order_Var_v1 t0) r))) 
                               (=> (exists ((r Warehouse))(= (New_order_Var_v1 t0) r)) (not (New_order_isN_v1 t0))))) :named v1-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Warehouse_Proj_w_id (New_order_Var_v1 t0)) (New_order_Param_input_w_id t0))) :named v1-select-prop))
;v2
(declare-fun New_order_isN_v2 (T) Bool)
(declare-fun New_order_Var_v2 (T) District)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v2 t0)) (exists ((r District))(= (New_order_Var_v2 t0) r))) 
                               (=> (exists ((r District))(= (New_order_Var_v2 t0) r)) (not (New_order_isN_v2 t0))))) :named v2-isnull-prop) )
(assert (! (forall ((t0 T)) (= (District_Proj_d_id (New_order_Var_v2 t0)) (New_order_Param_input_d_id t0))) :named v2-select-prop))
;v3
(declare-fun New_order_isN_v3 (T) Bool)
(declare-fun New_order_Var_v3 (T) District)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v3 t0)) (exists ((r District))(= (New_order_Var_v3 t0) r))) 
                               (=> (exists ((r District))(= (New_order_Var_v3 t0) r)) (not (New_order_isN_v3 t0))))) :named v3-isnull-prop) )
(assert (! (forall ((t0 T)) (and (= (District_Proj_d_wid (New_order_Var_v3 t0)) (New_order_Param_input_w_id t0)) (= (District_Proj_d_id (New_order_Var_v3 t0)) (New_order_Param_input_d_id t0)))) :named v3-select-prop))
;v4
(declare-fun New_order_isN_v4 (T) Bool)
(declare-fun New_order_Var_v4 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v4 t0)) (exists ((r Customer))(= (New_order_Var_v4 t0) r))) 
                               (=> (exists ((r Customer))(= (New_order_Var_v4 t0) r)) (not (New_order_isN_v4 t0))))) :named v4-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Customer_Proj_c_id (New_order_Var_v4 t0)) (New_order_Param_input_c_id t0))) :named v4-select-prop))
;v5
(declare-fun New_order_isN_v5 (T) Bool)
(declare-fun New_order_Var_v5 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v5 t0)) (exists ((r Customer))(= (New_order_Var_v5 t0) r))) 
                               (=> (exists ((r Customer))(= (New_order_Var_v5 t0) r)) (not (New_order_isN_v5 t0))))) :named v5-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Customer_Proj_c_id (New_order_Var_v5 t0)) (New_order_Param_input_c_id t0))) :named v5-select-prop))
;v6
(declare-fun New_order_isN_v6 (T) Bool)
(declare-fun New_order_Var_v6 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v6 t0)) (exists ((r Customer))(= (New_order_Var_v6 t0) r))) 
                               (=> (exists ((r Customer))(= (New_order_Var_v6 t0) r)) (not (New_order_isN_v6 t0))))) :named v6-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Customer_Proj_c_id (New_order_Var_v6 t0)) (New_order_Param_input_c_id t0))) :named v6-select-prop))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       RW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Delivery))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-delivery-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Stock_level))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-stock_level-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Order_status))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-order_status-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Payment))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-payment-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) New_order))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-new_order-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Delivery))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-delivery-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Stock_level))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-stock_level-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Order_status))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-order_status-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Payment))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-payment-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) New_order))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-new_order-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Delivery))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-delivery-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Stock_level))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-stock_level-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Order_status))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-order_status-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Payment))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-payment-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) New_order))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-new_order-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Delivery))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-delivery-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Stock_level))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-stock_level-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Order_status))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-order_status-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Payment))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-payment-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) New_order))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-new_order-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Delivery))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-delivery-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Stock_level))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-stock_level-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Order_status))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-order_status-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Payment))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-payment-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) New_order))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or false
                            (exists ((r District))
                                (and 
                                (IsAlive_District r t2)
                                (RW_District r t1 t2)
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t1)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t1)))  true
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t2)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t2)))  true))) )))
                                :named new_order-new_order-rw-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WR-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Delivery))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-delivery-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Stock_level))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-stock_level-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Order_status))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-order_status-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Payment))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-payment-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) New_order))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-new_order-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Delivery))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-delivery-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Stock_level))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-stock_level-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Order_status))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-order_status-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Payment))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-payment-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) New_order))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-new_order-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Delivery))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-delivery-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Stock_level))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-stock_level-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Order_status))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-order_status-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Payment))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-payment-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) New_order))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-new_order-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Delivery))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-delivery-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Stock_level))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-stock_level-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Order_status))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-order_status-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Payment))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-payment-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) New_order))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-new_order-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Delivery))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-delivery-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Stock_level))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-stock_level-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Order_status))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-order_status-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Payment))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-payment-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) New_order))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or false
                            (exists ((r District))
                                (and 
                                (IsAlive_District r t1)
                                (WR_District r t1 t2)
                                (not (New_order_isN_v3 t2))
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t2)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t2)))  true
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t1)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t1)))  true))) )))
                                :named new_order-new_order-wr-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Delivery))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-delivery-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Stock_level))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-stock_level-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Order_status))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-order_status-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Payment))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-payment-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) New_order))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named delivery-new_order-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Delivery))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-delivery-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Stock_level))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-stock_level-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Order_status))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-order_status-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Payment))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-payment-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) New_order))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named stock_level-new_order-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Delivery))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-delivery-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Stock_level))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-stock_level-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Order_status))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-order_status-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Payment))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-payment-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) New_order))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named order_status-new_order-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Delivery))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-delivery-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Stock_level))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-stock_level-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Order_status))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-order_status-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Payment))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-payment-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) New_order))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-new_order-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Delivery))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-delivery-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Stock_level))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-stock_level-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Order_status))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-order_status-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Payment))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-payment-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) New_order))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        (or false
                            (exists ((r District))
                                (and 
                                (WW_District r t1 t2)
                                (IsAlive_District r t1)
                                (IsAlive_District r t2)
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t1)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t1)))  true
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t2)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t2)))  true))) )))
                                :named new_order-new_order-ww-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WR Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Delivery) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named delivery-delivery-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Stock_level) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named delivery-stock_level-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Order_status) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named delivery-order_status-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Payment) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named delivery-payment-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) New_order) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named delivery-new_order-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Delivery) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named stock_level-delivery-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Stock_level) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named stock_level-stock_level-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Order_status) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named stock_level-order_status-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Payment) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named stock_level-payment-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) New_order) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named stock_level-new_order-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Delivery) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named order_status-delivery-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Stock_level) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named order_status-stock_level-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Order_status) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named order_status-order_status-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Payment) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named order_status-payment-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) New_order) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named order_status-new_order-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Delivery) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named payment-delivery-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Stock_level) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named payment-stock_level-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Order_status) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named payment-order_status-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Payment) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named payment-payment-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) New_order) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named payment-new_order-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Delivery) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named new_order-delivery-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Stock_level) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named new_order-stock_level-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Order_status) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named new_order-order_status-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Payment) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named new_order-payment-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) New_order) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named new_order-new_order-then-wr))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WW Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Delivery) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named delivery-delivery-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Stock_level) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named delivery-stock_level-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Order_status) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named delivery-order_status-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Payment) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named delivery-payment-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) New_order) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named delivery-new_order-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Delivery) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named stock_level-delivery-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Stock_level) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named stock_level-stock_level-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Order_status) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named stock_level-order_status-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Payment) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named stock_level-payment-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) New_order) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named stock_level-new_order-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Delivery) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named order_status-delivery-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Stock_level) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named order_status-stock_level-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Order_status) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named order_status-order_status-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Payment) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named order_status-payment-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) New_order) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named order_status-new_order-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Delivery) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named payment-delivery-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Stock_level) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named payment-stock_level-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Order_status) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named payment-order_status-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Payment) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named payment-payment-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) New_order) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named payment-new_order-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Delivery) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named new_order-delivery-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Stock_level) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named new_order-stock_level-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Order_status) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named new_order-order_status-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Payment) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named new_order-payment-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) New_order) (not (= t1 t2)))
                    (=> (or false
                            (exists ((r District))
                                (and 
                                (IsAlive_District r t1)
                                (IsAlive_District r t2)
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t1)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t1)))  true
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t2)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t2)))  true)))
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named new_order-new_order-then-ww))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                      Finalization                                                      
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(declare-fun D (T T) Bool)
(assert (! (forall ((t1 T)(t2 T)) (=> (D t1 t2) (or (WW t1 t2)(WR t1 t2)(RW t1 t2)))) :named gen-dep) )
(assert (! (exists ( (t1 T) (t2 T) (t3 T) (t4 T)) (and (not (= t1 t4))  (D t1 t2) (D t2 t3) (D t3 t4) (D t4 t1))) :named cycle))

;Guarantees
;CC 
(assert (! (forall ((t1 T) (t2 T) (t3 T))  (=> (and (vis  t1 t2) (vis  t2 t3)) (vis  t1 t3))):named cc))

(check-sat)
;(get-unsat-core)
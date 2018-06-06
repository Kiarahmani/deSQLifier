
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
  (and (= (Orders_Proj_o_id r1) (Orders_Proj_o_id r2))(= (Orders_Proj_o_did r1) (Orders_Proj_o_did r2))(= (Orders_Proj_o_wid r1) (Orders_Proj_o_wid r2)))(= r1 r2))) :named pk-orders) )
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
(declare-fun Orderline_Proj_ol_iid (Orderline) Int)
(declare-fun Orderline_Proj_ol_delivdate (Orderline) String)
(declare-fun Orderline_Proj_ol_info (Orderline) String)
(assert (! (forall ((r1 Orderline)(r2 Orderline)) (=>
  (and (= (Orderline_Proj_ol_oid r1) (Orderline_Proj_ol_oid r2))(= (Orderline_Proj_ol_did r1) (Orderline_Proj_ol_did r2))(= (Orderline_Proj_ol_wid r1) (Orderline_Proj_ol_wid r2))(= (Orderline_Proj_ol_number r1) (Orderline_Proj_ol_number r2)))(= r1 r2))) :named pk-orderline) )
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
(declare-fun Stock_Proj_s_ytd (Stock) Int)
(declare-fun Stock_Proj_s_quant (Stock) Int)
(declare-fun Stock_Proj_s_ordercnt (Stock) Int)
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
(declare-fun Delivery_Param_input_w_id (T) Int)
(declare-fun Delivery_Param_input_d_id (T) Int)
(declare-fun Delivery_Param_input_temp (T) Int)
(declare-fun Delivery_Param_input_temp2 (T) Int)
(declare-fun Delivery_Param_input_carrier_id (T) Int)
(declare-fun Stock_level_Param_input_w_id (T) Int)
(declare-fun Stock_level_Param_input_d_id (T) Int)
(declare-fun Order_status_Param_input_w_id (T) Int)
(declare-fun Order_status_Param_input_d_id (T) Int)
(declare-fun Order_status_Param_input_c_name (T) String)
(declare-fun Order_status_Param_input_c_id (T) Int)
(declare-fun Order_status_Param_input_cid_is_given (T) Bool)
(declare-fun Payment_Param_input_w_id (T) Int)
(declare-fun Payment_Param_input_d_id (T) Int)
(declare-fun Payment_Param_input_c_name (T) String)
(declare-fun Payment_Param_input_c_id (T) Int)
(declare-fun Payment_Param_input_h_amount (T) Int)
(declare-fun Payment_Param_input_cid_is_given (T) Bool)
(declare-fun New_order_Param_input_w_id (T) Int)
(declare-fun New_order_Param_input_d_id (T) Int)
(declare-fun New_order_Param_input_c_id (T) Int)
(declare-fun New_order_Param_input_o_id (T) Int)
(declare-fun New_order_Param_input_ol_qnt (T) Int)
(declare-fun New_order_SVar_input_item_list (T Item) Bool)

;v1
(declare-fun Delivery_SVar_v1 (T Neworder) Bool)
(assert (! (forall ((t0 T)(r Neworder)) (=> (Delivery_SVar_v1 t0 r) (and (= (Neworder_Proj_n_wid r) (Delivery_Param_input_w_id t0)) (= (Neworder_Proj_n_did r) (Delivery_Param_input_d_id t0))))) :named delivery-v1-var-prop))
;delivery_v2
(declare-fun Delivery_isN_v2 (T) Bool)
(declare-fun Delivery_Var_v2 (T) Neworder)
(assert (! (forall((t0 T))(and (=> (not (Delivery_isN_v2 t0)) (exists ((r Neworder))(= (Delivery_Var_v2 t0) r))) 
                               (=> (exists ((r Neworder))(= (Delivery_Var_v2 t0) r)) (not (Delivery_isN_v2 t0))))) :named delivery-v2-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Neworder_Proj_n_oid (Delivery_Var_v2 t0)) (Delivery_Param_input_temp t0))) :named delivery-v2-var-filter-prop))
(assert (! (forall ((t0 T))(Delivery_SVar_v1 t0 (Delivery_Var_v2 t0)))  :named delivery-v2-var-chosen-prop))
;delivery_v3
(declare-fun Delivery_isN_v3 (T) Bool)
(declare-fun Delivery_Var_v3 (T) Orders)
(assert (! (forall((t0 T))(and (=> (not (Delivery_isN_v3 t0)) (exists ((r Orders))(= (Delivery_Var_v3 t0) r))) 
                               (=> (exists ((r Orders))(= (Delivery_Var_v3 t0) r)) (not (Delivery_isN_v3 t0))))) :named delivery-v3-isnull-prop) )
(assert (! (forall ((t0 T)) (and (and (= (Orders_Proj_o_id (Delivery_Var_v3 t0)) (Neworder_Proj_n_oid (Delivery_Var_v2 t0))) (= (Orders_Proj_o_wid (Delivery_Var_v3 t0)) (Delivery_Param_input_w_id t0))) (= (Orders_Proj_o_did (Delivery_Var_v3 t0)) (Delivery_Param_input_d_id t0)))) :named delivery-v3-select-prop))
;v4
(declare-fun Delivery_SVar_v4 (T Orderline) Bool)
(assert (! (forall ((t0 T)(r Orderline)) (=> (Delivery_SVar_v4 t0 r) (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t0))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t0))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t0))))) :named delivery-v4-var-prop))
;delivery_v5
(declare-fun Delivery_isN_v5 (T) Bool)
(declare-fun Delivery_Var_v5 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (Delivery_isN_v5 t0)) (exists ((r Customer))(= (Delivery_Var_v5 t0) r))) 
                               (=> (exists ((r Customer))(= (Delivery_Var_v5 t0) r)) (not (Delivery_isN_v5 t0))))) :named delivery-v5-isnull-prop) )
(assert (! (forall ((t0 T)) (and (and (= (Customer_Proj_c_wid (Delivery_Var_v5 t0)) (Delivery_Param_input_w_id t0)) (= (Customer_Proj_c_did (Delivery_Var_v5 t0)) (Delivery_Param_input_d_id t0))) (= (Customer_Proj_c_id (Delivery_Var_v5 t0)) (Orders_Proj_o_cid (Delivery_Var_v3 t0))))) :named delivery-v5-select-prop))
;stock_level_v1
(declare-fun Stock_level_isN_v1 (T) Bool)
(declare-fun Stock_level_Var_v1 (T) District)
(assert (! (forall((t0 T))(and (=> (not (Stock_level_isN_v1 t0)) (exists ((r District))(= (Stock_level_Var_v1 t0) r))) 
                               (=> (exists ((r District))(= (Stock_level_Var_v1 t0) r)) (not (Stock_level_isN_v1 t0))))) :named stock_level-v1-isnull-prop) )
(assert (! (forall ((t0 T)) (and (= (District_Proj_d_wid (Stock_level_Var_v1 t0)) (Stock_level_Param_input_w_id t0)) (= (District_Proj_d_id (Stock_level_Var_v1 t0)) (Stock_level_Param_input_d_id t0)))) :named stock_level-v1-select-prop))
;v2
(declare-fun Stock_level_SVar_v2 (T Orderline) Bool)
(assert (! (forall ((t0 T)(r Orderline)) (=> (Stock_level_SVar_v2 t0 r) (and (and (and (> (Orderline_Proj_ol_oid r) (- (District_Proj_d_nextoid (Stock_level_Var_v1 t0)) 20)) (< (Orderline_Proj_ol_oid r) (District_Proj_d_nextoid (Stock_level_Var_v1 t0)))) (= (Orderline_Proj_ol_wid r) (Stock_level_Param_input_w_id t0))) (= (Orderline_Proj_ol_did r) (Stock_level_Param_input_d_id t0))))) :named stock_level-v2-var-prop))
;stock_level_loop_var_1
(declare-fun Stock_level_isN_loop_var_1 (T) Bool)
(declare-fun Stock_level_Var_loop_var_1 (T) Orderline)
(assert (! (forall((t0 T))(and (=> (not (Stock_level_isN_loop_var_1 t0)) (exists ((r Orderline))(= (Stock_level_Var_loop_var_1 t0) r))) 
                               (=> (exists ((r Orderline))(= (Stock_level_Var_loop_var_1 t0) r)) (not (Stock_level_isN_loop_var_1 t0))))) :named stock_level-loop_var_1-isnull-prop) )
(assert (! (forall ((t0 T)) true) :named stock_level-loop_var_1-var-filter-prop))
(assert (! (forall ((t0 T))(Stock_level_SVar_v2 t0 (Stock_level_Var_loop_var_1 t0)))  :named stock_level-loop_var_1-var-chosen-prop))
;v3
(declare-fun Stock_level_SVar_v3 (T Stock) Bool)
(assert (! (forall ((t0 T)(r Stock)) (=> (Stock_level_SVar_v3 t0 r) (and (= (Stock_Proj_s_iid r) (Orderline_Proj_ol_iid (Stock_level_Var_loop_var_1 t0))) (= (Stock_Proj_s_wid r) (Stock_level_Param_input_w_id t0))))) :named stock_level-v3-var-prop))
;order_status_v1
(declare-fun Order_status_isN_v1 (T) Bool)
(declare-fun Order_status_Var_v1 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (Order_status_isN_v1 t0)) (exists ((r Customer))(= (Order_status_Var_v1 t0) r))) 
                               (=> (exists ((r Customer))(= (Order_status_Var_v1 t0) r)) (not (Order_status_isN_v1 t0))))) :named order_status-v1-isnull-prop) )
(assert (! (forall ((t0 T)) (and (and (= (Customer_Proj_c_wid (Order_status_Var_v1 t0)) (Order_status_Param_input_w_id t0)) (= (Customer_Proj_c_did (Order_status_Var_v1 t0)) (Order_status_Param_input_d_id t0))) (= (Customer_Proj_c_id (Order_status_Var_v1 t0)) (Order_status_Param_input_c_id t0)))) :named order_status-v1-select-prop))
;v4
(declare-fun Order_status_SVar_v4 (T Orders) Bool)
(assert (! (forall ((t0 T)(r Orders)) (=> (Order_status_SVar_v4 t0 r) (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v1 t0))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t0))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t0))))) :named order_status-v4-var-prop))
;order_status_v7
(declare-fun Order_status_isN_v7 (T) Bool)
(declare-fun Order_status_Var_v7 (T) Orders)
(assert (! (forall((t0 T))(and (=> (not (Order_status_isN_v7 t0)) (exists ((r Orders))(= (Order_status_Var_v7 t0) r))) 
                               (=> (exists ((r Orders))(= (Order_status_Var_v7 t0) r)) (not (Order_status_isN_v7 t0))))) :named order_status-v7-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Orders_Proj_o_id (Order_status_Var_v7 t0)) 50)) :named order_status-v7-var-filter-prop))
(assert (! (forall ((t0 T))(Order_status_SVar_v4 t0 (Order_status_Var_v7 t0)))  :named order_status-v7-var-chosen-prop))
;v9
(declare-fun Order_status_SVar_v9 (T Orderline) Bool)
(assert (! (forall ((t0 T)(r Orderline)) (=> (Order_status_SVar_v9 t0 r) (and (and (= (Orderline_Proj_ol_wid r) (Order_status_Param_input_w_id t0)) (= (Orderline_Proj_ol_did r) (Order_status_Param_input_d_id t0))) (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Order_status_Var_v7 t0)))))) :named order_status-v9-var-prop))
;v2
(declare-fun Order_status_SVar_v2 (T Customer) Bool)
(assert (! (forall ((t0 T)(r Customer)) (=> (Order_status_SVar_v2 t0 r) (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t0)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t0))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t0))))) :named order_status-v2-var-prop))
;order_status_v3
(declare-fun Order_status_isN_v3 (T) Bool)
(declare-fun Order_status_Var_v3 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (Order_status_isN_v3 t0)) (exists ((r Customer))(= (Order_status_Var_v3 t0) r))) 
                               (=> (exists ((r Customer))(= (Order_status_Var_v3 t0) r)) (not (Order_status_isN_v3 t0))))) :named order_status-v3-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Customer_Proj_c_id (Order_status_Var_v3 t0)) 50)) :named order_status-v3-var-filter-prop))
(assert (! (forall ((t0 T))(Order_status_SVar_v2 t0 (Order_status_Var_v3 t0)))  :named order_status-v3-var-chosen-prop))
;v5
(declare-fun Order_status_SVar_v5 (T Orders) Bool)
(assert (! (forall ((t0 T)(r Orders)) (=> (Order_status_SVar_v5 t0 r) (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v3 t0))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t0))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t0))))) :named order_status-v5-var-prop))
;order_status_v6
(declare-fun Order_status_isN_v6 (T) Bool)
(declare-fun Order_status_Var_v6 (T) Orders)
(assert (! (forall((t0 T))(and (=> (not (Order_status_isN_v6 t0)) (exists ((r Orders))(= (Order_status_Var_v6 t0) r))) 
                               (=> (exists ((r Orders))(= (Order_status_Var_v6 t0) r)) (not (Order_status_isN_v6 t0))))) :named order_status-v6-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Orders_Proj_o_id (Order_status_Var_v6 t0)) 50)) :named order_status-v6-var-filter-prop))
(assert (! (forall ((t0 T))(Order_status_SVar_v5 t0 (Order_status_Var_v6 t0)))  :named order_status-v6-var-chosen-prop))
;v8
(declare-fun Order_status_SVar_v8 (T Orderline) Bool)
(assert (! (forall ((t0 T)(r Orderline)) (=> (Order_status_SVar_v8 t0 r) (and (and (= (Orderline_Proj_ol_wid r) (Order_status_Param_input_w_id t0)) (= (Orderline_Proj_ol_did r) (Order_status_Param_input_d_id t0))) (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Order_status_Var_v6 t0)))))) :named order_status-v8-var-prop))
;payment_v1
(declare-fun Payment_isN_v1 (T) Bool)
(declare-fun Payment_Var_v1 (T) Warehouse)
(assert (! (forall((t0 T))(and (=> (not (Payment_isN_v1 t0)) (exists ((r Warehouse))(= (Payment_Var_v1 t0) r))) 
                               (=> (exists ((r Warehouse))(= (Payment_Var_v1 t0) r)) (not (Payment_isN_v1 t0))))) :named payment-v1-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Warehouse_Proj_w_id (Payment_Var_v1 t0)) (Payment_Param_input_w_id t0))) :named payment-v1-select-prop))
;payment_v2
(declare-fun Payment_isN_v2 (T) Bool)
(declare-fun Payment_Var_v2 (T) District)
(assert (! (forall((t0 T))(and (=> (not (Payment_isN_v2 t0)) (exists ((r District))(= (Payment_Var_v2 t0) r))) 
                               (=> (exists ((r District))(= (Payment_Var_v2 t0) r)) (not (Payment_isN_v2 t0))))) :named payment-v2-isnull-prop) )
(assert (! (forall ((t0 T)) (and (= (District_Proj_d_wid (Payment_Var_v2 t0)) (Payment_Param_input_w_id t0)) (= (District_Proj_d_id (Payment_Var_v2 t0)) (Payment_Param_input_d_id t0)))) :named payment-v2-select-prop))
;payment_v3
(declare-fun Payment_isN_v3 (T) Bool)
(declare-fun Payment_Var_v3 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (Payment_isN_v3 t0)) (exists ((r Customer))(= (Payment_Var_v3 t0) r))) 
                               (=> (exists ((r Customer))(= (Payment_Var_v3 t0) r)) (not (Payment_isN_v3 t0))))) :named payment-v3-isnull-prop) )
(assert (! (forall ((t0 T)) (and (and (= (Customer_Proj_c_wid (Payment_Var_v3 t0)) (Payment_Param_input_w_id t0)) (= (Customer_Proj_c_did (Payment_Var_v3 t0)) (Payment_Param_input_d_id t0))) (= (Customer_Proj_c_id (Payment_Var_v3 t0)) (Payment_Param_input_c_id t0)))) :named payment-v3-select-prop))
;payment_v4
(declare-fun Payment_isN_v4 (T) Bool)
(declare-fun Payment_Var_v4 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (Payment_isN_v4 t0)) (exists ((r Customer))(= (Payment_Var_v4 t0) r))) 
                               (=> (exists ((r Customer))(= (Payment_Var_v4 t0) r)) (not (Payment_isN_v4 t0))))) :named payment-v4-isnull-prop) )
(assert (! (forall ((t0 T)) (and (and (= (Customer_Proj_c_wid (Payment_Var_v4 t0)) (Payment_Param_input_w_id t0)) (= (Customer_Proj_c_did (Payment_Var_v4 t0)) (Payment_Param_input_d_id t0))) (= (Customer_Proj_c_id (Payment_Var_v4 t0)) (Payment_Param_input_c_id t0)))) :named payment-v4-select-prop))
;payment_v5
(declare-fun Payment_isN_v5 (T) Bool)
(declare-fun Payment_Var_v5 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (Payment_isN_v5 t0)) (exists ((r Customer))(= (Payment_Var_v5 t0) r))) 
                               (=> (exists ((r Customer))(= (Payment_Var_v5 t0) r)) (not (Payment_isN_v5 t0))))) :named payment-v5-isnull-prop) )
(assert (! (forall ((t0 T)) (and (and (= (Customer_Proj_c_wid (Payment_Var_v5 t0)) (Payment_Param_input_w_id t0)) (= (Customer_Proj_c_did (Payment_Var_v5 t0)) (Payment_Param_input_d_id t0))) (= (Customer_Proj_c_id (Payment_Var_v5 t0)) (Payment_Param_input_c_id t0)))) :named payment-v5-select-prop))
;v6
(declare-fun Payment_SVar_v6 (T Customer) Bool)
(assert (! (forall ((t0 T)(r Customer)) (=> (Payment_SVar_v6 t0 r) (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t0)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t0))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t0))))) :named payment-v6-var-prop))
;payment_v7
(declare-fun Payment_isN_v7 (T) Bool)
(declare-fun Payment_Var_v7 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (Payment_isN_v7 t0)) (exists ((r Customer))(= (Payment_Var_v7 t0) r))) 
                               (=> (exists ((r Customer))(= (Payment_Var_v7 t0) r)) (not (Payment_isN_v7 t0))))) :named payment-v7-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Customer_Proj_c_id (Payment_Var_v7 t0)) 50)) :named payment-v7-var-filter-prop))
(assert (! (forall ((t0 T))(Payment_SVar_v6 t0 (Payment_Var_v7 t0)))  :named payment-v7-var-chosen-prop))
;new_order_v1
(declare-fun New_order_isN_v1 (T) Bool)
(declare-fun New_order_Var_v1 (T) Warehouse)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v1 t0)) (exists ((r Warehouse))(= (New_order_Var_v1 t0) r))) 
                               (=> (exists ((r Warehouse))(= (New_order_Var_v1 t0) r)) (not (New_order_isN_v1 t0))))) :named new_order-v1-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Warehouse_Proj_w_id (New_order_Var_v1 t0)) (New_order_Param_input_w_id t0))) :named new_order-v1-select-prop))
;new_order_v2
(declare-fun New_order_isN_v2 (T) Bool)
(declare-fun New_order_Var_v2 (T) District)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v2 t0)) (exists ((r District))(= (New_order_Var_v2 t0) r))) 
                               (=> (exists ((r District))(= (New_order_Var_v2 t0) r)) (not (New_order_isN_v2 t0))))) :named new_order-v2-isnull-prop) )
(assert (! (forall ((t0 T)) (= (District_Proj_d_id (New_order_Var_v2 t0)) (New_order_Param_input_d_id t0))) :named new_order-v2-select-prop))
;new_order_v3
(declare-fun New_order_isN_v3 (T) Bool)
(declare-fun New_order_Var_v3 (T) District)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v3 t0)) (exists ((r District))(= (New_order_Var_v3 t0) r))) 
                               (=> (exists ((r District))(= (New_order_Var_v3 t0) r)) (not (New_order_isN_v3 t0))))) :named new_order-v3-isnull-prop) )
(assert (! (forall ((t0 T)) (and (= (District_Proj_d_wid (New_order_Var_v3 t0)) (New_order_Param_input_w_id t0)) (= (District_Proj_d_id (New_order_Var_v3 t0)) (New_order_Param_input_d_id t0)))) :named new_order-v3-select-prop))
;new_order_v4
(declare-fun New_order_isN_v4 (T) Bool)
(declare-fun New_order_Var_v4 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v4 t0)) (exists ((r Customer))(= (New_order_Var_v4 t0) r))) 
                               (=> (exists ((r Customer))(= (New_order_Var_v4 t0) r)) (not (New_order_isN_v4 t0))))) :named new_order-v4-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Customer_Proj_c_id (New_order_Var_v4 t0)) (New_order_Param_input_c_id t0))) :named new_order-v4-select-prop))
;new_order_v5
(declare-fun New_order_isN_v5 (T) Bool)
(declare-fun New_order_Var_v5 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v5 t0)) (exists ((r Customer))(= (New_order_Var_v5 t0) r))) 
                               (=> (exists ((r Customer))(= (New_order_Var_v5 t0) r)) (not (New_order_isN_v5 t0))))) :named new_order-v5-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Customer_Proj_c_id (New_order_Var_v5 t0)) (New_order_Param_input_c_id t0))) :named new_order-v5-select-prop))
;new_order_v6
(declare-fun New_order_isN_v6 (T) Bool)
(declare-fun New_order_Var_v6 (T) Customer)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v6 t0)) (exists ((r Customer))(= (New_order_Var_v6 t0) r))) 
                               (=> (exists ((r Customer))(= (New_order_Var_v6 t0) r)) (not (New_order_isN_v6 t0))))) :named new_order-v6-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Customer_Proj_c_id (New_order_Var_v6 t0)) (New_order_Param_input_c_id t0))) :named new_order-v6-select-prop))
;new_order_loop_var_1
(declare-fun New_order_isN_loop_var_1 (T) Bool)
(declare-fun New_order_Var_loop_var_1 (T) Item)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_loop_var_1 t0)) (exists ((r Item))(= (New_order_Var_loop_var_1 t0) r))) 
                               (=> (exists ((r Item))(= (New_order_Var_loop_var_1 t0) r)) (not (New_order_isN_loop_var_1 t0))))) :named new_order-loop_var_1-isnull-prop) )
(assert (! (forall ((t0 T)) true) :named new_order-loop_var_1-var-filter-prop))
(assert (! (forall ((t0 T))(New_order_SVar_input_item_list t0 (New_order_Var_loop_var_1 t0)))  :named new_order-loop_var_1-var-chosen-prop))
;new_order_v7
(declare-fun New_order_isN_v7 (T) Bool)
(declare-fun New_order_Var_v7 (T) Item)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v7 t0)) (exists ((r Item))(= (New_order_Var_v7 t0) r))) 
                               (=> (exists ((r Item))(= (New_order_Var_v7 t0) r)) (not (New_order_isN_v7 t0))))) :named new_order-v7-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Item_Proj_i_id (New_order_Var_v7 t0)) (Item_Proj_i_id (New_order_Var_loop_var_1 t0)))) :named new_order-v7-select-prop))
;new_order_v8
(declare-fun New_order_isN_v8 (T) Bool)
(declare-fun New_order_Var_v8 (T) Stock)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v8 t0)) (exists ((r Stock))(= (New_order_Var_v8 t0) r))) 
                               (=> (exists ((r Stock))(= (New_order_Var_v8 t0) r)) (not (New_order_isN_v8 t0))))) :named new_order-v8-isnull-prop) )
(assert (! (forall ((t0 T)) (and (= (Stock_Proj_s_wid (New_order_Var_v8 t0)) (New_order_Param_input_w_id t0)) (= (Stock_Proj_s_iid (New_order_Var_v8 t0)) (Item_Proj_i_id (New_order_Var_loop_var_1 t0))))) :named new_order-v8-select-prop))
;new_order_v9
(declare-fun New_order_isN_v9 (T) Bool)
(declare-fun New_order_Var_v9 (T) Stock)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v9 t0)) (exists ((r Stock))(= (New_order_Var_v9 t0) r))) 
                               (=> (exists ((r Stock))(= (New_order_Var_v9 t0) r)) (not (New_order_isN_v9 t0))))) :named new_order-v9-isnull-prop) )
(assert (! (forall ((t0 T)) (and (= (Stock_Proj_s_wid (New_order_Var_v9 t0)) (New_order_Param_input_w_id t0)) (= (Stock_Proj_s_iid (New_order_Var_v9 t0)) (Item_Proj_i_id (New_order_Var_loop_var_1 t0))))) :named new_order-v9-select-prop))
;new_order_v10
(declare-fun New_order_isN_v10 (T) Bool)
(declare-fun New_order_Var_v10 (T) Stock)
(assert (! (forall((t0 T))(and (=> (not (New_order_isN_v10 t0)) (exists ((r Stock))(= (New_order_Var_v10 t0) r))) 
                               (=> (exists ((r Stock))(= (New_order_Var_v10 t0) r)) (not (New_order_isN_v10 t0))))) :named new_order-v10-isnull-prop) )
(assert (! (forall ((t0 T)) (and (= (Stock_Proj_s_wid (New_order_Var_v10 t0)) (New_order_Param_input_w_id t0)) (= (Stock_Proj_s_iid (New_order_Var_v10 t0)) (Item_Proj_i_id (New_order_Var_loop_var_1 t0))))) :named new_order-v10-select-prop))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       RW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Delivery))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or false
                            (exists ((r Neworder))
                                (and 
                                (and (= (Neworder_Proj_n_wid r) (Delivery_Param_input_w_id t1)) (= (Neworder_Proj_n_did r) (Delivery_Param_input_d_id t1)))  true
                                (and (and (= (Neworder_Proj_n_oid r) (Delivery_Param_input_temp t2)) (= (Neworder_Proj_n_wid r) (Delivery_Param_input_w_id t2))) (= (Neworder_Proj_n_did r) (Delivery_Param_input_d_id t2)))  true
                                (IsAlive_Neworder r t2)
                                (RW_Alive_Neworder r t1 t2))))
                            (exists ((r Orderline))
                                (and 
                                (IsAlive_Orderline r t2)
                                (RW_Orderline r t1 t2)
                                (not (Delivery_SVar_v4 t1 r))
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t1))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t1))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t1)))  true
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t2))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t2))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t2)))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true))) )))
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
                        (or (or false
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))))) )))
                                :named delivery-payment-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) New_order))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                            (exists ((r Neworder))
                                (and 
                                (and (= (Neworder_Proj_n_wid r) (Delivery_Param_input_w_id t1)) (= (Neworder_Proj_n_did r) (Delivery_Param_input_d_id t1)))  true
                                ;insert
                                (= (Neworder_Proj_n_oid r) (New_order_Param_input_o_id t2))
                                (= (Neworder_Proj_n_did r) (New_order_Param_input_d_id t2))
                                (= (Neworder_Proj_n_wid r) (New_order_Param_input_w_id t2))  true
                                (not (IsAlive_Neworder r t1))
                                (RW_Alive_Neworder r t1 t2))))
                            (exists ((r Orders))
                                (and 
                                (and (and (= (Orders_Proj_o_id r) (Neworder_Proj_n_oid (Delivery_Var_v2 t1))) (= (Orders_Proj_o_wid r) (Delivery_Param_input_w_id t1))) (= (Orders_Proj_o_did r) (Delivery_Param_input_d_id t1)))  true
                                ;insert
                                (= (Orders_Proj_o_id r) (New_order_Param_input_o_id t2))
                                (= (Orders_Proj_o_cid r) (New_order_Param_input_c_id t2))
                                (= (Orders_Proj_o_did r) (New_order_Param_input_d_id t2))
                                (= (Orders_Proj_o_wid r) (New_order_Param_input_w_id t2))
                                (= (Orders_Proj_o_carrierid r) 0)
                                (= (Orders_Proj_o_entrydate r) "06/05/2018")  true
                                (not (IsAlive_Orders r t1))
                                (RW_Alive_Orders r t1 t2)))) )))
                                :named delivery-new_order-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Stock_level) (= (type t2) Delivery))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or false
                            (exists ((r Orderline))
                                (and 
                                (IsAlive_Orderline r t2)
                                (RW_Orderline r t1 t2)
                                (not (Stock_level_SVar_v2 t1 r))
                                (and (and (and (> (Orderline_Proj_ol_oid r) (- (District_Proj_d_nextoid (Stock_level_Var_v1 t1)) 20)) (< (Orderline_Proj_ol_oid r) (District_Proj_d_nextoid (Stock_level_Var_v1 t1)))) (= (Orderline_Proj_ol_wid r) (Stock_level_Param_input_w_id t1))) (= (Orderline_Proj_ol_did r) (Stock_level_Param_input_d_id t1)))  true
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t2))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t2))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t2)))  true))) )))
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
                        (or (or (or (or (or false
                            (exists ((r District))
                                (and 
                                (IsAlive_District r t2)
                                (RW_District r t1 t2)
                                (and (= (District_Proj_d_wid r) (Stock_level_Param_input_w_id t1)) (= (District_Proj_d_id r) (Stock_level_Param_input_d_id t1)))  true
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t2)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t2)))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t2)
                                (RW_Stock r t1 t2)
                                (not (Stock_level_SVar_v3 t1 r))
                                (and (= (Stock_Proj_s_iid r) (Orderline_Proj_ol_iid (Stock_level_Var_loop_var_1 t1))) (= (Stock_Proj_s_wid r) (Stock_level_Param_input_w_id t1)))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t2)
                                (RW_Stock r t1 t2)
                                (not (Stock_level_SVar_v3 t1 r))
                                (and (= (Stock_Proj_s_iid r) (Orderline_Proj_ol_iid (Stock_level_Var_loop_var_1 t1))) (= (Stock_Proj_s_wid r) (Stock_level_Param_input_w_id t1)))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t2)
                                (RW_Stock r t1 t2)
                                (not (Stock_level_SVar_v3 t1 r))
                                (and (= (Stock_Proj_s_iid r) (Orderline_Proj_ol_iid (Stock_level_Var_loop_var_1 t1))) (= (Stock_Proj_s_wid r) (Stock_level_Param_input_w_id t1)))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10)))))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t2)
                                (RW_Stock r t1 t2)
                                (not (Stock_level_SVar_v3 t1 r))
                                (and (= (Stock_Proj_s_iid r) (Orderline_Proj_ol_iid (Stock_level_Var_loop_var_1 t1))) (= (Stock_Proj_s_wid r) (Stock_level_Param_input_w_id t1)))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10)))))) )))
                                :named stock_level-new_order-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) Delivery))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or false
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Order_status_Param_input_c_id t1)))  (and true (Order_status_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true)))
                            (exists ((r Orders))
                                (and 
                                (IsAlive_Orders r t2)
                                (RW_Orders r t1 t2)
                                (not (Order_status_SVar_v4 t1 r))
                                (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v1 t1))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t1))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t1)))  (and true (Order_status_Param_input_cid_is_given t1))
                                (and (and (= (Orders_Proj_o_id r) (Neworder_Proj_n_oid (Delivery_Var_v2 t2))) (= (Orders_Proj_o_wid r) (Delivery_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Delivery_Param_input_d_id t2)))  true)))
                            (exists ((r Orderline))
                                (and 
                                (IsAlive_Orderline r t2)
                                (RW_Orderline r t1 t2)
                                (not (Order_status_SVar_v9 t1 r))
                                (and (and (= (Orderline_Proj_ol_wid r) (Order_status_Param_input_w_id t1)) (= (Orderline_Proj_ol_did r) (Order_status_Param_input_d_id t1))) (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Order_status_Var_v7 t1))))  (and true (Order_status_Param_input_cid_is_given t1))
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t2))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t2))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t2)))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Order_status_SVar_v2 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t1)))  (and true (not (Order_status_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Order_status_SVar_v2 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t1)))  (and true (not (Order_status_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true)))
                            (exists ((r Orders))
                                (and 
                                (IsAlive_Orders r t2)
                                (RW_Orders r t1 t2)
                                (not (Order_status_SVar_v5 t1 r))
                                (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v3 t1))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t1))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t1)))  (and true (not (Order_status_Param_input_cid_is_given t1)))
                                (and (and (= (Orders_Proj_o_id r) (Neworder_Proj_n_oid (Delivery_Var_v2 t2))) (= (Orders_Proj_o_wid r) (Delivery_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Delivery_Param_input_d_id t2)))  true)))
                            (exists ((r Orderline))
                                (and 
                                (IsAlive_Orderline r t2)
                                (RW_Orderline r t1 t2)
                                (not (Order_status_SVar_v8 t1 r))
                                (and (and (= (Orderline_Proj_ol_wid r) (Order_status_Param_input_w_id t1)) (= (Orderline_Proj_ol_did r) (Order_status_Param_input_d_id t1))) (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Order_status_Var_v6 t1))))  (and true (not (Order_status_Param_input_cid_is_given t1)))
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t2))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t2))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t2)))  true))) )))
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
                        (or (or (or (or (or (or (or (or false
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Order_status_Param_input_c_id t1)))  (and true (Order_status_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Order_status_Param_input_c_id t1)))  (and true (Order_status_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Order_status_SVar_v2 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t1)))  (and true (not (Order_status_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Order_status_SVar_v2 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t1)))  (and true (not (Order_status_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Order_status_SVar_v2 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t1)))  (and true (not (Order_status_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Order_status_SVar_v2 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t1)))  (and true (not (Order_status_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Order_status_SVar_v2 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t1)))  (and true (not (Order_status_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Order_status_SVar_v2 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t1)))  (and true (not (Order_status_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))))) )))
                                :named order_status-payment-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Order_status) (= (type t2) New_order))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                            (exists ((r Orders))
                                (and 
                                (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v1 t1))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t1))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t1)))  (and true (Order_status_Param_input_cid_is_given t1))
                                ;insert
                                (= (Orders_Proj_o_id r) (New_order_Param_input_o_id t2))
                                (= (Orders_Proj_o_cid r) (New_order_Param_input_c_id t2))
                                (= (Orders_Proj_o_did r) (New_order_Param_input_d_id t2))
                                (= (Orders_Proj_o_wid r) (New_order_Param_input_w_id t2))
                                (= (Orders_Proj_o_carrierid r) 0)
                                (= (Orders_Proj_o_entrydate r) "06/05/2018")  true
                                (not (IsAlive_Orders r t1))
                                (RW_Alive_Orders r t1 t2))))
                            (exists ((r Orders))
                                (and 
                                (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v3 t1))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t1))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t1)))  (and true (not (Order_status_Param_input_cid_is_given t1)))
                                ;insert
                                (= (Orders_Proj_o_id r) (New_order_Param_input_o_id t2))
                                (= (Orders_Proj_o_cid r) (New_order_Param_input_c_id t2))
                                (= (Orders_Proj_o_did r) (New_order_Param_input_d_id t2))
                                (= (Orders_Proj_o_wid r) (New_order_Param_input_w_id t2))
                                (= (Orders_Proj_o_carrierid r) 0)
                                (= (Orders_Proj_o_entrydate r) "06/05/2018")  true
                                (not (IsAlive_Orders r t1))
                                (RW_Alive_Orders r t1 t2)))) )))
                                :named order_status-new_order-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Delivery))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or false
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Payment_SVar_v6 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Payment_SVar_v6 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true))) )))
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
                        (or (or (or (or (or (or (or (or (or (or (or (or (or (or false
                            (exists ((r Warehouse))
                                (and 
                                (IsAlive_Warehouse r t2)
                                (RW_Warehouse r t1 t2)
                                (= (Warehouse_Proj_w_id r) (Payment_Param_input_w_id t1))  true
                                (= (Warehouse_Proj_w_id r) (Payment_Param_input_w_id t2))  true)))
                            (exists ((r District))
                                (and 
                                (IsAlive_District r t2)
                                (RW_District r t1 t2)
                                (and (= (District_Proj_d_wid r) (Payment_Param_input_w_id t1)) (= (District_Proj_d_id r) (Payment_Param_input_d_id t1)))  true
                                (and (= (District_Proj_d_wid r) (Payment_Param_input_w_id t2)) (= (District_Proj_d_id r) (Payment_Param_input_d_id t2)))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Payment_SVar_v6 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Payment_SVar_v6 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Payment_SVar_v6 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Payment_SVar_v6 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Payment_SVar_v6 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t2)
                                (RW_Customer r t1 t2)
                                (not (Payment_SVar_v6 t1 r))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))))) )))
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
                        (or (or (or (or (or false
                            (exists ((r District))
                                (and 
                                (IsAlive_District r t2)
                                (RW_District r t1 t2)
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t1)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t1)))  true
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t2)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t2)))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t2)
                                (RW_Stock r t1 t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t2)
                                (RW_Stock r t1 t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t2)
                                (RW_Stock r t1 t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10)))))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t2)
                                (RW_Stock r t1 t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10)))))) )))
                                :named new_order-new_order-rw-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WR-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Delivery))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or false
                            (exists ((r Neworder))
                                (and 
                                (and (= (Neworder_Proj_n_wid r) (Delivery_Param_input_w_id t2)) (= (Neworder_Proj_n_did r) (Delivery_Param_input_d_id t2)))  true
                                (and (and (= (Neworder_Proj_n_oid r) (Delivery_Param_input_temp t1)) (= (Neworder_Proj_n_wid r) (Delivery_Param_input_w_id t1))) (= (Neworder_Proj_n_did r) (Delivery_Param_input_d_id t1)))  true
                                (IsAlive_Neworder r t1)
                                (not (IsAlive_Neworder r t2))
                                (WR_Alive_Neworder r t1 t2))))
                            (exists ((r Orderline))
                                (and 
                                (IsAlive_Orderline r t1)
                                (WR_Orderline r t1 t2)
                                (Delivery_SVar_v4 t2 r)
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t2))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t2))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t2)))  true
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t1))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t1))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t1)))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Delivery_isN_v5 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true))) )))
                                :named delivery-delivery-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Stock_level))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or false
                            (exists ((r Orderline))
                                (and 
                                (IsAlive_Orderline r t1)
                                (WR_Orderline r t1 t2)
                                (Stock_level_SVar_v2 t2 r)
                                (and (and (and (> (Orderline_Proj_ol_oid r) (- (District_Proj_d_nextoid (Stock_level_Var_v1 t2)) 20)) (< (Orderline_Proj_ol_oid r) (District_Proj_d_nextoid (Stock_level_Var_v1 t2)))) (= (Orderline_Proj_ol_wid r) (Stock_level_Param_input_w_id t2))) (= (Orderline_Proj_ol_did r) (Stock_level_Param_input_d_id t2)))  true
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t1))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t1))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t1)))  true))) )))
                                :named delivery-stock_level-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Order_status))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or false
                            (exists ((r Orders))
                                (and 
                                (IsAlive_Orders r t1)
                                (WR_Orders r t1 t2)
                                (Order_status_SVar_v4 t2 r)
                                (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v1 t2))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t2)))  (and true (Order_status_Param_input_cid_is_given t2))
                                (and (and (= (Orders_Proj_o_id r) (Neworder_Proj_n_oid (Delivery_Var_v2 t1))) (= (Orders_Proj_o_wid r) (Delivery_Param_input_w_id t1))) (= (Orders_Proj_o_did r) (Delivery_Param_input_d_id t1)))  true)))
                            (exists ((r Orders))
                                (and 
                                (IsAlive_Orders r t1)
                                (WR_Orders r t1 t2)
                                (Order_status_SVar_v5 t2 r)
                                (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v3 t2))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t2)))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                (and (and (= (Orders_Proj_o_id r) (Neworder_Proj_n_oid (Delivery_Var_v2 t1))) (= (Orders_Proj_o_wid r) (Delivery_Param_input_w_id t1))) (= (Orders_Proj_o_did r) (Delivery_Param_input_d_id t1)))  true)))
                            (exists ((r Orderline))
                                (and 
                                (IsAlive_Orderline r t1)
                                (WR_Orderline r t1 t2)
                                (Order_status_SVar_v9 t2 r)
                                (and (and (= (Orderline_Proj_ol_wid r) (Order_status_Param_input_w_id t2)) (= (Orderline_Proj_ol_did r) (Order_status_Param_input_d_id t2))) (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Order_status_Var_v7 t2))))  (and true (Order_status_Param_input_cid_is_given t2))
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t1))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t1))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t1)))  true)))
                            (exists ((r Orderline))
                                (and 
                                (IsAlive_Orderline r t1)
                                (WR_Orderline r t1 t2)
                                (Order_status_SVar_v8 t2 r)
                                (and (and (= (Orderline_Proj_ol_wid r) (Order_status_Param_input_w_id t2)) (= (Orderline_Proj_ol_did r) (Order_status_Param_input_d_id t2))) (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Order_status_Var_v6 t2))))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t1))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t1))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t1)))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Order_status_isN_v1 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Order_status_Param_input_c_id t2)))  (and true (Order_status_Param_input_cid_is_given t2))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Order_status_SVar_v2 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t2)))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Order_status_SVar_v2 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t2)))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true))) )))
                                :named delivery-order_status-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Payment))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or false
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Payment_isN_v3 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Payment_SVar_v6 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Payment_SVar_v6 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true))) )))
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
                        (or (or false
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Delivery_isN_v5 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Delivery_isN_v5 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))))) )))
                                :named payment-delivery-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Stock_level))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-stock_level-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Order_status))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or false
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Order_status_isN_v1 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Order_status_Param_input_c_id t2)))  (and true (Order_status_Param_input_cid_is_given t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Order_status_SVar_v2 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t2)))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Order_status_SVar_v2 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t2)))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Order_status_SVar_v2 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t2)))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Order_status_isN_v1 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Order_status_Param_input_c_id t2)))  (and true (Order_status_Param_input_cid_is_given t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Order_status_SVar_v2 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t2)))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Order_status_SVar_v2 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t2)))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Order_status_SVar_v2 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Order_status_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Order_status_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Order_status_Param_input_c_name t2)))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))))) )))
                                :named payment-order_status-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) Payment))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or (or (or (or (or (or (or false
                            (exists ((r Warehouse))
                                (and 
                                (IsAlive_Warehouse r t1)
                                (WR_Warehouse r t1 t2)
                                (not (Payment_isN_v1 t2))
                                (= (Warehouse_Proj_w_id r) (Payment_Param_input_w_id t2))  true
                                (= (Warehouse_Proj_w_id r) (Payment_Param_input_w_id t1))  true)))
                            (exists ((r District))
                                (and 
                                (IsAlive_District r t1)
                                (WR_District r t1 t2)
                                (not (Payment_isN_v2 t2))
                                (and (= (District_Proj_d_wid r) (Payment_Param_input_w_id t2)) (= (District_Proj_d_id r) (Payment_Param_input_d_id t2)))  true
                                (and (= (District_Proj_d_wid r) (Payment_Param_input_w_id t1)) (= (District_Proj_d_id r) (Payment_Param_input_d_id t1)))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Payment_isN_v3 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Payment_SVar_v6 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Payment_isN_v4 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Payment_SVar_v6 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Payment_isN_v5 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Payment_SVar_v6 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Payment_isN_v3 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Payment_SVar_v6 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Payment_isN_v4 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Payment_SVar_v6 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (not (Payment_isN_v5 t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (WR_Customer r t1 t2)
                                (Payment_SVar_v6 t2 r)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_name r) (Payment_Param_input_c_name t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))))) )))
                                :named payment-payment-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Payment) (= (type t2) New_order))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named payment-new_order-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Delivery))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or false
                            (exists ((r Orders))
                                (and 
                                (and (and (= (Orders_Proj_o_id r) (Neworder_Proj_n_oid (Delivery_Var_v2 t2))) (= (Orders_Proj_o_wid r) (Delivery_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Delivery_Param_input_d_id t2)))  true
                                ;insert
                                (= (Orders_Proj_o_id r) (New_order_Param_input_o_id t1))
                                (= (Orders_Proj_o_cid r) (New_order_Param_input_c_id t1))
                                (= (Orders_Proj_o_did r) (New_order_Param_input_d_id t1))
                                (= (Orders_Proj_o_wid r) (New_order_Param_input_w_id t1))
                                (= (Orders_Proj_o_carrierid r) 0)
                                (= (Orders_Proj_o_entrydate r) "06/05/2018")  true
                                (IsAlive_Orders r t2)
                                (not (Delivery_isN_v3 t2))
                                (WR_Alive_Orders r t1 t2))))
                            (exists ((r Neworder))
                                (and 
                                (and (= (Neworder_Proj_n_wid r) (Delivery_Param_input_w_id t2)) (= (Neworder_Proj_n_did r) (Delivery_Param_input_d_id t2)))  true
                                ;insert
                                (= (Neworder_Proj_n_oid r) (New_order_Param_input_o_id t1))
                                (= (Neworder_Proj_n_did r) (New_order_Param_input_d_id t1))
                                (= (Neworder_Proj_n_wid r) (New_order_Param_input_w_id t1))  true
                                (IsAlive_Neworder r t2)
                                (WR_Alive_Neworder r t1 t2)))) )))
                                :named new_order-delivery-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Stock_level))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or false
                            (exists ((r District))
                                (and 
                                (IsAlive_District r t1)
                                (WR_District r t1 t2)
                                (not (Stock_level_isN_v1 t2))
                                (and (= (District_Proj_d_wid r) (Stock_level_Param_input_w_id t2)) (= (District_Proj_d_id r) (Stock_level_Param_input_d_id t2)))  true
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t1)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t1)))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (WR_Stock r t1 t2)
                                (Stock_level_SVar_v3 t2 r)
                                (and (= (Stock_Proj_s_iid r) (Orderline_Proj_ol_iid (Stock_level_Var_loop_var_1 t2))) (= (Stock_Proj_s_wid r) (Stock_level_Param_input_w_id t2)))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (WR_Stock r t1 t2)
                                (Stock_level_SVar_v3 t2 r)
                                (and (= (Stock_Proj_s_iid r) (Orderline_Proj_ol_iid (Stock_level_Var_loop_var_1 t2))) (= (Stock_Proj_s_wid r) (Stock_level_Param_input_w_id t2)))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (WR_Stock r t1 t2)
                                (Stock_level_SVar_v3 t2 r)
                                (and (= (Stock_Proj_s_iid r) (Orderline_Proj_ol_iid (Stock_level_Var_loop_var_1 t2))) (= (Stock_Proj_s_wid r) (Stock_level_Param_input_w_id t2)))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10)))))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (WR_Stock r t1 t2)
                                (Stock_level_SVar_v3 t2 r)
                                (and (= (Stock_Proj_s_iid r) (Orderline_Proj_ol_iid (Stock_level_Var_loop_var_1 t2))) (= (Stock_Proj_s_wid r) (Stock_level_Param_input_w_id t2)))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10)))))) )))
                                :named new_order-stock_level-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Order_status))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or false
                            (exists ((r Orders))
                                (and 
                                (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v1 t2))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t2)))  (and true (Order_status_Param_input_cid_is_given t2))
                                ;insert
                                (= (Orders_Proj_o_id r) (New_order_Param_input_o_id t1))
                                (= (Orders_Proj_o_cid r) (New_order_Param_input_c_id t1))
                                (= (Orders_Proj_o_did r) (New_order_Param_input_d_id t1))
                                (= (Orders_Proj_o_wid r) (New_order_Param_input_w_id t1))
                                (= (Orders_Proj_o_carrierid r) 0)
                                (= (Orders_Proj_o_entrydate r) "06/05/2018")  true
                                (IsAlive_Orders r t2)
                                (WR_Alive_Orders r t1 t2))))
                            (exists ((r Orders))
                                (and 
                                (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v3 t2))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t2)))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                ;insert
                                (= (Orders_Proj_o_id r) (New_order_Param_input_o_id t1))
                                (= (Orders_Proj_o_cid r) (New_order_Param_input_c_id t1))
                                (= (Orders_Proj_o_did r) (New_order_Param_input_d_id t1))
                                (= (Orders_Proj_o_wid r) (New_order_Param_input_w_id t1))
                                (= (Orders_Proj_o_carrierid r) 0)
                                (= (Orders_Proj_o_entrydate r) "06/05/2018")  true
                                (IsAlive_Orders r t2)
                                (WR_Alive_Orders r t1 t2)))) )))
                                :named new_order-order_status-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Payment))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named new_order-payment-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) New_order))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or false
                            (exists ((r District))
                                (and 
                                (IsAlive_District r t1)
                                (WR_District r t1 t2)
                                (not (New_order_isN_v3 t2))
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t2)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t2)))  true
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t1)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t1)))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (WR_Stock r t1 t2)
                                (not (New_order_isN_v9 t2))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (WR_Stock r t1 t2)
                                (not (New_order_isN_v8 t2))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (WR_Stock r t1 t2)
                                (not (New_order_isN_v10 t2))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10)))))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (WR_Stock r t1 t2)
                                (not (New_order_isN_v10 t2))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10)))))) )))
                                :named new_order-new_order-wr-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Delivery) (= (type t2) Delivery))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        (or (or (or (or false
                            (exists ((r Orders))
                                (and 
                                (WW_Orders r t1 t2)
                                (IsAlive_Orders r t1)
                                (IsAlive_Orders r t2)
                                (and (and (= (Orders_Proj_o_id r) (Neworder_Proj_n_oid (Delivery_Var_v2 t1))) (= (Orders_Proj_o_wid r) (Delivery_Param_input_w_id t1))) (= (Orders_Proj_o_did r) (Delivery_Param_input_d_id t1)))  true
                                (and (and (= (Orders_Proj_o_id r) (Neworder_Proj_n_oid (Delivery_Var_v2 t2))) (= (Orders_Proj_o_wid r) (Delivery_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Delivery_Param_input_d_id t2)))  true)))
                            (exists ((r Orderline))
                                (and 
                                (WW_Orderline r t1 t2)
                                (IsAlive_Orderline r t1)
                                (IsAlive_Orderline r t2)
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t1))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t1))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t1)))  true
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t2))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t2))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t2)))  true)))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true)))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true))) )))
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
                        (or (or false
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))))) )))
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
                        (or (or false
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true)))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true))) )))
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
                        (or (or (or (or (or (or (or (or (or (or (or (or (or (or false
                            (exists ((r Warehouse))
                                (and 
                                (WW_Warehouse r t1 t2)
                                (IsAlive_Warehouse r t1)
                                (IsAlive_Warehouse r t2)
                                (= (Warehouse_Proj_w_id r) (Payment_Param_input_w_id t1))  true
                                (= (Warehouse_Proj_w_id r) (Payment_Param_input_w_id t2))  true)))
                            (exists ((r District))
                                (and 
                                (WW_District r t1 t2)
                                (IsAlive_District r t1)
                                (IsAlive_District r t2)
                                (and (= (District_Proj_d_wid r) (Payment_Param_input_w_id t1)) (= (District_Proj_d_id r) (Payment_Param_input_d_id t1)))  true
                                (and (= (District_Proj_d_wid r) (Payment_Param_input_w_id t2)) (= (District_Proj_d_id r) (Payment_Param_input_d_id t2)))  true)))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (WW_Customer r t1 t2)
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2)))))) )))
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
                        (or (or (or (or (or (or (or false
                            (exists ((r District))
                                (and 
                                (WW_District r t1 t2)
                                (IsAlive_District r t1)
                                (IsAlive_District r t2)
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t1)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t1)))  true
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t2)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t2)))  true)))
                            (exists ((r Stock))
                                (and 
                                (WW_Stock r t1 t2)
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true)))
                            (exists ((r Stock))
                                (and 
                                (WW_Stock r t1 t2)
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true)))
                            (exists ((r Stock))
                                (and 
                                (WW_Stock r t1 t2)
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10)))))
                            (exists ((r Stock))
                                (and 
                                (WW_Stock r t1 t2)
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10))))))
                            (exists ((r Stock))
                                (and 
                                (WW_Stock r t1 t2)
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10)))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10)))))
                            (exists ((r Stock))
                                (and 
                                (WW_Stock r t1 t2)
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10)))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10)))))) )))
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
                    (=> (or (or false
                            (exists ((r Orders))
                                (and 
                                (and (and (= (Orders_Proj_o_id r) (Neworder_Proj_n_oid (Delivery_Var_v2 t2))) (= (Orders_Proj_o_wid r) (Delivery_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Delivery_Param_input_d_id t2)))  true
                                ;insert
                                (= (Orders_Proj_o_id r) (New_order_Param_input_o_id t1))
                                (= (Orders_Proj_o_cid r) (New_order_Param_input_c_id t1))
                                (= (Orders_Proj_o_did r) (New_order_Param_input_d_id t1))
                                (= (Orders_Proj_o_wid r) (New_order_Param_input_w_id t1))
                                (= (Orders_Proj_o_carrierid r) 0)
                                (= (Orders_Proj_o_entrydate r) "06/05/2018")  true
                                (not (Delivery_isN_v3 t2))
                                (IsAlive_Orders r t2)
                                (WR_Alive_Orders r t1 t2))))
                            (exists ((r Neworder))
                                (and 
                                (and (= (Neworder_Proj_n_wid r) (Delivery_Param_input_w_id t2)) (= (Neworder_Proj_n_did r) (Delivery_Param_input_d_id t2)))  true
                                ;insert
                                (= (Neworder_Proj_n_oid r) (New_order_Param_input_o_id t1))
                                (= (Neworder_Proj_n_did r) (New_order_Param_input_d_id t1))
                                (= (Neworder_Proj_n_wid r) (New_order_Param_input_w_id t1))  true
                                (IsAlive_Neworder r t2)
                                (WR_Alive_Neworder r t1 t2))))
                        (WR t1 t2) )))
                                :named new_order-delivery-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Stock_level) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named new_order-stock_level-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) New_order) (= (type t2) Order_status) (not (= t1 t2)))
                    (=> (or (or false
                            (exists ((r Orders))
                                (and 
                                (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v1 t2))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t2)))  (and true (Order_status_Param_input_cid_is_given t2))
                                ;insert
                                (= (Orders_Proj_o_id r) (New_order_Param_input_o_id t1))
                                (= (Orders_Proj_o_cid r) (New_order_Param_input_c_id t1))
                                (= (Orders_Proj_o_did r) (New_order_Param_input_d_id t1))
                                (= (Orders_Proj_o_wid r) (New_order_Param_input_w_id t1))
                                (= (Orders_Proj_o_carrierid r) 0)
                                (= (Orders_Proj_o_entrydate r) "06/05/2018")  true
                                (IsAlive_Orders r t2)
                                (WR_Alive_Orders r t1 t2))))
                            (exists ((r Orders))
                                (and 
                                (and (and (= (Orders_Proj_o_cid r) (Customer_Proj_c_id (Order_status_Var_v3 t2))) (= (Orders_Proj_o_wid r) (Order_status_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Order_status_Param_input_d_id t2)))  (and true (not (Order_status_Param_input_cid_is_given t2)))
                                ;insert
                                (= (Orders_Proj_o_id r) (New_order_Param_input_o_id t1))
                                (= (Orders_Proj_o_cid r) (New_order_Param_input_c_id t1))
                                (= (Orders_Proj_o_did r) (New_order_Param_input_d_id t1))
                                (= (Orders_Proj_o_wid r) (New_order_Param_input_w_id t1))
                                (= (Orders_Proj_o_carrierid r) 0)
                                (= (Orders_Proj_o_entrydate r) "06/05/2018")  true
                                (IsAlive_Orders r t2)
                                (WR_Alive_Orders r t1 t2))))
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
                    (=> (or (or (or (or false
                            (exists ((r Orders))
                                (and 
                                (IsAlive_Orders r t1)
                                (IsAlive_Orders r t2)
                                (and (and (= (Orders_Proj_o_id r) (Neworder_Proj_n_oid (Delivery_Var_v2 t1))) (= (Orders_Proj_o_wid r) (Delivery_Param_input_w_id t1))) (= (Orders_Proj_o_did r) (Delivery_Param_input_d_id t1)))  true
                                (and (and (= (Orders_Proj_o_id r) (Neworder_Proj_n_oid (Delivery_Var_v2 t2))) (= (Orders_Proj_o_wid r) (Delivery_Param_input_w_id t2))) (= (Orders_Proj_o_did r) (Delivery_Param_input_d_id t2)))  true)))
                            (exists ((r Orderline))
                                (and 
                                (IsAlive_Orderline r t1)
                                (IsAlive_Orderline r t2)
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t1))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t1))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t1)))  true
                                (and (and (= (Orderline_Proj_ol_oid r) (Orders_Proj_o_id (Delivery_Var_v3 t2))) (= (Orderline_Proj_ol_wid r) (Delivery_Param_input_w_id t2))) (= (Orderline_Proj_ol_did r) (Delivery_Param_input_d_id t2)))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true)))
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
                    (=> (or (or false
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t1))))  true
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
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
                    (=> (or (or false
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Delivery_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Delivery_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Orders_Proj_o_cid (Delivery_Var_v3 t2))))  true)))
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
                    (=> (or (or (or (or (or (or (or (or (or (or (or (or (or (or false
                            (exists ((r Warehouse))
                                (and 
                                (IsAlive_Warehouse r t1)
                                (IsAlive_Warehouse r t2)
                                (= (Warehouse_Proj_w_id r) (Payment_Param_input_w_id t1))  true
                                (= (Warehouse_Proj_w_id r) (Payment_Param_input_w_id t2))  true)))
                            (exists ((r District))
                                (and 
                                (IsAlive_District r t1)
                                (IsAlive_District r t2)
                                (and (= (District_Proj_d_wid r) (Payment_Param_input_w_id t1)) (= (District_Proj_d_id r) (Payment_Param_input_d_id t1)))  true
                                (and (= (District_Proj_d_wid r) (Payment_Param_input_w_id t2)) (= (District_Proj_d_id r) (Payment_Param_input_d_id t2)))  true)))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (Payment_Param_input_cid_is_given t1))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (Payment_Param_input_cid_is_given t2)))))
                            (exists ((r Customer))
                                (and 
                                (IsAlive_Customer r t1)
                                (IsAlive_Customer r t2)
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t1)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t1))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t1)))  (and true (not (Payment_Param_input_cid_is_given t1)))
                                (and (and (= (Customer_Proj_c_wid r) (Payment_Param_input_w_id t2)) (= (Customer_Proj_c_did r) (Payment_Param_input_d_id t2))) (= (Customer_Proj_c_id r) (Payment_Param_input_c_id t2)))  (and true (not (Payment_Param_input_cid_is_given t2))))))
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
                    (=> (or (or (or (or (or (or (or false
                            (exists ((r District))
                                (and 
                                (IsAlive_District r t1)
                                (IsAlive_District r t2)
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t1)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t1)))  true
                                (and (= (District_Proj_d_wid r) (New_order_Param_input_w_id t2)) (= (District_Proj_d_id r) (New_order_Param_input_d_id t2)))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  true
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  true)))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10)))))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10))))))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10)))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10)))))
                            (exists ((r Stock))
                                (and 
                                (IsAlive_Stock r t1)
                                (IsAlive_Stock r t2)
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t1)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t1))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t1)) (New_order_Param_input_ol_qnt t1)) 10)))
                                (and (= (Stock_Proj_s_wid r) (New_order_Param_input_w_id t2)) (= (Stock_Proj_s_iid r) (Item_Proj_i_id (New_order_Var_loop_var_1 t2))))  (and true (not (> (- (Stock_Proj_s_quant (New_order_Var_v10 t2)) (New_order_Param_input_ol_qnt t2)) 10))))))
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named new_order-new_order-then-ww))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                      Finalization                                                      
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(declare-fun D (T T) Bool)
(assert (! (forall ((t1 T)(t2 T)) (=> (D t1 t2) (or (WW t1 t2)(WR t1 t2)(RW t1 t2)))) :named gen-dep) )
(assert (! (exists ( (t1 T) (t2 T) (t3 T) (t4 T) (t5 T) (t6 T) (t7 T) (t8 T) (t9 T) (t10 T) (t11 T) (t12 T)) (and (not (= t1 t12))  (D t1 t2) (D t2 t3) (D t3 t4) (D t4 t5) (D t5 t6) (D t6 t7) (D t7 t8) (D t8 t9) (D t9 t10) (D t10 t11) (D t11 t12) (D t12 t1))) :named cycle))

;Guarantees
;Selective SER 
(assert (! (forall ((t1 T) (t2 T)) (=> (and (or (and (= (type t1) New_order)(= (type t2)Payment))
                                                (and (= (type t1) Payment)(= (type t2)New_order))) 
                                            (ar t1 t2))  (vis t1 t2))):named New_order-Payment-selective-ser ))
;Selective SER 
(assert (! (forall ((t1 T) (t2 T)) (=> (and (or (and (= (type t1) New_order)(= (type t2)New_order))
                                                (and (= (type t1) New_order)(= (type t2)New_order))) 
                                            (ar t1 t2))  (vis t1 t2))):named New_order-New_order-selective-ser ))
;Selective SER 
(assert (! (forall ((t1 T) (t2 T)) (=> (and (or (and (= (type t1) New_order)(= (type t2)Delivery))
                                                (and (= (type t1) Delivery)(= (type t2)New_order))) 
                                            (ar t1 t2))  (vis t1 t2))):named New_order-Delivery-selective-ser ))
;Selective SER 
(assert (! (forall ((t1 T) (t2 T)) (=> (and (or (and (= (type t1) Delivery)(= (type t2)Payment))
                                                (and (= (type t1) Payment)(= (type t2)Delivery))) 
                                            (ar t1 t2))  (vis t1 t2))):named Delivery-Payment-selective-ser ))
;Selective SER 
(assert (! (forall ((t1 T) (t2 T)) (=> (and (or (and (= (type t1) Delivery)(= (type t2)Delivery))
                                                (and (= (type t1) Delivery)(= (type t2)Delivery))) 
                                            (ar t1 t2))  (vis t1 t2))):named Delivery-Delivery-selective-ser ))
;Selective SER 
(assert (! (forall ((t1 T) (t2 T)) (=> (and (or (and (= (type t1) Payment)(= (type t2)Payment))
                                                (and (= (type t1) Payment)(= (type t2)Payment))) 
                                            (ar t1 t2))  (vis t1 t2))):named Payment-Payment-selective-ser ))
;CC 
(assert (! (forall ((t1 T) (t2 T) (t3 T))  (=> (and (vis  t1 t2) (vis  t2 t3)) (vis  t1 t3))):named cc))

(check-sat)
;(get-unsat-core)
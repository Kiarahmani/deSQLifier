
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       Constants                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(set-option :produce-unsat-cores true)

(declare-datatypes () ((TType (Txn3) (Txn4) (Txn5) (Txn2) (Txn1)))) 
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


(declare-sort Bankaccount)
(declare-fun Bankaccount_Proj_b_id (Bankaccount) Int)
(declare-fun Bankaccount_Proj_b_bal (Bankaccount) Int)
(assert (forall ((r1 Bankaccount)(r2 Bankaccount)) (=>
  (and (= (Bankaccount_Proj_b_id r1) (Bankaccount_Proj_b_id r2)))(= r1 r2))))
(declare-fun RW_Bankaccount (Bankaccount T T) Bool)
(declare-fun RW_Alive_Bankaccount (Bankaccount T T) Bool)
(declare-fun WR_Bankaccount (Bankaccount T T) Bool)
(declare-fun WR_Alive_Bankaccount (Bankaccount T T) Bool)
(declare-fun WW_Bankaccount (Bankaccount T T) Bool)
(declare-fun WW_Alive_Bankaccount (Bankaccount T T) Bool)
(declare-fun IsAlive_Bankaccount (Bankaccount T) Bool)
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (RW_Bankaccount r t1 t2) (RW t1 t2))))
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (RW_Alive_Bankaccount r t1 t2) (RW t1 t2))))
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WR_Bankaccount r t1 t2) (WR t1 t2))))
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WR_Alive_Bankaccount r t1 t2) (WR t1 t2))))
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WW_Bankaccount r t1 t2) (WW t1 t2))))
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WW_Alive_Bankaccount r t1 t2) (WW t1 t2))))
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Bankaccount r t2 t1)(RW_Bankaccount r t1 t3))(WW_Bankaccount r t2 t3))))
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Bankaccount r t2 t1)(RW_Alive_Bankaccount r t1 t3))(WW_Alive_Bankaccount r t2 t3))))

(declare-sort Employee)
(declare-fun Employee_Proj_e_id (Employee) Int)
(declare-fun Employee_Proj_e_name (Employee) String)
(declare-fun Employee_Proj_e_sal (Employee) Int)
(assert (forall ((r1 Employee)(r2 Employee)) (=>
  (and (= (Employee_Proj_e_id r1) (Employee_Proj_e_id r2)))(= r1 r2))))
(declare-fun RW_Employee (Employee T T) Bool)
(declare-fun RW_Alive_Employee (Employee T T) Bool)
(declare-fun WR_Employee (Employee T T) Bool)
(declare-fun WR_Alive_Employee (Employee T T) Bool)
(declare-fun WW_Employee (Employee T T) Bool)
(declare-fun WW_Alive_Employee (Employee T T) Bool)
(declare-fun IsAlive_Employee (Employee T) Bool)
(assert  (forall ((r Employee)(t1 T)(t2 T)) (=> (RW_Employee r t1 t2) (RW t1 t2))))
(assert  (forall ((r Employee)(t1 T)(t2 T)) (=> (RW_Alive_Employee r t1 t2) (RW t1 t2))))
(assert  (forall ((r Employee)(t1 T)(t2 T)) (=> (WR_Employee r t1 t2) (WR t1 t2))))
(assert  (forall ((r Employee)(t1 T)(t2 T)) (=> (WR_Alive_Employee r t1 t2) (WR t1 t2))))
(assert  (forall ((r Employee)(t1 T)(t2 T)) (=> (WW_Employee r t1 t2) (WW t1 t2))))
(assert  (forall ((r Employee)(t1 T)(t2 T)) (=> (WW_Alive_Employee r t1 t2) (WW t1 t2))))
(assert  (forall ((r Employee)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Employee r t2 t1)(RW_Employee r t1 t3))(WW_Employee r t2 t3))))
(assert  (forall ((r Employee)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Employee r t2 t1)(RW_Alive_Employee r t1 t3))(WW_Alive_Employee r t2 t3))))


(declare-fun Txn3_Param_in_id (T) Int)
(declare-fun Txn3_Param_amount (T) Int)
(declare-fun Txn4_Param_in_id (T) Int)
(declare-fun Txn4_Param_amount (T) Int)
(declare-fun Txn5_Param_in_id (T) Int)
(declare-fun Txn5_Param_amount (T) Int)
(declare-fun Txn2_Param_in_id (T) Int)
(declare-fun Txn2_Param_amount (T) Int)
(declare-fun Txn1_Param_src_id (T) Int)
(declare-fun Txn1_Param_dst_id (T) Int)
(declare-fun Txn1_Param_amount (T) Int)


(declare-fun Txn3_isN_read_v (T) Bool)
(declare-fun Txn3_Var_read_v (T) Int)
(declare-fun Txn3_isN_w_read_all (T) Bool)
(declare-fun Txn3_Var_w_read_all (T) Int)
(declare-fun Txn4_isN_read_v (T) Bool)
(declare-fun Txn4_Var_read_v (T) Int)
(declare-fun Txn5_isN_read_v (T) Bool)
(declare-fun Txn5_Var_read_v (T) Int)
(declare-fun Txn2_isN_read_v (T) Bool)
(declare-fun Txn2_Var_read_v (T) Int)
(declare-fun Txn2_isN_w_read_all (T) Bool)
(declare-fun Txn2_Var_w_read_all (T) Int)
(declare-fun Txn1_isN_acc_src (T) Bool)
(declare-fun Txn1_Var_acc_src (T) Int)
(declare-fun Txn1_isN_acc_dst (T) Bool)
(declare-fun Txn1_Var_acc_dst (T) Int)


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       RW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn3))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn3_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (< (- (Employee_Proj_e_sal r) (Txn3_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true
                             (> (Txn3_Var_w_read_all t2) (- (Txn3_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn4))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn5))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn2))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn2_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (< (- (Employee_Proj_e_sal r) (Txn3_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true
                             (> (Txn2_Var_w_read_all t2) (- (Txn3_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn1))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn1_isN_acc_dst t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (> (- (Employee_Proj_e_sal r) (Txn3_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true
                             (> (Txn1_Var_acc_dst t2) (- (Txn3_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn3))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2)))))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn4))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn5))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn2))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2)))))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn1))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t1))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn3))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2)))))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn4))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn5))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn2))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2)))))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn1))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t1))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn3))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn3_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (< (- (Employee_Proj_e_sal r) (Txn2_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true
                             (> (Txn3_Var_w_read_all t2) (- (Txn2_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn4))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn5))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn2))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn2_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (< (- (Employee_Proj_e_sal r) (Txn2_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true
                             (> (Txn2_Var_w_read_all t2) (- (Txn2_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn1))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (RW_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn1_isN_acc_dst t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (> (- (Employee_Proj_e_sal r) (Txn2_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true
                             (> (Txn1_Var_acc_dst t2) (- (Txn2_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (RW_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn3))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn3_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (< (Txn1_Param_amount t1) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true
                             (> (Txn3_Var_w_read_all t2) (Txn1_Param_amount t1)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn3_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (< 400 (Employee_Proj_e_sal r) )))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn4))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true ))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn5))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true ))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn2))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn2_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (< (Txn1_Param_amount t1) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (RW_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true
                             (> (Txn2_Var_w_read_all t2) (Txn1_Param_amount t1)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn2_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (< 400 (Employee_Proj_e_sal r) )))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn1))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn1_isN_acc_dst t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (> (Txn1_Param_amount t1) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (RW_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true
                             (> (Txn1_Var_acc_dst t2) (Txn1_Param_amount t1)))))
                        (exists ((r Bankaccount))
                        (and (IsAlive_Bankaccount r t2)
                             (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Txn1_Param_src_id t1))
                             true
                             (= (Bankaccount_Proj_b_id r) (Txn1_Param_src_id t2))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (RW_Employee r t1 t2)
                             (not (Txn1_isN_acc_dst t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (> 400 (Employee_Proj_e_sal r) )))) ))))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WR-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn3))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn3_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (= (- (Employee_Proj_e_sal r) (Txn3_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true
                             (>= (Txn3_Var_w_read_all t2) (- (Txn3_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn4))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn5))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn2))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn2_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (= (- (Employee_Proj_e_sal r) (Txn3_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true
                             (>= (Txn2_Var_w_read_all t2) (- (Txn3_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn1))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn1_isN_acc_dst t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (= (- (Employee_Proj_e_sal r) (Txn3_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (not (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 300))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 400))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 500))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true
                             (<= (Txn1_Var_acc_dst t2) (- (Txn3_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn3))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn4))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn5))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn2))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn1))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn3))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn4))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn5))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn2))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn1))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn3))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn3_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (= (- (Employee_Proj_e_sal r) (Txn2_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true
                             (>= (Txn3_Var_w_read_all t2) (- (Txn2_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn4))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn5))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn2))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn2_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (= (- (Employee_Proj_e_sal r) (Txn2_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true
                             (>= (Txn2_Var_w_read_all t2) (- (Txn2_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn1))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn1_isN_acc_dst t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (= (- (Employee_Proj_e_sal r) (Txn2_Param_amount t1)) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (not (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1))))
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 200))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true
                             (<= (Txn1_Var_acc_dst t2) (- (Txn2_Param_amount t1) 100)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (< (Employee_Proj_e_sal r) (+ (Employee_Proj_e_sal r) 400))
                             true
                             (WR_Alive_Employee r t1 t2)))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn3))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn3_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (= (Txn1_Param_amount t1) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn3_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true
                             (>= (Txn3_Var_w_read_all t2) (Txn1_Param_amount t1)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn3_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (= 400 (Employee_Proj_e_sal r) )))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn4))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn4_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn5))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn5_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn2))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn2_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (= (Txn1_Param_amount t1) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (Txn2_isN_read_v t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true
                             (>= (Txn2_Var_w_read_all t2) (Txn1_Param_amount t1)))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn2_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (= 400 (Employee_Proj_e_sal r) )))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn1))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn1_isN_acc_dst t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (= (Txn1_Param_amount t1) (Employee_Proj_e_sal r) ))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (not (IsAlive_Employee r t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             true
                             (WR_Alive_Employee r t1 t2))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true
                             (<= (Txn1_Var_acc_dst t2) (Txn1_Param_amount t1)))))
                        (exists ((r Bankaccount))
                        (and (IsAlive_Bankaccount r t1)
                             (WR_Bankaccount r t1 t2)
                             (not (Txn1_isN_acc_src t2))
                             (= (Bankaccount_Proj_b_id r) (Txn1_Param_src_id t2))
                             true
                             (= (Bankaccount_Proj_b_id r) (Txn1_Param_src_id t1))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (WR_Employee r t1 t2)
                             (not (Txn1_isN_acc_dst t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (= 400 (Employee_Proj_e_sal r) )))) ))))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2))))))))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2))))))))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true)))))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2))))))))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2))))))))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true)))))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2))))))))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        false))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2))))))))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> (and (WW t1 t2) (not (= t2 t1)))
                        (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true)))
                        (exists ((r Bankaccount))
                        (and (IsAlive_Bankaccount r t1)
                             (IsAlive_Bankaccount r t2)
                             (= (Bankaccount_Proj_b_id r) (Txn1_Param_src_id t1))
                             true
                             (= (Bankaccount_Proj_b_id r) (Txn1_Param_src_id t2))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true)))))))




;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WR Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn3_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn2_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn1_isN_acc_dst t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn3_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn3_Param_amount t1) 100))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn3_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn2_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn1_isN_acc_dst t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (+ (Txn2_Param_in_id t1) 1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (- (Txn2_Param_amount t1) 100))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn3_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn3_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn4_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn4_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn5_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn5_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn2_isN_read_v t2))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn2_isN_w_read_all t2))
                             (= (Employee_Proj_e_name r) "Roger")
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (WR t1 t2) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t2)
                             (not (Txn1_isN_acc_dst t2))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true
                             (WR_Alive_Employee r t1 t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1))
                             (= (Employee_Proj_e_name r) "David")
                             (= (Employee_Proj_e_sal r) (Txn1_Param_amount t1))
                             true )))
                        (WR t1 t2) ))))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WW Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2))))))
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2))))))
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn3) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t1))
                             (and true (> (Txn3_Var_read_v t1) (Txn3_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true)))
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn4) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn5) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2))))))
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2))))))
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn2) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t1))
                             (and true (> (Txn2_Var_read_v t1) (Txn2_Param_amount t1)))
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true)))
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn3) (not (= t1 t2)))
                    (=> (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn3_Param_in_id t2))
                             (and true (> (Txn3_Var_read_v t2) (Txn3_Param_amount t2))))))
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn4) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn5) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn2) (not (= t1 t2)))
                    (=> (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2))))))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn2_Param_in_id t2))
                             (and true (> (Txn2_Var_read_v t2) (Txn2_Param_amount t2))))))
                        (or (WW t1 t2) (WW t2 t1)) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Txn1) (= (type t2) Txn1) (not (= t1 t2)))
                    (=> (or (or (or (or (or false
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t1)))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true)))
                        (exists ((r Bankaccount))
                        (and (IsAlive_Bankaccount r t1)
                             (IsAlive_Bankaccount r t2)
                             (= (Bankaccount_Proj_b_id r) (Txn1_Param_src_id t1))
                             true
                             (= (Bankaccount_Proj_b_id r) (Txn1_Param_src_id t2))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (not (= (Employee_Proj_e_id r) (Txn1_Param_src_id t2)))
                             true)))
                        (exists ((r Employee))
                        (and (IsAlive_Employee r t1)
                             (IsAlive_Employee r t2)
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t1))
                             true
                             (= (Employee_Proj_e_id r) (Txn1_Param_dst_id t2))
                             true)))
                        (or (WW t1 t2) (WW t2 t1)) ))))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                      Finalization                                                      
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(declare-fun D (T T) Bool)
(assert (forall ((t1 T)(t2 T)) (=> (D t1 t2) (or (WW t1 t2)(WR t1 t2)(RW t1 t2)))))
(assert (exists ( (t1 T) (t2 T) (t3 T)) (and (not (= t1 t3))  (D t1 t2) (D t2 t3) (D t3 t1))))

(assert (! (forall ((t1 T) (t2 T) (t3 T))  (=> (and (vis  t1 t2) (vis  t2 t3)) (vis  t1 t3))):named cc)) ;CC

(check-sat)
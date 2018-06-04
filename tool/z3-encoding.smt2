
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       Constants                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(set-option :produce-unsat-cores true)

(declare-datatypes () ((TType (Deposit)))) 
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


(declare-fun Deposit_Param_input (T) Int)


(declare-fun Deposit_isN_v1 (T) Bool)
(declare-fun Deposit_Var_v1 (T) Employee)
(assert (forall ((t0 T)) (= (Employee_Proj_e_id (Deposit_Var_v1 t0)) 100)))
(declare-fun Deposit_SVar_v2 (T Employee) Bool)
(assert (forall ((t0 T)(r Employee)) (=> (Deposit_SVar_v2 t0 r) (> (Employee_Proj_e_sal r) (Employee_Proj_e_id (Deposit_Var_v1 t0)))) ))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       RW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or false
                            (exists ((r Employee))
                                (and 
                                (IsAlive_Employee r t2)
                                (RW_Employee r t1 t2)
                                (= (Employee_Proj_e_id r) 100)  true
                                (= (Employee_Proj_e_id r) (+ (Deposit_Param_input t2) 1))  true))) ))))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WR-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or false
                            (exists ((r Employee))
                                (and 
                                (IsAlive_Employee r t2)
                                (WR_Employee r t1 t2)
                                (not (Deposit_isN_v1 t2))
                                (= (Employee_Proj_e_id r) 100)  true
                                (= (Employee_Proj_e_id r) (+ (Deposit_Param_input t1) 1))  true))) ))))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        (or false
                            (exists ((r Employee))
                                (and 
                                (IsAlive_Employee r t1)
                                (IsAlive_Employee r t2)
                                (= (Employee_Proj_e_id r) (+ (Deposit_Param_input t1) 1))  true
                                (= (Employee_Proj_e_id r) (+ (Deposit_Param_input t2) 1))  true))) ))))




;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WR Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) ))))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WW Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit) (not (= t1 t2)))
                    (=> (or false
                            (exists ((r Employee))
                                (and 
                                (IsAlive_Employee r t1)
                                (IsAlive_Employee r t2)
                                (= (Employee_Proj_e_id r) (+ (Deposit_Param_input t1) 1))  true
                                (= (Employee_Proj_e_id r) (+ (Deposit_Param_input t2) 1))  true)))
                        (or (WW t1 t2) (WW t2 t1)) ))))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                      Finalization                                                      
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(declare-fun D (T T) Bool)
(assert (forall ((t1 T)(t2 T)) (=> (D t1 t2) (or (WW t1 t2)(WR t1 t2)(RW t1 t2)))))
(assert (exists ( (t1 T) (t2 T) (t3 T)) (and (not (= t1 t3))  (D t1 t2) (D t2 t3) (D t3 t1))))

(assert (! (forall ((t1 T) (t2 T) (t3 T))  (=> (and (vis  t1 t2) (vis  t2 t3)) (vis  t1 t3))):named cc)) ;CC

(check-sat)
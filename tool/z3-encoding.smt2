
;------------------------------------------------------------------------------------------------------------------------
;                                                       Constants                                                       
;------------------------------------------------------------------------------------------------------------------------


(set-option :produce-unsat-cores true)

(declare-datatypes () ((TType (Withdraw) (Deposit)))) 
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


;------------------------------------------------------------------------------------------------------------------------
;                                                   Table Declarations                                                   
;------------------------------------------------------------------------------------------------------------------------


(declare-sort Bankaccount)
(declare-fun Bankaccount_Proj_b_id (Bankaccount) Int)
(declare-fun Bankaccount_Proj_b_bal (Bankaccount) Int)
(assert (forall ((r1 Bankaccount)(r2 Bankaccount)) (=>
  (and (= (Bankaccount_Proj_b_id r1) (Bankaccount_Proj_b_id r2)))(= r1 r2))))
(declare-fun RW_Bankaccount (Bankaccount T T) Bool)
(declare-fun WR_Bankaccount (Bankaccount T T) Bool)
(declare-fun WW_Bankaccount (Bankaccount T T) Bool)
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (RW_Bankaccount r t1 t2) (RW t1 t2))))
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WR_Bankaccount r t1 t2) (WR t1 t2))))
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WW_Bankaccount r t1 t2) (WW t1 t2))))
(assert  (forall ((r Bankaccount)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Bankaccount r t2 t1)(RW_Bankaccount r t1 t3))(WW_Bankaccount r t2 t3))))

(declare-sort Student)
(declare-fun Student_Proj_b_id (Student) Int)
(declare-fun Student_Proj_b_bal (Student) Int)
(assert (forall ((r1 Student)(r2 Student)) (=>
  (and (= (Student_Proj_b_id r1) (Student_Proj_b_id r2)))(= r1 r2))))
(declare-fun RW_Student (Student T T) Bool)
(declare-fun WR_Student (Student T T) Bool)
(declare-fun WW_Student (Student T T) Bool)
(assert  (forall ((r Student)(t1 T)(t2 T)) (=> (RW_Student r t1 t2) (RW t1 t2))))
(assert  (forall ((r Student)(t1 T)(t2 T)) (=> (WR_Student r t1 t2) (WR t1 t2))))
(assert  (forall ((r Student)(t1 T)(t2 T)) (=> (WW_Student r t1 t2) (WW t1 t2))))
(assert  (forall ((r Student)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Student r t2 t1)(RW_Student r t1 t3))(WW_Student r t2 t3))))


(declare-fun Withdraw_Param_src_id (T) Int)
(declare-fun Withdraw_Param_amount (T) Int)
(declare-fun Deposit_Param_src_id (T) Int)
(declare-fun Deposit_Param_dst_id (T) Int)
(declare-fun Deposit_Param_amount (T) Int)


(declare-fun Withdraw_isN_acc_src (T) Bool)
(declare-fun Withdraw_Var_acc_src (T) Int)
(declare-fun Deposit_isN_acc_src (T) Bool)
(declare-fun Deposit_Var_acc_src (T) Int)
(declare-fun Deposit_isN_acc_dst (T) Bool)
(declare-fun Deposit_Var_acc_dst (T) Int)


;------------------------------------------------------------------------------------------------------------------------
;                                                        RW Rules                                                        
;------------------------------------------------------------------------------------------------------------------------


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Withdraw) (= (type t2) Withdraw))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or false
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t2))))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Withdraw) (= (type t2) Deposit))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t2)))))
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t2))))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Withdraw))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t2)))))
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t1))
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t2))))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or false
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t2)))))
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t2)))))
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t2)))))
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t2))))) ))))
;------------------------------------------------------------------------------------------------------------------------
;                                                        WR Rules                                                        
;------------------------------------------------------------------------------------------------------------------------


(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Withdraw) (= (type t2) Withdraw))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or false
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t2))))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Withdraw) (= (type t2) Deposit))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t2)))))
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t2))))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Withdraw))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t2)))))
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t1))
                             (= (Bankaccount_Proj_b_id r) (Withdraw_Param_src_id t2))))) ))))

(assert (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or (or (or false
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t2)))))
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t2)))))
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_src_id t2)))))
                        (exists ((r Bankaccount))
                        (and (RW_Bankaccount r t1 t2)
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t1))
                             (= (Bankaccount_Proj_b_id r) (Deposit_Param_dst_id t2))))) ))))
;------------------------------------------------------------------------------------------------------------------------
;                                                        WW Rules                                                        
;------------------------------------------------------------------------------------------------------------------------



;------------------------------------------------------------------------------------------------------------------------
;                                                      Finalization                                                      
;------------------------------------------------------------------------------------------------------------------------


(assert (exists ((t1 T) (t2 T)) (and (not (= t1 t2)) (RW t1 t2) (RW t2 t1))))



(check-sat)
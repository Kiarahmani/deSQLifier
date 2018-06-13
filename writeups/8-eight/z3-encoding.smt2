
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       Constants                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(set-option :produce-unsat-cores true)

(declare-datatypes () ((TType (Withdraw)))) 
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


(declare-sort Account)
(declare-fun Account_Proj_a_id (Account) Int)
(declare-fun Account_Proj_a_owner (Account) String)
(declare-fun Account_Proj_a_balance (Account) Int)
(assert (! (forall ((r1 Account)(r2 Account)) (=>
  (and (= (Account_Proj_a_id r1) (Account_Proj_a_id r2)))(= r1 r2))) :named pk-account) )
(declare-fun RW_Account (Account T T) Bool)
(declare-fun RW_Alive_Account (Account T T) Bool)
(declare-fun WR_Account (Account T T) Bool)
(declare-fun WR_Alive_Account (Account T T) Bool)
(declare-fun WW_Account (Account T T) Bool)
(declare-fun WW_Alive_Account (Account T T) Bool)
(declare-fun IsAlive_Account (Account T) Bool)
(assert (! (forall ((r Account)(t1 T)(t2 T)) (=> (RW_Account r t1 t2) (RW t1 t2)))       :named account-RW-then-row))
(assert (! (forall ((r Account)(t1 T)(t2 T)) (=> (RW_Alive_Account r t1 t2) (RW t1 t2))) :named account-RW-then-alive))
(assert (! (forall ((r Account)(t1 T)(t2 T)) (=> (WR_Account r t1 t2) (WR t1 t2)))       :named account-WR-then-row))
(assert (! (forall ((r Account)(t1 T)(t2 T)) (=> (WR_Alive_Account r t1 t2) (WR t1 t2))) :named account-WR-then-alive))
(assert (! (forall ((r Account)(t1 T)(t2 T)) (=> (WW_Account r t1 t2) (WW t1 t2)))       :named account-WW-then-row))
(assert (! (forall ((r Account)(t1 T)(t2 T)) (=> (WW_Alive_Account r t1 t2) (WW t1 t2))) :named account-WW-then-alive))
(assert (! (forall ((r Account)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Account r t2 t1)(RW_Account r t1 t3))(WW_Account r t2 t3))) :named account-lww-row))
(assert (! (forall ((r Account)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Account r t2 t1)(RW_Alive_Account r t1 t3))(WW_Alive_Account r t2 t3))) :named account-lww-alive))

;params
(declare-fun Withdraw_Param_input (T) Int)

;at__all_acs
(declare-fun Withdraw_SVar_at__all_acs (T Account) Bool)
(assert (! (forall ((t0 T)(r Account)) (=> (Withdraw_SVar_at__all_acs t0 r) (= 1 1))) :named withdraw-at__all_acs-var-prop))
;at__kia_acs
(declare-fun Withdraw_SVar_at__kia_acs (T Account) Bool)
(assert (! (forall ((t0 T)(r Account)) (=> (Withdraw_SVar_at__kia_acs t0 r) (= (Account_Proj_a_owner r) "Kia"))) :named withdraw-at__kia_acs-var-prop))
;withdraw_at__ac1
(declare-fun Withdraw_isN_at__ac1 (T) Bool)
(declare-fun Withdraw_Var_at__ac1 (T) Account)
(assert (! (forall((t0 T))(and (=> (not (Withdraw_isN_at__ac1 t0)) (exists ((r Account))(= (Withdraw_Var_at__ac1 t0) r))) 
                               (=> (exists ((r Account))(= (Withdraw_Var_at__ac1 t0) r)) (not (Withdraw_isN_at__ac1 t0))))) :named withdraw-at__ac1-isnull-prop) )
(assert (! (forall ((t0 T)) (= 1 1)) :named withdraw-at__ac1-var-filter-prop))
(assert (! (forall ((t0 T))(Withdraw_SVar_at__kia_acs t0 (Withdraw_Var_at__ac1 t0)))  :named withdraw-at__ac1-var-chosen-prop))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       RW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Withdraw) (= (type t2) Withdraw))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                            (exists ((r Account))
                                (and 
                                (IsAlive_Account r t2)
                                (RW_Account r t1 t2)
                                (not (Withdraw_SVar_at__all_acs t1 r))
                                (= 1 1)  true
                                (= (Account_Proj_a_id r) (Account_Proj_a_id (Withdraw_Var_at__ac1 t2)))  true)))
                            (exists ((r Account))
                                (and 
                                (IsAlive_Account r t2)
                                (RW_Account r t1 t2)
                                (not (Withdraw_SVar_at__kia_acs t1 r))
                                (= (Account_Proj_a_owner r) "Kia")  true
                                (= (Account_Proj_a_id r) (Account_Proj_a_id (Withdraw_Var_at__ac1 t2)))  true))) )))
                                :named withdraw-withdraw-rw-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WR-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Withdraw) (= (type t2) Withdraw))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or false
                            (exists ((r Account))
                                (and 
                                (IsAlive_Account r t1)
                                (WR_Account r t1 t2)
                                (Withdraw_SVar_at__all_acs t2 r)
                                (= 1 1)  true
                                (= (Account_Proj_a_id r) (Account_Proj_a_id (Withdraw_Var_at__ac1 t1)))  true)))
                            (exists ((r Account))
                                (and 
                                (IsAlive_Account r t1)
                                (WR_Account r t1 t2)
                                (Withdraw_SVar_at__kia_acs t2 r)
                                (= (Account_Proj_a_owner r) "Kia")  true
                                (= (Account_Proj_a_id r) (Account_Proj_a_id (Withdraw_Var_at__ac1 t1)))  true))) )))
                                :named withdraw-withdraw-wr-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Withdraw) (= (type t2) Withdraw))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        (or false
                            (exists ((r Account))
                                (and 
                                (WW_Account r t1 t2)
                                (IsAlive_Account r t1)
                                (IsAlive_Account r t2)
                                (= (Account_Proj_a_id r) (Account_Proj_a_id (Withdraw_Var_at__ac1 t1)))  true
                                (= (Account_Proj_a_id r) (Account_Proj_a_id (Withdraw_Var_at__ac1 t2)))  true))) )))
                                :named withdraw-withdraw-ww-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WR Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Withdraw) (= (type t2) Withdraw) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named withdraw-withdraw-then-wr))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WW Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Withdraw) (= (type t2) Withdraw) (not (= t1 t2)))
                    (=> (or false
                            (exists ((r Account))
                                (and 
                                (IsAlive_Account r t1)
                                (IsAlive_Account r t2)
                                (= (Account_Proj_a_id r) (Account_Proj_a_id (Withdraw_Var_at__ac1 t1)))  true
                                (= (Account_Proj_a_id r) (Account_Proj_a_id (Withdraw_Var_at__ac1 t2)))  true)))
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named withdraw-withdraw-then-ww))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                      Finalization                                                      
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(declare-fun D (T T) Bool)
(assert (! (forall ((t1 T)(t2 T)) (=> (D t1 t2) (or (WW t1 t2)(WR t1 t2)(RW t1 t2)))) :named gen-dep) )
(assert (! (exists ( (t1 T) (t2 T) (t3 T) (t4 T) (t5 T) (t6 T) (t7 T) (t8 T) (t9 T) (t10 T) (t11 T) (t12 T)) (and (not (= t1 t12))  (D t1 t2) (D t2 t3) (D t3 t4) (D t4 t5) (D t5 t6) (D t6 t7) (D t7 t8) (D t8 t9) (D t9 t10) (D t10 t11) (D t11 t12) (D t12 t1))) :named cycle))

;Guarantees
;CC 
(assert (! (forall ((t1 T) (t2 T) (t3 T))  (=> (and (vis  t1 t2) (vis  t2 t3)) (vis  t1 t3))):named cc))

(check-sat)
;(get-unsat-core)
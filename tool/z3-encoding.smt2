
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       Constants                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(set-option :produce-unsat-cores true)

(declare-datatypes () ((TType (Deposit) (Status)))) 
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
(declare-fun Bankaccount_Proj_b_owner (Bankaccount) String)
(declare-fun Bankaccount_Proj_b_bal (Bankaccount) Int)
(assert (! (forall ((r1 Bankaccount)(r2 Bankaccount)) (=>
  (and (= (Bankaccount_Proj_b_id r1) (Bankaccount_Proj_b_id r2)))(= r1 r2))) :named pk-bankaccount) )
(declare-fun RW_Bankaccount (Bankaccount T T) Bool)
(declare-fun RW_Alive_Bankaccount (Bankaccount T T) Bool)
(declare-fun WR_Bankaccount (Bankaccount T T) Bool)
(declare-fun WR_Alive_Bankaccount (Bankaccount T T) Bool)
(declare-fun WW_Bankaccount (Bankaccount T T) Bool)
(declare-fun WW_Alive_Bankaccount (Bankaccount T T) Bool)
(declare-fun IsAlive_Bankaccount (Bankaccount T) Bool)
(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (RW_Bankaccount r t1 t2) (RW t1 t2)))       :named bankaccount-RW-then-row))
(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (RW_Alive_Bankaccount r t1 t2) (RW t1 t2))) :named bankaccount-RW-then-alive))
(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WR_Bankaccount r t1 t2) (WR t1 t2)))       :named bankaccount-WR-then-row))
(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WR_Alive_Bankaccount r t1 t2) (WR t1 t2))) :named bankaccount-WR-then-alive))
(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WW_Bankaccount r t1 t2) (WW t1 t2)))       :named bankaccount-WW-then-row))
(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WW_Alive_Bankaccount r t1 t2) (WW t1 t2))) :named bankaccount-WW-then-alive))
(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Bankaccount r t2 t1)(RW_Bankaccount r t1 t3))(WW_Bankaccount r t2 t3))) :named bankaccount-lww-row))
(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Bankaccount r t2 t1)(RW_Alive_Bankaccount r t1 t3))(WW_Alive_Bankaccount r t2 t3))) :named bankaccount-lww-alive))

;params
(declare-fun Deposit_Param_ac_id (T) Int)
(declare-fun Status_Param_ac_id (T) Int)
(declare-fun Status_Param_ac_id2 (T) Int)

;status_v1
(declare-fun Status_isN_v1 (T) Bool)
(declare-fun Status_Var_v1 (T) Bankaccount)
(assert (! (forall((t0 T))(and (=> (not (Status_isN_v1 t0)) (exists ((r Bankaccount))(= (Status_Var_v1 t0) r))) 
                               (=> (exists ((r Bankaccount))(= (Status_Var_v1 t0) r)) (not (Status_isN_v1 t0))))) :named status-v1-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Bankaccount_Proj_b_id (Status_Var_v1 t0)) (Status_Param_ac_id t0))) :named status-v1-select-prop))
;status_v2
(declare-fun Status_isN_v2 (T) Bool)
(declare-fun Status_Var_v2 (T) Bankaccount)
(assert (! (forall((t0 T))(and (=> (not (Status_isN_v2 t0)) (exists ((r Bankaccount))(= (Status_Var_v2 t0) r))) 
                               (=> (exists ((r Bankaccount))(= (Status_Var_v2 t0) r)) (not (Status_isN_v2 t0))))) :named status-v2-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Bankaccount_Proj_b_id (Status_Var_v2 t0)) (Status_Param_ac_id2 t0))) :named status-v2-select-prop))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       RW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named deposit-deposit-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Status))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named deposit-status-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Status) (= (type t2) Deposit))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        (or (or false
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t2)
                                (RW_Bankaccount r t1 t2)
                                (= (Bankaccount_Proj_b_id r) (Status_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t2))  true)))
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t2)
                                (RW_Bankaccount r t1 t2)
                                (= (Bankaccount_Proj_b_id r) (Status_Param_ac_id2 t1))  true
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t2))  true))) )))
                                :named status-deposit-rw-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Status) (= (type t2) Status))
                    (=> (and (RW t1 t2) (not (= t1 t2)))
                        false )))
                                :named status-status-rw-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WR-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named deposit-deposit-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Status))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        (or (or false
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t1)
                                (WR_Bankaccount r t1 t2)
                                (not (Status_isN_v1 t2))
                                (= (Bankaccount_Proj_b_id r) (Status_Param_ac_id t2))  true
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t1))  true)))
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t1)
                                (WR_Bankaccount r t1 t2)
                                (not (Status_isN_v2 t2))
                                (= (Bankaccount_Proj_b_id r) (Status_Param_ac_id2 t2))  true
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t1))  true))) )))
                                :named deposit-status-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Status) (= (type t2) Deposit))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named status-deposit-wr-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Status) (= (type t2) Status))
                    (=> (and (WR t1 t2) (not (= t1 t2)))
                        false )))
                                :named status-status-wr-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        (or false
                            (exists ((r Bankaccount))
                                (and 
                                (WW_Bankaccount r t1 t2)
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t2))  true))) )))
                                :named deposit-deposit-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Status))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named deposit-status-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Status) (= (type t2) Deposit))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named status-deposit-ww-then))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Status) (= (type t2) Status))
                    (=> (and (WW t1 t2) (not (= t1 t2)))
                        false )))
                                :named status-status-ww-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WR Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named deposit-deposit-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Status) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named deposit-status-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Status) (= (type t2) Deposit) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named status-deposit-then-wr))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Status) (= (type t2) Status) (not (= t1 t2)))
                    (=> false
                        (WR t1 t2) )))
                                :named status-status-then-wr))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WW Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Deposit) (not (= t1 t2)))
                    (=> (or false
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t2))  true)))
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named deposit-deposit-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Deposit) (= (type t2) Status) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named deposit-status-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Status) (= (type t2) Deposit) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named status-deposit-then-ww))

(assert (! (forall ((t1 T) (t2 T))
                (=> (and (= (type t1) Status) (= (type t2) Status) (not (= t1 t2)))
                    (=> false
                        (or (WW t1 t2) (WW t2 t1)) )))
                                :named status-status-then-ww))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                      Finalization                                                      
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(declare-fun D (T T) Bool)
(assert (! (forall ((t1 T)(t2 T)) (=> (D t1 t2) (or (WW t1 t2)(WR t1 t2)(RW t1 t2)))) :named gen-dep) )
(assert (! (exists ( (t1 T) (t2 T) (t3 T) (t4 T) (t5 T) (t6 T) (t7 T)) (and (not (= t1 t7))  (D t1 t2) (D t2 t3) (D t3 t4) (D t4 t5) (D t5 t6) (D t6 t7) (D t7 t1))) :named cycle))

;Guarantees
;PSI 
(assert (! (forall ((t1 T) (t2 T)) (=> (WW t1 t2) (vis t1 t2))):named psi))

(check-sat)
;(get-unsat-core)
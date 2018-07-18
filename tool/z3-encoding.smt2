
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       Constants                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(set-option :produce-unsat-cores true)

(declare-datatypes () ((TType (Deposit)))) 
(declare-datatypes () ((OType (Deposit_select_1)(Deposit_update_1))))  
(declare-sort T)
(declare-sort O)
(declare-fun type (T) TType)
(declare-fun otype (O) OType)  
(declare-fun parent (O) T)
(declare-fun sibling (O O) Bool)
(declare-fun program_order (O O) Bool)  

(declare-fun WR (T T) Bool)
(declare-fun RW (T T) Bool)
(declare-fun WW (T T) Bool)
(declare-fun WR_O (O O) Bool)
(declare-fun RW_O (O O) Bool)
(declare-fun WW_O (O O) Bool)
(declare-fun vis (T T) Bool)
(declare-fun ar (T T) Bool)

(assert (! (forall ((o1 O)(o2 O))(=> (program_order o1 o2)(sibling o1 o2))) :named po_then_sib))
(assert (! (forall ((o O))(not (program_order o o))) :named irreflx_po))
(assert (! (forall ((o1 O)(o2 O))(=> (= (parent o1)(parent o2))(sibling o1 o2))) :named par_then_sib))
(assert (! (forall ((o1 O)(o2 O))(=> (sibling o1 o2) (= (parent o1)(parent o2)))) :named sib_then_par))
(assert (! (forall ((o1 O)(o2 O))(=> (and (= (otype o1)(otype o2)) (= (parent o1)(parent o2)))(= o1 o2))) :named types_then_eq))
(assert (! (forall ((t T)) (not (or (WR t t) (RW t t) (WW t t))))     :named no_loops))
(assert (! (forall ((t1 T) (t2 T))   (=> (vis t1 t2) (not (vis t2 t1))))      :named acyc_vis))
(assert (! (forall ((t1 T) (t2 T) (t3 T))(=> (and (ar  t1 t2) (ar  t2 t3)) (ar  t1 t3)))  :named trans_ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (not (= t1 t2)) (xor (ar  t1 t2) (ar  t2 t1))))  :named total_ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (vis t1 t2) (ar t1 t2)))       :named vis_in_ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (WR t1 t2) (vis t1 t2)))       :named wr_then_vis))
(assert (! (forall ((t1 T) (t2 T))   (=> (WW t1 t2) (ar t1 t2)))        :named ww->ar))
(assert (! (forall ((t1 T) (t2 T))   (=> (RW t1 t2) (not (vis t2 t1))))     :named rw_then_not_vis))
(assert (! (forall ((t T))     (not (ar t t)))          :named irreflx_ar))

(assert (! (forall ((o1 O))(=> (= (otype o1) Deposit_update_1) (= (type (parent o1)) Deposit))) :named op_types_to_dep1))
(assert (! (forall ((o1 O))(=> (= (otype o1) Deposit_select_1) (= (type (parent o1)) Deposit))) :named op_types_to_dep2))
(assert (! (forall ((o1 O))(=> (= (type (parent o1)) Deposit)(or (= (otype o1) Deposit_select_1)
                                                                 (= (otype o1) Deposit_update_1)))) :named dep_to_ops_type))

(assert (! (forall ((o1 O)(o2 O))(=> (WR_O o1 o2)(WR (parent o1)(parent o2)))) :named wr_op_txn))
(assert (! (forall ((o1 O)(o2 O))(=> (RW_O o1 o2)(RW (parent o1)(parent o2)))) :named rw_op_txn))
(assert (! (forall ((o1 O)(o2 O))(=> (WW_O o1 o2)(WW (parent o1)(parent o2)))) :named ww_op_txn))

(assert (! (forall ((t1 T)(t2 T))(=> (WW t1 t2) (exists ((o1 O)(o2 O)) (and (= (parent o1) t1)(= (parent o2) t2)(WW_O o1 o2))))) :named ww_to_ww_o))
(assert (! (forall ((t1 T)(t2 T))(=> (RW t1 t2) (exists ((o1 O)(o2 O)) (and (= (parent o1) t1)(= (parent o2) t2)(RW_O o1 o2))))) :named rw_to_rw_o))
(assert (! (forall ((t1 T)(t2 T))(=> (WR t1 t2) (exists ((o1 O)(o2 O)) (and (= (parent o1) t1)(= (parent o2) t2)(WR_O o1 o2))))) :named wr_to_wr_o))


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

;deposit_v1
(declare-fun Deposit_isN_v1 (T) Bool)
(declare-fun Deposit_Var_v1 (T) Bankaccount)
(assert (! (forall((t0 T))(and (=> (not (Deposit_isN_v1 t0)) (exists ((r Bankaccount))(= (Deposit_Var_v1 t0) r))) 
                               (=> (exists ((r Bankaccount))(= (Deposit_Var_v1 t0) r)) (not (Deposit_isN_v1 t0))))) :named deposit-v1-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Bankaccount_Proj_b_id (Deposit_Var_v1 t0)) (Deposit_Param_ac_id t0))) :named deposit-v1-select-prop))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       RW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Deposit) (= (type t2) Deposit))
                    (=> (and (RW_O o1 o2) (not (= t1 t2)))
                        (or false
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t2)
                                (RW_Bankaccount r t1 t2)
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t2))  true))) )))
                                :named deposit-deposit-rw-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WR-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Deposit) (= (type t2) Deposit))
                    (=> (and (WR_O o1 o2) (not (= t1 t2)))
                        (or false
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t1)
                                (WR_Bankaccount r t1 t2)
                                (not (Deposit_isN_v1 t2))
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t2))  true
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t1))  true))) )))
                                :named deposit-deposit-wr-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Deposit) (= (type t2) Deposit))
                    (=> (and (WW_O o1 o2) (not (= t1 t2)))
                        (or false
                            (exists ((r Bankaccount))
                                (and 
                                (WW_Bankaccount r t1 t2)
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t2))  true))) )))
                                :named deposit-deposit-ww-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WR Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Deposit) (= (type t2) Deposit) (not (= t1 t2)))
                    (=> false
                        (WR_O o1 o2) )))
                                :named deposit-deposit-then-wr))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WW Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Deposit) (= (type t2) Deposit) (not (= t1 t2)))
                    (=> (or false
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Deposit_Param_ac_id t2))  true)))
                        (or (WW_O o1 o2) (WW_O o2 o1)) )))
                                :named deposit-deposit-then-ww))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                      Finalization                                                      
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(declare-fun D (T T) Bool)
(assert (! (forall ((t1 T)(t2 T)) (=> (D t1 t2) (or (WW t1 t2)(WR t1 t2)(RW t1 t2)))) :named gen-dep) )
(assert (! (exists ( (t1 T) (t2 T) (t3 T)) (and (not (= t1 t3))  (D t1 t2) (D t2 t3) (D t3 t1))) :named cycle))

;Guarantees
;EC

(check-sat)
;(get-unsat-core) 
;(get-model)
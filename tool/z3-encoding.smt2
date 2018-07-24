
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       Constants                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(set-option :produce-unsat-cores true)

(declare-datatypes () ((TType (Insert1) (Read)))) 
(declare-datatypes () ((OType (Insert1_insert_1)(Insert1_insert_2) (Read_select_1)(Read_select_2)))) 
(declare-sort T)
(declare-sort O)
(declare-fun type (T) TType)
(declare-fun otype (O) OType)
(declare-fun is_write (O) Bool)
(declare-fun parent (O) T)
(declare-fun sibling (O O) Bool)
(declare-fun program_order (O O) Bool)  
(assert (forall ((o O))(=> (or (=(otype o) Insert1_insert_1)(=(otype o) Insert1_insert_2))(is_write o))))
(assert (forall ((o O))(=> (is_write o)(or (=(otype o) Insert1_insert_1)(=(otype o) Insert1_insert_2)))))

(assert (! (forall ((o1 O))(=> (= (otype o1) Insert1_insert_1) (= (type (parent o1)) Insert1))) :named op_types_Insert1_insert_1))
(assert (! (forall ((o1 O))(=> (= (otype o1) Insert1_insert_2) (= (type (parent o1)) Insert1))) :named op_types_Insert1_insert_2))
(assert (! (forall ((o1 O))(=> (= (otype o1) Read_select_1) (= (type (parent o1)) Read))) :named op_types_Read_select_1))
(assert (! (forall ((o1 O))(=> (= (otype o1) Read_select_2) (= (type (parent o1)) Read))) :named op_types_Read_select_2))

(declare-fun WR_O (O O) Bool)
(declare-fun RW_O (O O) Bool)
(declare-fun WW_O (O O) Bool)
(declare-fun vis (O O) Bool)
(declare-fun ar (O O) Bool)

(assert (! (forall ((o1 O)(o2 O))(=> (ar o1 o2)(and (is_write o1)(is_write o2)))) :named ar_on_writes))
(assert (! (forall ((o1 O)(o2 O))(=> (and (vis o1 o2)(is_write o1)(is_write o2))(ar o1 o2))) :named vis_then_ar))
(assert (! (forall ((o1 O) (o2 O))(=> (program_order o1 o2)(sibling o1 o2))) :named po_then_sib))
(assert (! (forall ((o  O))(not (program_order o o))) :named irreflx_po))
(assert (! (forall ((o1 O) (o2 O))(=> (= (parent o1)(parent o2))(sibling o1 o2))) :named par_then_sib))
(assert (! (forall ((o1 O) (o2 O))(=> (sibling o1 o2) (= (parent o1)(parent o2)))) :named sib_then_par))
(assert (! (forall ((o1 O) (o2 O))(=> (and (= (otype o1)(otype o2)) (= (parent o1)(parent o2)))(= o1 o2))) :named types_then_eq))
(assert (! (forall ((o  O))(not (or (WR_O o o) (RW_O o o) (WW_O o o))))     :named no_loops_o))
(assert (! (forall ((t1 O) (t2 O) (t3 O))(=> (and (ar  t1 t2) (ar  t2 t3)) (ar  t1 t3)))  :named trans_ar))
(assert (! (forall ((t1 O) (t2 O))(=> (and (is_write t1) (is_write t2) (not (= t1 t2)) (not (sibling t1 t2))) 
                                      (xor (ar  t1 t2) (ar  t2 t1))))  :named total_ar))
(assert (! (forall ((o1 O) (o2 O))   (=> (WR_O o1 o2) (vis o1 o2)))       :named wr_then_vis))
(assert (! (forall ((o1 O) (o2 O))   (=> (WW_O o1 o2) (ar o1 o2)))        :named ww->ar))
(assert (! (forall ((o1 O) (o2 O))   (=> (RW_O o1 o2) (not (vis o2 o1))))     :named rw_then_not_vis))
(assert (! (forall ((t O)) (not (ar t t)))          :named irreflx_ar))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                   Table Declarations                                                   
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(declare-sort Bankaccount)
(declare-fun Bankaccount_Proj_b_id (Bankaccount) Int)
(declare-fun Bankaccount_Proj_b_owner (Bankaccount) String)
(declare-fun Bankaccount_Proj_b_bal (Bankaccount) Int)
(assert (! (forall ((r1 Bankaccount)(r2 Bankaccount)) (=>
  (and (= (Bankaccount_Proj_b_id r1) (Bankaccount_Proj_b_id r2)))(= r1 r2))) :named pk-bankaccount) )
(declare-fun RW_Bankaccount_O (Bankaccount O O) Bool)
(declare-fun RW_Alive_Bankaccount (Bankaccount O O) Bool)
(declare-fun WR_Bankaccount_O (Bankaccount O O) Bool)
(declare-fun WR_Alive_Bankaccount (Bankaccount O O) Bool)
(declare-fun WW_Bankaccount_O (Bankaccount O O) Bool)
(declare-fun WW_Alive_Bankaccount (Bankaccount O O) Bool)
(declare-fun IsAlive_Bankaccount (Bankaccount T) Bool)
(assert (! (forall ((r Bankaccount)(t1 O)(t2 O)) (=> (RW_Alive_Bankaccount r t1 t2) (RW_O t1 t2))) :named bankaccount-RW-then-alive))
(assert (! (forall ((r Bankaccount)(o1 O)(o2 O)) (=> (RW_Bankaccount_O r o1 o2) (RW_O o1 o2))) :named bankaccount-RW-then-o))
(assert (! (forall ((r Bankaccount)(t1 O)(t2 O)) (=> (WR_Alive_Bankaccount r t1 t2) (WR_O t1 t2))) :named bankaccount-WR-then-alive))
(assert (! (forall ((r Bankaccount)(o1 O)(o2 O)) (=> (WR_Bankaccount_O r o1 o2) (WR_O o1 o2))) :named bankaccount-WR-then-o))
(assert (! (forall ((r Bankaccount)(t1 O)(t2 O)) (=> (WW_Alive_Bankaccount r t1 t2) (WW_O t1 t2))) :named bankaccount-WW-then-alive))
(assert (! (forall ((r Bankaccount)(o1 O)(o2 O)) (=> (WW_Bankaccount_O r o1 o2) (WW_O o1 o2))) :named bankaccount-WW-then-o))
(assert (! (forall ((r Bankaccount)(o1 O)(o2 O)(o3 O)) 
     (=> (and (not (sibling o2 o3)) (WR_Bankaccount_O r o2 o1)(RW_Bankaccount_O r o1 o3))(WW_Bankaccount_O r o2 o3))) :named bankaccount-lww-row))
(assert (! (forall ((r Bankaccount)(t1 O)(t2 O)(t3 O)) 
         (=> (and (WR_Alive_Bankaccount r t2 t1)(RW_Alive_Bankaccount r t1 t3))(WW_Alive_Bankaccount r t2 t3))) :named bankaccount-lww-alive))

;params
(declare-fun Insert1_Param_ac_id (T) Int)
(declare-fun Insert1_Param_ac_id2 (T) Int)
(declare-fun Read_Param_ac_id (T) Int)
(declare-fun Read_Param_ac_id2 (T) Int)

;read_v1
(declare-fun Read_isN_v1 (T) Bool)
(declare-fun Read_Var_v1 (T) Bankaccount)
(assert (! (forall((t0 T))(and (=> (not (Read_isN_v1 t0)) (exists ((r Bankaccount))(= (Read_Var_v1 t0) r))) 
                               (=> (exists ((r Bankaccount))(= (Read_Var_v1 t0) r)) (not (Read_isN_v1 t0))))) :named read-v1-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Bankaccount_Proj_b_id (Read_Var_v1 t0)) (Read_Param_ac_id t0))) :named read-v1-select-prop))
;read_v2
(declare-fun Read_isN_v2 (T) Bool)
(declare-fun Read_Var_v2 (T) Bankaccount)
(assert (! (forall((t0 T))(and (=> (not (Read_isN_v2 t0)) (exists ((r Bankaccount))(= (Read_Var_v2 t0) r))) 
                               (=> (exists ((r Bankaccount))(= (Read_Var_v2 t0) r)) (not (Read_isN_v2 t0))))) :named read-v2-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Bankaccount_Proj_b_id (Read_Var_v2 t0)) (Read_Param_ac_id2 t0))) :named read-v2-select-prop))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       RW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Insert1) (= (type t2) Insert1))
                    (=> (and (RW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named insert1-insert1-rw-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Insert1) (= (type t2) Read))
                    (=> (and (RW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named insert1-read-rw-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Insert1))
                    (=> (and (RW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        (or (or (or (or false
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Read_select_1)
                                (= (otype o2) Insert1_insert_1)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id t1))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t2))
                                (= (Bankaccount_Proj_b_owner r) "David")
                                (= (Bankaccount_Proj_b_bal r) (+ 100 10))  true
                                (not (IsAlive_Bankaccount r t1))
                                (RW_Alive_Bankaccount r o1 o2))))
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Read_select_1)
                                (= (otype o2) Insert1_insert_2)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id t1))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t2))
                                (= (Bankaccount_Proj_b_owner r) "George")
                                (= (Bankaccount_Proj_b_bal r) (+ 200 20))  true
                                (not (IsAlive_Bankaccount r t1))
                                (RW_Alive_Bankaccount r o1 o2))))
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Read_select_2)
                                (= (otype o2) Insert1_insert_1)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id2 t1))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t2))
                                (= (Bankaccount_Proj_b_owner r) "David")
                                (= (Bankaccount_Proj_b_bal r) (+ 100 10))  true
                                (not (IsAlive_Bankaccount r t1))
                                (RW_Alive_Bankaccount r o1 o2))))
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Read_select_2)
                                (= (otype o2) Insert1_insert_2)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id2 t1))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t2))
                                (= (Bankaccount_Proj_b_owner r) "George")
                                (= (Bankaccount_Proj_b_bal r) (+ 200 20))  true
                                (not (IsAlive_Bankaccount r t1))
                                (RW_Alive_Bankaccount r o1 o2)))) )))
                                :named read-insert1-rw-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Read))
                    (=> (and (RW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named read-read-rw-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WR-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Insert1) (= (type t2) Insert1))
                    (=> (and (WR_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named insert1-insert1-wr-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Insert1) (= (type t2) Read))
                    (=> (and (WR_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        (or (or (or (or false
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Insert1_insert_1)
                                (= (otype o2) Read_select_1)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id t2))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t1))
                                (= (Bankaccount_Proj_b_owner r) "David")
                                (= (Bankaccount_Proj_b_bal r) (+ 100 10))  true
                                (IsAlive_Bankaccount r t2)
                                (not (Read_isN_v1 t2))
                                (WR_Alive_Bankaccount r o1 o2))))
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Insert1_insert_1)
                                (= (otype o2) Read_select_2)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id2 t2))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t1))
                                (= (Bankaccount_Proj_b_owner r) "David")
                                (= (Bankaccount_Proj_b_bal r) (+ 100 10))  true
                                (IsAlive_Bankaccount r t2)
                                (not (Read_isN_v2 t2))
                                (WR_Alive_Bankaccount r o1 o2))))
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Insert1_insert_2)
                                (= (otype o2) Read_select_1)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id t2))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t1))
                                (= (Bankaccount_Proj_b_owner r) "George")
                                (= (Bankaccount_Proj_b_bal r) (+ 200 20))  true
                                (IsAlive_Bankaccount r t2)
                                (not (Read_isN_v1 t2))
                                (WR_Alive_Bankaccount r o1 o2))))
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Insert1_insert_2)
                                (= (otype o2) Read_select_2)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id2 t2))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t1))
                                (= (Bankaccount_Proj_b_owner r) "George")
                                (= (Bankaccount_Proj_b_bal r) (+ 200 20))  true
                                (IsAlive_Bankaccount r t2)
                                (not (Read_isN_v2 t2))
                                (WR_Alive_Bankaccount r o1 o2)))) )))
                                :named insert1-read-wr-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Insert1))
                    (=> (and (WR_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named read-insert1-wr-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Read))
                    (=> (and (WR_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named read-read-wr-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Insert1) (= (type t2) Insert1))
                    (=> (and (WW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named insert1-insert1-ww-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Insert1) (= (type t2) Read))
                    (=> (and (WW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named insert1-read-ww-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Insert1))
                    (=> (and (WW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named read-insert1-ww-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Read))
                    (=> (and (WW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named read-read-ww-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WR Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Insert1) (= (type t2) Insert1) (not (= t1 t2)))
                    (=> false
                        (WR_O o1 o2) )))
                                :named insert1-insert1-then-wr))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Insert1) (= (type t2) Read) (not (= t1 t2)))
                    (=> (or (or (or (or false
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Insert1_insert_1)
                                (= (otype o2) Read_select_1)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id t2))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t1))
                                (= (Bankaccount_Proj_b_owner r) "David")
                                (= (Bankaccount_Proj_b_bal r) (+ 100 10))  true
                                (not (Read_isN_v1 t2))
                                (IsAlive_Bankaccount r t2)
                                (WR_Alive_Bankaccount r o1 o2))))
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Insert1_insert_1)
                                (= (otype o2) Read_select_2)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id2 t2))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t1))
                                (= (Bankaccount_Proj_b_owner r) "David")
                                (= (Bankaccount_Proj_b_bal r) (+ 100 10))  true
                                (not (Read_isN_v2 t2))
                                (IsAlive_Bankaccount r t2)
                                (WR_Alive_Bankaccount r o1 o2))))
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Insert1_insert_2)
                                (= (otype o2) Read_select_1)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id t2))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t1))
                                (= (Bankaccount_Proj_b_owner r) "George")
                                (= (Bankaccount_Proj_b_bal r) (+ 200 20))  true
                                (not (Read_isN_v1 t2))
                                (IsAlive_Bankaccount r t2)
                                (WR_Alive_Bankaccount r o1 o2))))
                            (exists ((r Bankaccount))
                                (and 
                                (= (otype o1) Insert1_insert_2)
                                (= (otype o2) Read_select_2)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id2 t2))  true
                                ;insert
                                (= (Bankaccount_Proj_b_id r) (Insert1_Param_ac_id t1))
                                (= (Bankaccount_Proj_b_owner r) "George")
                                (= (Bankaccount_Proj_b_bal r) (+ 200 20))  true
                                (not (Read_isN_v2 t2))
                                (IsAlive_Bankaccount r t2)
                                (WR_Alive_Bankaccount r o1 o2))))
                        (WR_O o1 o2) )))
                                :named insert1-read-then-wr))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Insert1) (not (= t1 t2)))
                    (=> false
                        (WR_O o1 o2) )))
                                :named read-insert1-then-wr))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Read) (not (= t1 t2)))
                    (=> false
                        (WR_O o1 o2) )))
                                :named read-read-then-wr))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WW Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Insert1) (= (type t2) Insert1) (not (= t1 t2)))
                    (=> false
                        (or (WW_O o1 o2) (WW_O o2 o1)) )))
                                :named insert1-insert1-then-ww))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Insert1) (= (type t2) Read) (not (= t1 t2)))
                    (=> false
                        (or (WW_O o1 o2) (WW_O o2 o1)) )))
                                :named insert1-read-then-ww))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Insert1) (not (= t1 t2)))
                    (=> false
                        (or (WW_O o1 o2) (WW_O o2 o1)) )))
                                :named read-insert1-then-ww))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Read) (not (= t1 t2)))
                    (=> false
                        (or (WW_O o1 o2) (WW_O o2 o1)) )))
                                :named read-read-then-ww))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                      Finalization                                                      
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(declare-fun D (O O) Bool)
(declare-fun X (O O) Bool)

(assert (! (forall ((t1 O)(t2 O)) (=> (D t1 t2) (and (not (sibling t1 t2))(or (WW_O t1 t2)(WR_O t1 t2)(RW_O t1 t2))))) :named gen-dep) )
(assert (! (forall ((t1 O)(t2 O)) (=> (X t1 t2) (or (sibling t1 t2)(D t1 t2)))) :named gen-depx) )
(assert (! (exists ( (t1 O) (t2 O) (t3 O) (t4 O)) (and (not (= t1 t4)) (D t1 t2) (X t2 t3) (X t3 t4) (X t4 t1))) :named cycle))

;Guarantees
;RC
(assert (! (forall ((o1 O)(o2 O)(o3 O))(=> (and (vis o1 o2)(sibling o1 o3))(vis o3 o2))) :named rc))
(assert (! (forall ((o1 O)(o2 O)(o3 O))(=> (is_write o3)(and (ar o1 o2)(sibling o2 o3))(ar o1 o3))) :named rc2))

(check-sat)
;(get-unsat-core) 
;(get-model)

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       Constants                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(set-option :produce-unsat-cores true)

(declare-datatypes () ((TType (Write) (Read)))) 
(declare-datatypes () ((OType (Write_update_1)(Write_update_2)(Read_select_1))))  
(declare-sort T)
(declare-sort O)
(declare-fun type (T) TType)
(declare-fun otype (O) OType)  
(declare-fun parent (O) T)
(declare-fun sibling (O O) Bool)
(declare-fun program_order (O O) Bool)  

(declare-fun WR_O (O O) Bool)
(declare-fun RW_O (O O) Bool)
(declare-fun WW_O (O O) Bool)
(declare-fun vis (O O) Bool)
(declare-fun ar (O O) Bool)

(assert (! (forall ((o1 O))(=> (= (otype o1) Read_select_1) (= (type (parent o1)) Read))) :named op_types_to_dep1))
(assert (! (forall ((o1 O))(=> (= (otype o1) Write_update_1) (= (type (parent o1)) Write))) :named op_types_to_dep2))
(assert (! (forall ((o1 O))(=> (= (otype o1) Write_update_2) (= (type (parent o1)) Write))) :named op_types_to_dep3))
(assert (! (forall ((o1 O))(=> (= (type (parent o1)) Read)(or (= (otype o1) Read_select_1)))) :named dep_to_ops_type))
(assert (! (forall ((o1 O))(=> (= (type (parent o1)) Write)(or (= (otype o1) Write_update_1)
                                                              (= (otype o1) Write_update_2)))) :named dep_to_ops_typeX))
(declare-fun is_write (O) Bool)
(assert (forall ((o1 O)(o2 O))(=> (ar o1 o2)(and (is_write o1)(is_write o2)))))
(assert (forall ((o1 O)(o2 O))(=> (vis o1 o2)(and (is_write o1)(not (is_write o2))))))
(assert (forall ((o O))(=> (is_write o)(or (=(otype o)Write_update_1)(= (otype o)Write_update_2)))))
(assert (forall ((o O))(=> (or (=(otype o)Write_update_1)(= (otype o)Write_update_2))(is_write o))))
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
(declare-fun RW_Alive_Bankaccount (Bankaccount T T) Bool)
(declare-fun WR_Bankaccount_O (Bankaccount O O) Bool)
(declare-fun WR_Alive_Bankaccount (Bankaccount T T) Bool)
(declare-fun WW_Bankaccount_O (Bankaccount O O) Bool)
(declare-fun WW_Alive_Bankaccount (Bankaccount T T) Bool)
(declare-fun IsAlive_Bankaccount (Bankaccount T) Bool)
;(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (RW_Alive_Bankaccount r t1 t2) (RW t1 t2))) :named bankaccount-RW-then-alive))
(assert (! (forall ((r Bankaccount)(o1 O)(o2 O)) (=> (RW_Bankaccount_O r o1 o2) (RW_O o1 o2))) :named bankaccount-RW-then-o))
;(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (RW_Bankaccount r t1 t2) 
;                                            (exists ((o1 O)(o2 O)) 
;                                                            (and (= (parent o1) t1)(= (parent o2) t2)
;                                                                 (RW_Bankaccount_O r o1 o2))))) :named RWo_to_RW_o))
;(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WR_Alive_Bankaccount r t1 t2) (WR t1 t2))) :named bankaccount-WR-then-alive))
(assert (! (forall ((r Bankaccount)(o1 O)(o2 O)) (=> (WR_Bankaccount_O r o1 o2) (WR_O o1 o2))) :named bankaccount-WR-then-o))
;(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WR_Bankaccount r t1 t2) 
;                                            (exists ((o1 O)(o2 O)) 
;                                                            (and (= (parent o1) t1)(= (parent o2) t2)
;                                                                 (WR_Bankaccount_O r o1 o2))))) :named WRo_to_WR_o))
;(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WW_Alive_Bankaccount r t1 t2) (WW t1 t2))) :named bankaccount-WW-then-alive))
(assert (! (forall ((r Bankaccount)(o1 O)(o2 O)) (=> (WW_Bankaccount_O r o1 o2) (WW_O o1 o2))) :named bankaccount-WW-then-o))
;(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)) (=> (WW_Bankaccount r t1 t2) 
;                                            (exists ((o1 O)(o2 O)) 
;                                                            (and (= (parent o1) t1)(= (parent o2) t2)
;                                                                 (WW_Bankaccount_O r o1 o2))))) :named WWo_to_WW_o))
(assert (! (forall ((r Bankaccount)(o1 O)(o2 O)(o3 O)) 
     (=> (and (not (sibling o2 o3)) (WR_Bankaccount_O r o2 o1)(RW_Bankaccount_O r o1 o3))(WW_Bankaccount_O r o2 o3))) :named bankaccount-lww-row))
(assert (! (forall ((r Bankaccount)(t1 T)(t2 T)(t3 T)) 
         (=> (and (WR_Alive_Bankaccount r t2 t1)(RW_Alive_Bankaccount r t1 t3))(WW_Alive_Bankaccount r t2 t3))) :named bankaccount-lww-alive))

;params
(declare-fun Write_Param_ac_id (T) Int)
(declare-fun Read_Param_ac_id (T) Int)

;read_v1
(declare-fun Read_isN_v1 (T) Bool)
(declare-fun Read_Var_v1 (T) Bankaccount)
(assert (! (forall((t0 T))(and (=> (not (Read_isN_v1 t0)) (exists ((r Bankaccount))(= (Read_Var_v1 t0) r))) 
                               (=> (exists ((r Bankaccount))(= (Read_Var_v1 t0) r)) (not (Read_isN_v1 t0))))) :named read-v1-isnull-prop) )
(assert (! (forall ((t0 T)) (= (Bankaccount_Proj_b_id (Read_Var_v1 t0)) (Read_Param_ac_id t0))) :named read-v1-select-prop))


;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       RW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Write) (= (type t2) Write))
                    (=> (and (RW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named write-write-rw-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Write) (= (type t2) Read))
                    (=> (and (RW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named write-read-rw-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Write))
                    (=> (and (RW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        (or (or false
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t2)
                                (RW_Bankaccount_O r o1 o2)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t2))  true)))
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t2)
                                (RW_Bankaccount_O r o1 o2)
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t2))  true))) )))
                                :named read-write-rw-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Read))
                    (=> (and (RW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named read-read-rw-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WR-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Write) (= (type t2) Write))
                    (=> (and (WR_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named write-write-wr-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Write) (= (type t2) Read))
                    (=> (and (WR_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        (or (or false
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t1)
                                (WR_Bankaccount_O r o1 o2)
                                (not (Read_isN_v1 t2))
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id t2))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t1))  true)))
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t1)
                                (WR_Bankaccount_O r o1 o2)
                                (not (Read_isN_v1 t2))
                                (= (Bankaccount_Proj_b_id r) (Read_Param_ac_id t2))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t1))  true))) )))
                                :named write-read-wr-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Write))
                    (=> (and (WR_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named read-write-wr-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Read))
                    (=> (and (WR_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named read-read-wr-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       WW-> Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Write) (= (type t2) Write))
                    (=> (and (WW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        (or (or (or (or false
                            (exists ((r Bankaccount))
                                (and 
                                (WW_Bankaccount_O r o1 o2)
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t2))  true)))
                            (exists ((r Bankaccount))
                                (and 
                                (WW_Bankaccount_O r o1 o2)
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t2))  true)))
                            (exists ((r Bankaccount))
                                (and 
                                (WW_Bankaccount_O r o1 o2)
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t2))  true)))
                            (exists ((r Bankaccount))
                                (and 
                                (WW_Bankaccount_O r o1 o2)
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t2))  true))) )))
                                :named write-write-ww-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Write) (= (type t2) Read))
                    (=> (and (WW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named write-read-ww-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Write))
                    (=> (and (WW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named read-write-ww-then))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and  (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Read))
                    (=> (and (WW_O o1 o2) (not (= o1 o2)) (not (= t1 t2)))
                        false )))
                                :named read-read-ww-then))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WR Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Write) (= (type t2) Write) (not (= t1 t2)))
                    (=> false
                        (WR_O o1 o2) )))
                                :named write-write-then-wr))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Write) (= (type t2) Read) (not (= t1 t2)))
                    (=> false
                        (WR_O o1 o2) )))
                                :named write-read-then-wr))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Write) (not (= t1 t2)))
                    (=> false
                        (WR_O o1 o2) )))
                                :named read-write-then-wr))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Read) (not (= t1 t2)))
                    (=> false
                        (WR_O o1 o2) )))
                                :named read-read-then-wr))

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;                                                       ->WW Rules                                                       
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Write) (= (type t2) Write) (not (= t1 t2)))
                    (=> (or (or (or (or false
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t2))  true)))
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t2))  true)))
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t2))  true)))
                            (exists ((r Bankaccount))
                                (and 
                                (IsAlive_Bankaccount r t1)
                                (IsAlive_Bankaccount r t2)
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t1))  true
                                (= (Bankaccount_Proj_b_id r) (Write_Param_ac_id t2))  true)))
                        (or (WW_O o1 o2) (WW_O o2 o1)) )))
                                :named write-write-then-ww))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Write) (= (type t2) Read) (not (= t1 t2)))
                    (=> false
                        (or (WW_O o1 o2) (WW_O o2 o1)) )))
                                :named write-read-then-ww))

(assert (! (forall ((t1 T) (t2 T) (o1 O) (o2 O))
                (=> (and (= (parent o1) t1) (= (parent o2) t2) (= (type t1) Read) (= (type t2) Write) (not (= t1 t2)))
                    (=> false
                        (or (WW_O o1 o2) (WW_O o2 o1)) )))
                                :named read-write-then-ww))

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
(assert (! (exists ( (t1 O) (t2 O) (t3 O) (t4 O) (t5 O)) (and (not (= t1 t5)) (D t1 t2) (X t2 t3) (X t3 t4) (X t4 t5) (X t5 t1))) :named cycle))

;Guarantees
;PSI 
(assert (! (forall ((t1 O) (t2 O)) (=> (WW_O t1 t2) (vis t1 t2))):named psi))
;RC
(assert (forall ((o1 O)(o2 O)(o3 O))(=> (and (vis o1 o3)(sibling o1 o2))(vis o2 o3))))
(assert (forall ((o1 O)(o2 O)(o3 O))(=> (and (ar  o1 o3)(sibling o1 o2))(ar  o2 o3))))

(check-sat)
;(get-unsat-core) 
(get-model)
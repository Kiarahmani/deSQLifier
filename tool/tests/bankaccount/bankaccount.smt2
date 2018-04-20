(set-option :produce-unsat-cores true)
;=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
; Primitive types
(declare-datatypes () ((TType (P1)))) ;all extracted programs
(declare-sort T) 
(declare-fun type (T) TType)

; Basic Relations 
(declare-fun WR (T T) Bool)
(declare-fun RW (T T) Bool)
(declare-fun WW (T T) Bool)
(declare-fun vis (T T) Bool)
(declare-fun ar (T T) Bool)

; Basic Assertions on Basic Relations
(assert (! (forall ((t T))  		 (not (or (WR t t) (RW t t) (WW t t)))) 		:named no_loops))
(assert (! (forall ((t1 T) (t2 T)) 	 (=> (vis t1 t2) (not (vis t2 t1)))) 			:named acyc_vis)) 
(assert (! (forall ((t1 T) (t2 T) (t3 T))(=> (and (ar  t1 t2) (ar  t2 t3)) (ar  t1 t3)))	:named trans_ar)) 
(assert (! (forall ((t1 T) (t2 T)) 	 (=> (not (= t1 t2)) (xor (ar  t1 t2) (ar  t2 t1))))	:named total_ar)) 
(assert (! (forall ((t1 T) (t2 T)) 	 (=> (vis t1 t2) (ar t1 t2)))				:named vis_in_ar)) 
(assert (! (forall ((t1 T) (t2 T)) 	 (=> (WR t1 t2) (vis t1 t2)))				:named wr_then_vis))
(assert (! (forall ((t1 T) (t2 T)) 	 (=> (WW t1 t2) (ar t1 t2)))				:named ww->ar)) 
(assert (! (forall ((t1 T) (t2 T)) 	 (=> (RW t1 t2) (not (vis t2 t1))))			:named rw_then_not_vis)) 
(assert (! (forall ((t T)) 		 (not (ar t t)))					:named irreflx_ar)) 


; Conditions Extracted from the Transactional Program
;---------------------------------------------------------------------------------------------------- 

; Object Definitions:
(declare-sort BankAccount)
(declare-fun accID (BankAccount) Int)
(declare-fun accBal (BankAccount) Int)
(assert (forall ((r1 BankAccount)(r2 BankAccount)) (=> (= (accID r1) (accID r2)) (= r1 r2))))
(declare-fun P1_read_acc (T) Int)
(declare-fun P1_write_acc (T BankAccount) Bool)



; Extracted Conditions
(assert (! 
	(forall ((t1 T) (t2 T))
		(=> (and (RW t1 t2) (not (= t1 t2)))
		(exists ((b BankAccount)) 
			(and (= (accID b) (P1_read_acc t1))  
		     	     (= (accID b) (P1_read_acc t2))))))
	:named exts_rec) )

(assert (!
	(forall ((t1 T) (t2 T) (b BankAccount)) 
		(=> (and (not (= t1 t2))
			 (= (accID b) (P1_read_acc t1)) 
		     	 (= (accID b) (P1_read_acc t2)) )
		(or (WW t1 t2) (WW t2 t1))))
	:named sffcnt_cnflct))


;---------------------------------------------------------------------------------------------------- 
; Cycles to Check
(assert (exists ((t1 T) (t2 T)) 
		(and (not (= t1 t2)) (RW t1 t2) (RW t2 t1))))


;---------------------------------------------------------------------------------------------------- 
; Consistency and Isolation Guarantees


;(assert (! (forall ((t1 T) (t2 T)) (=> (ar t1 t2) (vis t1 t2))):named ser )) ;SER
(assert (! (forall ((t1 T) (t2 T)) (=> (WW t1 t2) (vis t1 t2))):named psi)) ;PSI
;(assert (! (forall ((t1 T) (t2 T) (t3 T)) 	(=> (and (vis  t1 t2) (vis  t2 t3)) (vis  t1 t3))):named cc)) ;CC



(check-sat)
;(get-unsat-core)
;(get-model)

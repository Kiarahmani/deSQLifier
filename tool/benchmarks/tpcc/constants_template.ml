(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program SERIALIZABILITYectnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = corr
let _MAX_CYCLE_LENGTH = cl
let _GUARANTEE = [(SER,Some "New_order",None);
                  (SER,Some "Payment",None);
                  (RR,Some "Order_status",None); (*when rr-> unsat in es and sat in ser*)
                  (SER, Some "Stock_level",None); (*when rr-> sat in both cases*) (*both cases unsat when column checks added to range select*)
                  (SER,Some "Delivery",None)]

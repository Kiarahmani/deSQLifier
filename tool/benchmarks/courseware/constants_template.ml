(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program SERIALIZABILITYectnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = corr
let _MAX_CYCLE_LENGTH = cl
let _GUARANTEE = [(RC,Some "Enroll_student",None);
                  (RC,Some "Query_student",None); 
                  (RC,Some "Add_course",None); 
                  (RC,Some "Register",None);
                  (RC,Some "Remove_course",None) 
                 ]

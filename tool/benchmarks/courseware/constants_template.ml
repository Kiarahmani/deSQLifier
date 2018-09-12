(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program SERIALIZABILITYectnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = corr
let _MAX_CYCLE_LENGTH = cl
let _GUARANTEE = [(EC,Some "Enroll_student",None); 
                  (PSI,Some "Enroll_student2",None);
                  (EC,Some "Query_student",None); 
                  (EC,Some "Query_student2",None); 
                  (EC,Some "Query_course",None); 
                  (EC,Some "Query_course2",None); 
                  (EC,Some "Add_course",None); 
                  (EC,Some "Register",None);
                  (SER,Some "Register2",None);
                  (SER,Some "Increase_capacity",None);
                  (SER,Some "Expel_student",None);
                  (EC,Some "Enter_grade",None);
                  (EC,Some "Remove_course",None) 
                 ]
(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program SERIALIZABILITYectnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = SERIALIZABILITY
let _MAX_CYCLE_LENGTH = 3
let _GUARANTEE = [(EC,Some "Write",None);
                  (EC,Some "Read",None)]

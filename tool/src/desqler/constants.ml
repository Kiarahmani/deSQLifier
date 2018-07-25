(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program correctnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = EVENTUAL_SERIALIZABILITY
(*let _CORRECTNESS = SERIALIZABILITY*)
let _MAX_CYCLE_LENGTH = 4
let _GUARANTEE = [(PSI,Some "Read",None);(SER,Some "Write1",None);(SER,Some "Write2",None)]



(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program SERIALIZABILITYectnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = SERIALIZABILITY
let _MAX_CYCLE_LENGTH = 6
let _GUARANTEE = [
  (SER,Some "Add_link",None); 
  (SER,Some "Add_node",None); 
  (EC,Some "Count_link",None); 
  (SER,Some "Delete_link",None); 
  (EC,Some "",None); 
  (EC,Some "",None); 
  (EC,Some "",None); 
  (EC,Some "",None); 
  (EC,Some "",None); 
  (EC,Some "",None); 
]

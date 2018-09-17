(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program SERIALIZABILITYectnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = corr
let _MAX_CYCLE_LENGTH = cl
let _GUARANTEE = [
  (SER,Some "Add_link",None); 
  (SER,Some "Add_node",None); 
  (EC,Some "Count_link",None); 
  (SER,Some "Delete_link",None); 
  (EC,Some "Delete_Node",None); 
  (SER,Some "Get_link",None); 
  (EC,Some "Get_link_list",None); 
  (EC,Some "Get_node",None); 
  (EC,Some "Update_link",None); 
  (RC,Some "Update_node",None); 
]

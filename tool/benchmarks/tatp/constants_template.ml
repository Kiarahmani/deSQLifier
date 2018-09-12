(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program SERIALIZABILITYectnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = corr
let _MAX_CYCLE_LENGTH = cl
let _GUARANTEE = [
  (EC,Some "Delete_call_forwarding",None); 
  (EC,Some "Get_access_data",None); 
  (EC,Some "Get_new_destination",None); 
  (EC,Some "Get_subscriber_data",None); 
  (EC,Some "Insert_call_forwarding",None); 
  (EC,Some "Update_location",None); 
  (RC,Some "Update_subscriber_data",None); 
]

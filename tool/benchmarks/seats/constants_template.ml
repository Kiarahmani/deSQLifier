(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program SERIALIZABILITYectnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = corr
let _MAX_CYCLE_LENGTH = cl
let _GUARANTEE = [
  (RC,Some "Update_reservation",None); (*must be ser, even in isolation*)
  (RC,Some "Update_customer",None); (*can be rc*)
  (RC,Some "Find_open_seats",None); (*must be ser*)
  (SER,Some "Delete_reservation",None);
  (RC,Some "Find_flights",None); (*No wekaer than SER*)
  (SER,Some "New_reservation",None) (*can't go weaker than SER *)
]

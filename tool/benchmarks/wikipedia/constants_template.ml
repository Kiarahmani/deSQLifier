(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program SERIALIZABILITYectnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = corr
let _MAX_CYCLE_LENGTH = cl
let _GUARANTEE = [
  (RC,Some "Get_page_anonymous",None);
  (RC,Some "Get_page_authenticated",None);
  (RC,Some "Add_to_watchlist",None);
  (RC,Some "Remove_from_watchlist",None);
  (SER,Some "Update_page",None)

]

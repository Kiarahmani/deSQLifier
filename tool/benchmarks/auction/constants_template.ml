(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program SERIALIZABILITYectnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = corr
let _MAX_CYCLE_LENGTH = cl
let _GUARANTEE = [
  (EC,Some "New_user",None); 
  (SER,Some "New_item",None); 
  (SER,Some "New_bid",None);
  (RC,Some "New_comment",None);
  (EC,Some "New_comment_response",None);
  (SER,Some "New_purchase",None);
  (RC,Some "New_feedback",None);
  (RC,Some "Get_item",None);
  (EC,Some "Update_item",None);
  (RC,Some "Check_winning_bids",None);
  (EC,Some "Post_auction",None);
  (RC,Some "Get_comment",None);

]

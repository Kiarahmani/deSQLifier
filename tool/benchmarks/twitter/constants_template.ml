(*isolation/consistency guarantees offered by the stores*)
type g = SER | CC | RR | PSI | EC | RC
(*program SERIALIZABILITYectnees criterion against which the verification is done*)
type c = SERIALIZABILITY | EVENTUAL_SERIALIZABILITY



(*SET THE FOLLOWING CONSTANTS BEFORE RUNNING YOUR ANALYSIS*)
let _CORRECTNESS = corr
let _MAX_CYCLE_LENGTH = cl
let _GUARANTEE = [
  (EC,Some "Get_followers",None); 
  (EC,Some "Get_tweet",None); 
  (EC,Some "Get_tweet_from_following",None); 
  (EC,Some "Get_user_tweets",None); 
  (SER,Some "Insert_tweet",None); 
]

type g = SER | CC | RR | PSI | EC | RC


(*set the followig for your analysis*)
let _MAX_CYCLE_LENGTH = 4
let _GUARANTEE = [
                  (*(SER,Some "New_order",Some "Payment");
                  (SER,Some "New_order",Some "New_order");
                  (SER,Some "New_order",Some "Delivery");

                  (SER,Some "Delivery",Some "Payment");
                  (SER,Some "Delivery",Some "Delivery");

                  (SER,Some "Payment",Some "Payment");*)
                  (EC,None,None)]



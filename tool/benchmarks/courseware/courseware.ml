let unimpl () = failwith "Unimpl"
type table_name = 
  | Student | Course | Register |Instructor |Transcript |College
type column_name = 
  |S_all |S_id |S_coid |S_name |S_age |S_gender
  |C_all |C_id |C_title |C_coid |C_iid |C_credit |C_enrollcount |C_capacity
  |R_all |R_sid |R_cid |R_regdate 
  |I_all |I_id |I_name |I_age |I_specialty
  |T_all |T_sid |T_cid |T_iid |T_grade
  |CO_all | CO_id | CO_name |CO_founded |CO_stcount

module SQL: 
sig
  val select1:      table_name -> column_name  -> ('a -> bool) -> 'a
  val select:       table_name -> column_name -> ('a -> bool) -> 'a list
  val select_max:   table_name -> column_name -> ('a -> bool) -> 'a
  val select_min:   table_name -> column_name -> ('a -> bool) -> 'a
  val select_count: table_name -> column_name -> ('a -> bool) -> int
  val insert:       table_name  ->  'a -> unit
  val delete:       table_name  -> ('a -> bool) -> unit
  val update:       table_name  -> ('a -> unit) -> ('a -> bool) -> unit
  val choose:  ('a -> bool) -> 'a list -> 'a
  val foreach: 'a list -> ('a -> unit) -> unit
end = 
struct
  let select = unimpl ()
  let select1 = unimpl ()
  let select_max = unimpl ()
  let select_count = unimpl ()
  let select_min = unimpl ()
  let insert = unimpl ()
  let delete = unimpl ()
  let update = unimpl ()
  let choose = unimpl ()
  let foreach = unimpl ()
end
(*----------------------------------------------------------------------------------------------------*)

type student = {s_id:int; mutable s_name:string; mutable s_age:int; mutable s_gender:string; mutable s_coid:int}
type instructor = {i_id:int; mutable i_name:string; mutable i_age:int; mutable i_specialty:string}
type transcript = {t_s_id:int; t_c_id:int; mutable t_grade:int; mutable t_i_id:int}
type college = {co_id:int; mutable co_name:string; mutable co_founded:string; mutable co_stcount:int}
type course = {c_id:int; mutable c_title:string; mutable c_coid:int; mutable c_iid:int; mutable c_credit:int; mutable c_capacity:int}
type register = {r_s_id:int; r_c_id:int; mutable r_regdate:string}

(*----------------------------------------------------------------------------------------------------*)


(*TXN 1*)
let enroll_student_txn (input_s_id:int) (input_s_coid:int) (input_s_name:string) (input_s_age:int)(input_s_gender:string) =
  SQL.insert Student {s_id=input_s_id; s_coid=input_s_coid; s_name=input_s_name; s_age=input_s_age; s_gender=input_s_gender}
  
let enroll_student2_txn (input_s_id:int) (input_s_coid:int) (input_s_name:string) (input_s_age:int)(input_s_gender:string) =
  let v1 = SQL.select1 College CO_stcount
                   (fun u -> (u.co_id = input_s_coid)) in 
  SQL.update College
    (*do:*)    (fun u -> begin u.co_stcount <- v1.co_stcount+1; end)    
      (*where:*) (fun u -> u.co_id = input_s_coid)

(* TXN 2*)
let query_student_txn (input_s_id:int) =
  let v0 = SQL.select1 Student S_all 
      (fun r -> r.s_id = input_s_id) in
  let v2 = SQL.select1  College C_all 
      (fun r -> r.co_id = v0.s_coid) in
  ()

let query_student2_txn (input_s_id:int) =
  let v4 = SQL.select Transcript T_all
      (fun r -> r.t_s_id=input_s_id) in
  let v1 = SQL.select Register R_all
      (fun r -> r.r_s_id=input_s_id) in
  SQL.foreach v1
    begin fun loop_var_1 ->
      let v3 = SQL.select1 Course C_title
          (fun r -> r.c_id=loop_var_1.r_c_id) in
      ()
    end

(*TXN 3*)
let add_course_txn (input_c_id:int) (input_c_coid:int) (input_c_title:string) (input_c_iid:int)(input_c_credit:int)(input_c_capacity:int) =
  SQL.insert Course 
    {c_id=input_c_id; c_title=input_c_title; c_coid=input_c_coid; 
     c_iid=input_c_iid; c_credit=input_c_credit; c_capacity=input_c_capacity}


(*TXN 4*)
let remove_course_txn (input_c_id:int)  = 
  SQL.delete Course (fun r -> r.c_id=input_c_id);
  SQL.delete Register (fun r -> r.r_c_id=input_c_id)


(*TXN 5*)
let register_txn (input_s_id:int) (input_c_id:int) (input_today:string) = 
  SQL.insert Register {r_s_id=input_s_id; r_c_id=input_c_id; r_regdate=input_today}


let register2_txn (input_s_id:int) (input_c_id:int) (input_today:string) = 
  let v1 = SQL.select1 Course C_capacity
      (fun r -> r.c_id = input_c_id) in
  SQL.update Course
    (*do:*)    (fun u -> begin u.c_capacity <- v1.c_capacity-1; end)    
    (*where:*) (fun u -> u.c_id = input_c_id)


(*TXN 6*)
let query_course2_txn (input_c_id:int) =
  let v0 = SQL.select1 Course C_all 
      (fun r -> r.c_id = input_c_id) in
  let v1 = SQL.select Register R_all
      (fun r -> r.r_c_id=input_c_id) in
  ()
  
let query_course_txn (v1:register list) =
  SQL.foreach v1
    begin fun loop_var_1 ->
      let v2 = SQL.select1 Student S_all
          (fun r -> r.s_id=loop_var_1.r_s_id) in
      ()
    end

(*TXN 7*)
let increase_capacity_txn (input_threshold:int) =
  let v1 = SQL.select College C_all
      (fun r -> r.co_stcount > input_threshold) in
  SQL.foreach v1
    begin fun loop_var_1 ->
      let v2 = SQL.select  Course C_all
          (fun r -> r.c_coid=loop_var_1.co_id) in
      SQL.foreach v2
      begin fun loop_var_2 ->
        SQL.update Course
        (*do:*)    (fun u -> begin u.c_capacity <- loop_var_2.c_capacity+10; end)    
        (*where:*) (fun u -> u.c_id = loop_var_2.c_id);
        end
      end


(*TXN 7*)
let expel_student_txn (input_threshold:int) =
  let v1 = SQL.select Student S_all
      (fun r -> 1=1) in
  SQL.foreach v1
    begin fun loop_var_1 ->
      let v2 = SQL.select_count Transcript T_all
          (fun r -> r.t_s_id = loop_var_1.s_id && r.t_grade < input_threshold) in
      if v2 > 10
      then SQL.delete Student (fun r -> r.s_id=loop_var_1.s_id)
      else ()
      
      end

(*TXN 8*)
let enter_grade_txn (input_s_id:int)(input_i_id:int)(input_c_id:int)(input_grade:int) =
  SQL.insert Transcript  {t_s_id=input_s_id; t_c_id=input_c_id; t_grade=input_grade; t_i_id=input_i_id}




























open Typedtree
open Speclang



(*----------------------------------------------------------------------------------------------------*)
let printf = Printf.printf
let print_txn_name (Speclang.Fun.T app) = print_string app.name.name
let print_ident : Ident.t -> unit = fun ident -> print_string ident.name


module FOL = 
struct
  type t = T of {name_l: string; name_r: string}
  let left  (T{name_l;name_r}) = name_l
  let right (T{name_l;name_r}) = name_r
  let make ~name_l ~name_r = T{name_l=name_l;name_r=name_r}
end


(*----------------------------------------------------------------------------------------------------*)
module Statement =
struct
	type stmt_type = SELECT | UPDATE | INSERT | DELETE
  type t = T of {stmt_tp: stmt_type;
								 acc_table: string;
								 acc_fields: string list;
								 phi: FOL.t;
								 psi: FOL.t}
	let make ~stmt_tp ~acc_table ~acc_fields ~phi ~psi = 
		T {stmt_tp=stmt_tp; acc_table=acc_table; acc_fields=acc_fields; phi=phi; psi=psi}
  
  let get_type (T{stmt_tp;}) = stmt_tp
  let get_table(T{acc_table})=acc_table
  
  let make_empty =
    T {stmt_tp=SELECT; acc_table="Empty Table"; acc_fields=["empty filed"]; phi=(FOL.T{name_l="empty";name_r="empty"}); psi=(FOL.T{name_l="empty";name_r="empty"})}


  let print (T{stmt_tp;acc_table}) = match stmt_tp with
    | SELECT -> printf " SELECT";
								printf "(%s)" (acc_table);
		| UPDATE -> printf " UPDATE";
								printf "(%s)"  (acc_table);
end



(*----------------------------------------------------------------------------------------------------*)
module Transaction = 
struct
  type t = T of {name: string;
                 stmts: (Statement.t) list}
  let make ~name ~stmts = T {name=name; stmts=stmts}
	let print (T{name;stmts}) = List.iter (fun st -> printf "op: "; Statement.print st; printf "\n") (List.rev stmts)
  let name (T{name}) = name
  let stmts (T{stmts}) = stmts
end



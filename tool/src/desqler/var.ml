module Type =
struct
 	type t =
    | Int
    | Bool
    | String
    | List of t

  let rec to_string tp =
    match tp with
    |Int -> "Int" |String -> "String" |Bool -> "Bool"
    |List x -> "List of "^(to_string x)

end


module Table = 
struct
  type col = (string*string*Type.t*bool) (*table name, column name, type, is pk*)
  type t = T of {name: string; cols: col list}
  let name (T{name}) = name
  let cols (T{cols}) = cols
  let make ~name ~cols = T {name; cols}
end


module Variable = 
struct
  type kind = PARAM | LOCAL | FIELD  | RECORD
  type t = T of {name: string;field: string; table: string option; tp: Type.t; kn: kind}
  let make ~name ~field ~table ~tp ~kn = T{name; field; table; tp; kn}
  let name (T{name}) = name
  let table (T{table}) = match table with Some t -> t | None -> ""
  let field (T{field}) = field
  let kind (T{kn}) = kn
  let test_var = make "acc_dst" "" None Type.Int LOCAL
  let test_field = make "b_id" "" None Type.Int FIELD
  let test_param = make "src_id" "" None Type.Int PARAM
  let kind_to_string = fun x -> match x with PARAM -> "PARAM" | LOCAL -> "LOCAL" | RECORD -> "RECORD" | FIELD -> "FIELD"
end

let my_col:Table.col = ("test_table","test_col", Type.Int ,true) 



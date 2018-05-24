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
  type kind = PARAM | LOCAL | FIELD
  type t = T of {name: string; tp: Type.t; kn: kind}
  let make ~name ~tp ~kn = T{name; tp; kn}
  let name (T{name}) = name
  let test_var = make "acc_dst" Type.Int LOCAL
  let test_field = make "b_id" Type.Int FIELD
  let test_param = make "src_id" Type.Int PARAM
end

let my_col:Table.col = ("test_table","test_col", Type.Int ,true) 



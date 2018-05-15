module Type =
struct
 	type t =
    | Int
    | Bool
    | String
  let to_string tp =
    match tp with
    |Int -> "Int" |String -> "String" |Bool -> "Bool"

end


module Table = 
struct
  type col = (string*Type.t*bool)
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
  let test_var = make "test_var" Type.Int FIELD
end

let my_col:Table.col = ("test_col", Type.Int ,true) 



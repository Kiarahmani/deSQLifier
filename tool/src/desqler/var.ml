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
  type col = (string*Type.t)
  type t = T of {name: string; cols: col list}
  let name (T{name}) = name
  let cols (T{cols}) = cols
  let make ~name ~cols = T {name; cols}
end


module Variable = 
struct
  type k = PARAM | LCOAL | FIELD
  type t = T of {name: string; tp: Type.t; kind: k}
end


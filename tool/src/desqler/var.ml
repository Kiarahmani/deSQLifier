module Type =
struct
 	type _ t =
    | Int: int t
    | Bool: bool t
    | String: string t
	type some_type = SomeType: 'a t -> some_type
end


module Table = 
struct
  type col = string
  type t = T of {name: string; cols: col list}
  let name (T{name}) = name
end



module Variable = 
struct
  type k = PARAM | LCOAL | FIELD
  type t = T of {name: string; tp: Type.some_type; kind: k}
end


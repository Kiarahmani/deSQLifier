open Typedtree
open Speclang

module Coltype = 
struct
  type t = String | Int | Bool 
  let rec to_string = function
    | String -> "string" | Int -> "int" | Bool -> "bool"
end


module Tableschema = 
struct
  type t = T of {name: string;
                 cols: (string * some_type * bool) list}
  let make ~name ~cols = T {name=name; cols=cols}
  let print (T{name;cols}) = 
    let cols = List.map (fun (col_n,SomeType col_t,col_pk) -> 
                           if (col_pk)
                           then col_n^":"^(Type.to_string col_t)^"(ᴩᴋ)"
                           else col_n^":"^(Type.to_string col_t)) cols in
    begin
      Printf.printf "Table %s:\n  {%s}\n" name @@
        String.concat ", " cols
    end

  let name (T{name}) = name
  let cols (T{cols}) = cols
end




type t = T of {schemas: Tableschema.t list;
               txns: Fun.t list}

let make ~schemas ~txns = T {schemas; txns}

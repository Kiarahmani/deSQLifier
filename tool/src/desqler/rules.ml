open App
open Sql
open EncodeIR
open Speclang
module M = Misc

(*----------------------------------------------------------------------------------------------------*)
module Rule =
struct
  type rule_type = WR_Update_Select | RW_Update_Select



end
(*----------------------------------------------------------------------------------------------------*)
  type t = T of {name: Rule.rule_type}
  let make ~name  = T {name=name}
  let name (T{name}) = name
  let to_string (T{name}) = match name with 
                            |WR_Update_Select -> "ᴡʀ-ᴜᴩᴅᴀᴛᴇ-ꜱᴇʟᴇᴄᴛ"
                            |RW_Update_Select -> "ʀᴡ-ᴜᴩᴅᴀᴛᴇ-ꜱᴇʟᴇᴄᴛ"
                            | _ -> "ᴜɴᴋɴᴏᴡɴ ʀᴜʟᴇ"
  

  let apply = print_string "applying the rules..."

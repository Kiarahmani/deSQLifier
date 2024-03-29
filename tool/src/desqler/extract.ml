open Types
open Typedtree
open App
open Utils
open Speclang
module M = Misc


(* 
 * Extract table names (from table_name type). 
 *)
let extract_ttype_names (str_items) : string list = 
  let open Asttypes in 
  let doIt_cons_decl {cd_name} = String.lowercase_ascii cd_name.txt in
  let doIt_item_desc = function 
    | Tstr_type (Recursive, 
                 [{typ_name={txt="table_name"};
                   typ_kind=Ttype_variant cons_decls}]) ->
          List.map doIt_cons_decl cons_decls
    | _ -> [] in
      List.concat @@ 
        List.map (fun item -> 
                    doIt_item_desc item.str_desc) str_items
(*
 * Extract table schemas
 *)
let extract_table_schemas ttype_names str_items 
    : Tableschema.t list = 
  let open Asttypes in
  let rec doIt_core_type_desc (ctyp_desc) : some_type = 
    match ctyp_desc with
      | Ttyp_constr (path,longident,_) -> 
          begin
          match longident with
          | x -> 
          let path_str = Printtyp.string_of_path path in
          let some t = SomeType t in
            begin
              match path_str with 
                | "string" -> some @@ Type.String 
                | "int" -> some @@ Type.Int
                | "bool" -> some @@ Type.Bool
                | _ -> failwith "doIt_core_type_desc: Unimpl."
              end
          end

      | Ttyp_poly (_,core_t) -> doIt_core_type_desc core_t.ctyp_desc
      | _ -> failwith "doIt_core_type_desc: Unimpl." in
  let doIt_label_dec ({ld_name; ld_type = {ctyp_desc};ld_mutable}) 
        : (string*some_type*bool) = 
    let col_name = ld_name.txt in
    let col_pk = 
      begin
      match ld_mutable with
        |Immutable -> true
        |Mutable -> false
      end in 
    let col_t = doIt_core_type_desc ctyp_desc in
       (col_name,col_t,col_pk) in
  let doIt_item_desc = function 
    | Tstr_type (Recursive, 
                 [{typ_name={txt};
                   typ_kind=Ttype_record label_decs}]) 
      when (List.mem txt ttype_names) ->
          [Tableschema.make ~name:txt 
             ~cols:(List.map doIt_label_dec label_decs)]
    | _ -> [] in
      List.concat @@ 
        List.map (fun item -> 
                    doIt_item_desc item.str_desc) str_items
(*
 * Extract transactions
 *)

let extract_txns (str_items) = 
  let txns  = ref []  in
  let open Asttypes in
  let doIt_valbind rec_flag {vb_pat; vb_expr} = 
    match (vb_pat.pat_desc, vb_expr.exp_desc) with 
      | (Tpat_var (_,loc), Texp_function (_,[case],_)) -> 
          let mk_fun () = 
            let (args,body) = Astutils.extract_lambda case in
            let open Types in
            let arrow_t = vb_expr.exp_type.desc in
            let (arg_ts,res_t) = Astutils.uncurry_arrow arrow_t in
              Fun.make ~name: (Ident.create loc.txt) 
                       ~rec_flag: rec_flag
                       ~args_t: (List.zip args arg_ts) 
                       ~res_t: res_t ~body: body in
            if String.length loc.txt >= 4 && Str.last_chars loc.txt 4 = "_txn" 
            then txns:= (mk_fun ())::!txns
     
      
      | _ -> () in
    begin
      List.iter (fun {str_desc} -> match str_desc with
                   | Tstr_value (rec_flag,valbinds) -> 
                       let open Asttypes in 
                       let rec_flag = match rec_flag with 
                         | Nonrecursive -> false
                         | Recursive -> true in
                         List.iter (doIt_valbind rec_flag) valbinds
                   | _ -> ()) str_items;
      !txns
    end

let doIt ppf ({str_items; str_type; str_final_env}) = 
 let ttype_names = extract_ttype_names str_items in
  let _ = Printf.printf "\nTable names\n-----------\n     %s\n\n" @@  String.concat "," ttype_names in
  let _ = print_string "\nTable Schemas\n-------------\n" in
  let table_schemas = extract_table_schemas ttype_names str_items in
  let _ = List.iter Tableschema.print table_schemas in
  let txns  = extract_txns str_items in
  let print_fname fun_t = Printf.printf "     %s\n" @@ Ident.name @@  Fun.name fun_t in
  let app = App.make ~schemas: table_schemas ~txns:txns in
    begin
      print_string "\n\n";
      app
    end


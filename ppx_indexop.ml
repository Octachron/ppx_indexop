open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree

let make_module loc name items =
  items
  |>  Mod.structure ~loc 
  |>  Mb.mk ~loc {txt=name;loc}
  |> Str.module_  ~loc 

let singleton x = [x]

let translate_to_indexop = function
  | "get_par" -> ".()"  | "set_par" -> ".()<-"
  | "get_sq" -> ".[]"  | "set_sq" ->".[]<-"    
  | "get" | "get1" -> ".{}"
  | "set" | "set1" -> ".{}<-"
  | "get2" -> ".{,}"    | "set2" -> ".{,}<-"
  | "get3" -> ".{,,}"   | "set3" -> ".{,,}<-"
  | "getn" -> ".{,..,}" | "setn" -> ".{,..,}<-"
  | _ -> assert false
					 

let with_binding f = function
  | {pvb_pat={ ppat_desc= Ppat_var var ; ppat_loc; _ } as pr   ; _ } as b -> f b pr var
  | _ -> assert false

let rewrite_binding b pr {loc;txt} =
     let pvb_pat = { pr with ppat_desc = Ppat_var {loc; txt = translate_to_indexop txt}  } in 
     { b with pvb_pat }
		
let duplicate_unsafe b pr ({loc;txt} as sloc ) = sloc,
     let pvb_pat = { pr with ppat_desc = Ppat_var {loc; txt = "unsafe_" ^ txt}  } in 
     { b with pvb_pat }

let encapsulate name loc pstr =
  let bigarray m = make_module loc "Bigarray" [m] in
  match name with
  | "get_par" | "set_par" -> pstr |> make_module loc "Array"
  | "get_sq"  | "set_sq" -> pstr |> make_module loc "String"
  | "get" | "get1" | "set" | "set1" -> pstr |> make_module loc "Array1" |> bigarray
  | "get2" | "set2" -> pstr |> make_module loc "Array2" |> bigarray			       
  | "get3" | "set3" -> pstr |> make_module loc "Array3" |> bigarray
  | "getn" | "setn" -> pstr |> make_module loc "Genarray" |> bigarray
  | _ -> assert false


type version = { major:int; minor:int }
let ( <% ) {major;minor} v = if major < v.major then true else minor < v.minor 
						 
let impl = {major=4; minor=3}
let ocaml_version =
  let s = Sys.ocaml_version in
  let dot1 = String.index s '.' in
  let dot2 = String.index_from s (dot1+1) '.' in
  let major = int_of_string @@ String.sub s 0 dot1  in
  let minor = int_of_string @@ String.sub s (succ dot1) (dot2-dot1-1) in
  {major;minor}
			  								 
let rewrite_str_item = function
  | { pstr_loc; pstr_desc= Pstr_value (rec_flag, [binding] )  } as str_item ->
     if ocaml_version <% impl then
       let {txt;loc}, bind_unsafe = with_binding duplicate_unsafe binding in
       encapsulate txt loc [str_item; { str_item with pstr_desc= Pstr_value(rec_flag,[bind_unsafe]) } ] 
     else
     let binding =  binding |> with_binding rewrite_binding in 
     {pstr_loc; pstr_desc = Pstr_value(rec_flag, [binding])}  
  | _ -> assert false 					       							       

let rewrite_str  = function
  | [str_item] -> rewrite_str_item str_item
  | _ -> assert false 
				      
let indexop_mapper argv =  {
  default_mapper with
  structure_item =(
    fun mapper -> function
	       | { pstr_desc = Pstr_extension ( ({txt="indexop";loc}, PStr pstr) , l  ) } -> rewrite_str pstr
	       | x -> default_mapper.structure_item mapper x
)
}

let () = register "indexop" indexop_mapper
  

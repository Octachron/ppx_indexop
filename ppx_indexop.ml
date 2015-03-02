open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree

let make_module loc name items =
  items
  |>  Mod.structure ~loc 
  |>  Mb.mk ~loc {txt=name;loc}
  |> Str.module_  ~loc 

type array_kind = Array | String | Bigarray
type arity = Finite of int | Arbitrary
type operator_kind  = Set | Get
type array_type = { typ : array_kind; dim : arity }
type operator = {kind:operator_kind; arity: arity}
let mk_op kind arity = {kind;arity}

module ArityMap = struct
  include( Map.Make(struct type t=arity let compare=compare end) )
  let (<+) map (x,y) =
    let l = try find x map with Not_found -> [] in 
    add x (y@l) map	 
end
			
			 
let ( !! ) n = Finite n

let rec ( @* ) s = function
  | 1 -> s
  | 0 -> ""
  | n when n>0 -> s ^ ( s  @* (n-1) )
  | _ -> ""
			       
let translate_arity = function
  | Finite n -> "," @* (n-1)
  | Arbitrary -> ",..,"
			 
let translate_kind n = function
  | Array -> ".()"
  | String -> ".[]"
  | Bigarray -> ".{" ^ translate_arity n ^ "}"

let scan_operator = function
  | "get" | "get1" -> mk_op Get (!!1)
  | "set" | "set1" -> mk_op Set (!!1)
  | "get2" -> mk_op Get ( !!2 )
  | "set2" -> mk_op Set ( !!2 )
  | "get3" -> mk_op Get ( !!3 )
  | "set3" -> mk_op Set ( !! 3 )
  | "getn" -> mk_op Get Arbitrary
  | "setn" -> mk_op Set Arbitrary
  | _ -> assert false

let translate_indexop kind op_str =
  let op = scan_operator op_str in
  let n = op.arity in
  let base_name = translate_kind n kind in
  match op.kind with
  | Get -> base_name
  | Set -> base_name ^ "<-"

			 
let opkind_to_str  = function
  | Get -> "get"
  | Set -> "set"	 

let with_binding f = function
  | {pvb_pat={ ppat_desc= Ppat_var var ; ppat_loc; _ } as pr   ; _ } as b -> f b pr var
  | _ -> assert false

let rewrite_binding rewriter b pr {loc;txt} =
     let pvb_pat = { pr with ppat_desc = Ppat_var {loc; txt = rewriter txt}  } in 
     { b with pvb_pat }

let register_binding  m b pr sloc =
  let op = scan_operator sloc.txt in
  let name = opkind_to_str op.kind in
  let b = rewrite_binding (fun _ -> name)  b pr sloc in
  let b' = rewrite_binding (fun _ -> "unsafe_" ^ name ) b pr sloc in
  ArityMap.( m <+ (op.arity, [b;b']) )
 
let duplicate_unsafe b pr {loc;txt} =
     let pvb_pat = { pr with ppat_desc = Ppat_var {loc; txt = "unsafe_" ^ txt}  } in 
     { b with pvb_pat }

let kind_to_string = function
  | Array -> "Array"
  | String -> "String"
  | Bigarray -> "Bigarray"
       
let encapsulate_simple kind loc pstr =
  pstr |> make_module loc (kind_to_string kind)

let bigarray_submodule = function
  | Finite 1 -> "Array1"
  | Finite 2 -> "Array2"
  | Finite 3 -> "Array3"
  | Arbitrary -> "Genarray"
  | _ -> assert false
		      
let encapsulate_bigarray loc updater binding_map =
  let add_submodule arity bindings acc =
    let pstr = updater bindings in
    let sub  = make_module pstr.pstr_loc (bigarray_submodule arity) [pstr] in
    sub::acc in
  let submodules = ArityMap.( fold add_submodule binding_map [] ) in
  make_module loc "Bigarray" submodules
		

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

let update_binding str_item rec_flag  b =
  { str_item with pstr_desc = Pstr_value(rec_flag, b ) }

let rewrite_str_ante kind updater bindings=
  let full_bindings = List.fold_left ( fun l x ->  (with_binding duplicate_unsafe x)::l ) bindings bindings in
  let str_item = updater full_bindings in
  encapsulate_simple kind str_item.pstr_loc [ str_item ]
  

let rewrite_str_bigarray kind loc updater bindings=
  let arity_map = ArityMap.empty in
  let folder arity_map b = with_binding (register_binding arity_map) b in
  let arity_map = List.fold_left folder arity_map bindings in
  encapsulate_bigarray loc updater arity_map
			  
let rewrite_str_item kind = function
  | { pstr_loc; pstr_desc= Pstr_value (rec_flag, bindings )  } as str_item ->
     let updater = update_binding str_item rec_flag in
     if ocaml_version <% impl then
       match kind with
       | Bigarray -> rewrite_str_bigarray kind pstr_loc updater bindings
       | s -> rewrite_str_ante kind updater bindings 
     else
     let bindings=  List.map ( with_binding ( rewrite_binding @@ translate_indexop kind ) ) bindings in 
     {pstr_loc; pstr_desc = Pstr_value(rec_flag, bindings)}  
  | _ -> assert false 					       							       

let rewrite_str kind  = function
  | [str_item] -> rewrite_str_item kind str_item
  | _ -> assert false 
				      
let indexop_mapper argv =  {
  default_mapper with
  structure_item =(
    fun mapper -> function
	       | { pstr_desc = Pstr_extension ( ({txt="indexop";loc}, PStr pstr) , l  ) } -> rewrite_str Bigarray pstr
	       | { pstr_desc = Pstr_extension ( ({txt="indexop.arraylike";loc}, PStr pstr) , l  ) } -> rewrite_str Array pstr
	       | { pstr_desc = Pstr_extension ( ({txt="indexop.stringlike";loc}, PStr pstr) , l  ) } -> rewrite_str String pstr
	       | x -> default_mapper.structure_item mapper x
)
}

let () = register "indexop" indexop_mapper
  

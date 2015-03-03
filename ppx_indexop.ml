open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree

module Opt = struct
  let (>>?) opt f = match opt with
    | Some x -> f x
    | None -> None

  let (>|?) opt f = match opt with
    | Some x -> Some (f x)
    | None -> None
end


	       
let extract_loc = function
  | a::q -> a.pstr_loc
  | _ -> assert false

type ('a,'b) result = Ok of 'a | Error of 'b

let error x = Error x
let ok x = Ok x

let (>>?) opt f = match opt with
  | Ok x -> f x
  | Error e -> Error e
		     
let (>|?) opt f = match opt with
  | Ok x -> Ok (f x)
  | Error e -> Error e				    




let ( ><? ) x f = match x with
  | Error x -> f x
  | Ok y -> Ok y

exception Indexop_error of Location.error
	       
let localize loc e = match e with
  | `Incorrect_structure_item ->
     raise @@ Indexop_error Location.{
       loc;
       msg = "Incorrect structure item in an indexop extension";
       sub=[];
       if_highlight = "This structure item is invalide inside an indexop extension"
     }
  | `Unknown_identifiant s -> raise @@ Indexop_error Location.{
				loc;
				msg = "Incorrect identifiant [" ^ s ^"] in an indexop extension";
				sub=[];
				if_highlight = "This identifiant is invalide inside an indexop extension"
			      }
  | `Incorrect_arity n -> raise @@ Indexop_error Location.{
			    loc;
			    msg = "Incorrect arity [" ^ string_of_int n  ^">3] in an indexop extension";
			    sub=[];
			    if_highlight = "This identifiant has a fixed arity (n>3), which is invalid inside an indexop extension"
			  }
 
			  
let ( ><! ) x loc = match x with
  | Error x -> localize loc x
  | Ok y -> y


		       
		
let make_module name items =
  let loc = extract_loc items in 
  items
  |>  Mod.structure ~loc 
  |>  Mb.mk ~loc {txt=name;loc}
  |> Str.module_  ~loc 

type array_kind = Array | String | Bigarray
type arity = Finite of int | Arbitrary
type operator_kind  = Set | Get
type array_type = { typ : array_kind; dim : arity }
type operator = {kind:operator_kind; arity: arity}

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

					     
let mk_op kind arity = {kind;arity}
let scan_operator = function
  | "get" | "get1" -> ok @@ mk_op Get (!!1)
  | "set" | "set1" -> ok @@ mk_op Set (!!1)
  | "get2" -> ok @@ mk_op Get ( !!2 )
  | "set2" -> ok @@ mk_op Set ( !!2 )
  | "get3" -> ok @@ mk_op Get ( !!3 )
  | "set3" -> ok @@ mk_op Set ( !! 3 )
  | "getn" -> ok @@ mk_op Get Arbitrary
  | "setn" -> ok @@ mk_op Set Arbitrary
  | s -> error @@ `Unknown_identifiant s

let translate_indexop kind op_str =
  scan_operator op_str >|? fun op -> 
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
  | {pvb_loc; _}  -> localize pvb_loc `Incorrect_structure_item  

let rewrite_binding rewriter b pr {loc;txt} =
  let txt = rewriter txt ><! loc in
     let pvb_pat = { pr with ppat_desc = Ppat_var {loc; txt}  } in 
     { b with pvb_pat }
		       

let register_binding  m b pr sloc =
  let op = scan_operator sloc.txt ><! sloc.loc in 
  let name = opkind_to_str op.kind in
  let b' = rewrite_binding (fun _ -> ok name) b pr sloc in 
  let b'' = rewrite_binding (fun _ -> ok @@ "unsafe_" ^ name ) b pr sloc in
  ArityMap.( m <+ (op.arity, [b';b'']) )
 
let duplicate_unsafe b pr {loc;txt} =
     let pvb_pat = { pr with ppat_desc = Ppat_var {loc; txt = "unsafe_" ^ txt}  } in 
     { b with pvb_pat }

let kind_to_string = function
  | Array -> "Array"
  | String -> "String"
  | Bigarray -> "Bigarray"
       
let encapsulate_simple kind pstr =
  make_module (kind_to_string kind) pstr

let bigarray_submodule = function
  | Finite 1 -> ok @@ "Array1"
  | Finite 2 -> ok @@ "Array2"
  | Finite 3 -> ok @@ "Array3"
  | Arbitrary -> ok @@ "Genarray"
  | Finite k -> error @@ `Incorrect_arity k  


let encapsulate_bigarray str_map =
  let add_submodule arity pstr acc =
    let loc = extract_loc pstr in
    let sub_typ = bigarray_submodule arity ><! loc in
    let sub = make_module sub_typ pstr in
    sub::acc in
  ArityMap.fold add_submodule str_map ([])
  |>  make_module "Bigarray"
		

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


let split_str =  function
  | { pstr_loc; pstr_desc= Pstr_value (rec_flag, bindings )  } as str_item ->
     (update_binding str_item rec_flag, bindings )
  | {pstr_loc; _} -> localize pstr_loc `Incorrect_structure_item
     
    
let rewrite_str_item_ante kind str_item=
  let updater, bindings = split_str str_item in
  let full_bindings = List.fold_left ( fun l x -> (with_binding duplicate_unsafe x)::l  ) (bindings) bindings in
  let str_item = updater full_bindings in
  str_item

let map_with_errors f l =
  let rec map acc = function
  | a::q -> f a >>? fun x -> map (x::acc) q
  | [] -> ok [] in
  map [] l
    
let rewrite_str_ante kind str =
  str
  |> List.map (rewrite_str_item_ante kind)
  |> encapsulate_simple kind

let fold_with_errors f start l =
  let rec fold acc l=
    match l with
    | a::q -> f acc a >>? fun acc -> fold acc q
    | [] -> ok acc in
  fold start l

let rewrite_str_item_bigarray str_map str_item=
  let updater, bindings = split_str str_item in 
  let folder binding_map b = with_binding (register_binding binding_map) b in
  let folder' arity item str_map  =  ArityMap.( str_map <+ (arity,[item]) ) in
  bindings
  |> List.fold_left folder ArityMap.empty 
  |> ArityMap.map updater
  |> fun binding_map -> 
     ArityMap.fold folder' binding_map str_map
		  
		
let rewrite_str_bigarray str =
  str
  |> List.fold_left rewrite_str_item_bigarray ArityMap.empty 
  |> encapsulate_bigarray

let rewrite_str_post kind str=
  let rewrite_item str_item =
    let updater, bindings = split_str str_item in
    bindings
    |> List.map (with_binding (rewrite_binding @@ translate_indexop kind) )
    |> updater
  in
  List.map rewrite_item str


let catch_error str f =
  try f str with
  | Indexop_error e -> { pstr_desc = Pstr_extension (extension_of_error e, []); pstr_loc = e.Location.loc  }::str
	   
	   
let select kind str global_str =
  if ocaml_version <% impl then
    match kind with
    | Bigarray -> (rewrite_str_bigarray str)::global_str 
    | kind -> (rewrite_str_ante kind str)::global_str 
  else
    (rewrite_str_post kind str) @ global_str

				    

let structure_fold mapper str = function
  | { pstr_desc = Pstr_extension ( ({txt="indexop";loc}, PStr pstr) , l  ) } ->  catch_error str @@ select Bigarray pstr
  | { pstr_desc = Pstr_extension ( ({txt="indexop.arraylike";loc}, PStr pstr) , l  ) } -> catch_error str @@ select Array pstr
  | { pstr_desc = Pstr_extension ( ({txt="indexop.stringlike";loc}, PStr pstr) , l  ) } -> catch_error str @@ select String pstr
  | x -> (default_mapper.structure_item mapper x)::str		     
			      
let indexop_mapper argv =  {
  default_mapper with
  structure = (fun mapper str ->
	       str
	       |> List.fold_left (structure_fold mapper) []
	       |> List.rev
	 )
}

let () = register "indexop" indexop_mapper
  

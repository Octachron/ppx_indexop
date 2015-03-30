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

  let (><) opt default = match opt with
    | None -> default
    | Some x -> x
end


(*
let extract_loc = function
  | a::q -> a.pstr_loc
  | _ -> assert false

let extract_loc_sig = function
  | a::q -> a.psig_loc
  | _ -> assert false
 *)

type ('a,'b) result = Ok of 'a | Error of 'b

let error x = Error x
let ok x = Ok x

let (>>?) opt f = match opt with
  | Ok x -> f x
  | Error e -> Error e
		     
let (>|?) opt f = match opt with
  | Ok x -> Ok (f x)
  | Error e -> Error e				    

let hd_opt = function
  | [] -> None
  | a::q -> Some a


let ( ><? ) x f = match x with
  | Error x -> f x
  | Ok y -> Ok y


let map_with_errors f l =
  let rec map acc = function
    | a::q -> f a >>? fun x -> map (x::acc) q
    | [] -> ok [] in
  map [] l

let fold_with_errors f start l =
  let rec fold acc l=
    match l with
    | a::q -> f acc a >>? fun acc -> fold acc q
    | [] -> ok acc in
  fold start l

exception Indexop_error of Location.error
	       
let localize loc e =
  let open Location in
  match e with
  | `Incorrect_structure_item ->
     raise @@  Location.Error {
       loc;
       msg = "Incorrect structure item in an indexop extension";
       sub=[];
       if_highlight = "This structure item is invalide inside an indexop extension"
		 }
  | `Incorrect_sig_item -> raise @@  Location.Error {
       loc;
       msg = "Incorrect signature value with an indexop attribute ";
       sub=[];
       if_highlight = "This signature value can not be combined with an indexop attribute"
		 } 
  | `Unknown_identifiant s -> raise @@ Location.Error{
				loc;
				msg = "Incorrect identifiant [" ^ s ^"] in an indexop extension";
				sub=[];
				if_highlight = "This identifiant is invalide inside an indexop extension"
			      }
  | `Incorrect_arity n -> raise @@  Location.Error {
			    loc;
			    msg = "Incorrect arity [" ^ string_of_int n  ^">3] in an indexop extension";
			    sub=[];
			    if_highlight = "This identifiant has a fixed arity (n>3), which is invalid inside an indexop extension"
			  }
 
			  
let ( ><! ) x loc = match x with
  | Error x -> localize loc x
  | Ok y -> y


		       
		
let make_module name items =
  let open Opt in
  hd_opt items >|? fun item -> 
  let loc = item.pstr_loc in 
  items
  |> Mod.structure ~loc 
  |> Mb.mk ~loc {txt=name;loc}
  |> Str.module_  ~loc 

let make_module_sig name items =
  let open Opt in
  items |> hd_opt >|? fun item ->
  let loc = item.psig_loc in 
  Pmty_signature items
  |> Mty.mk ~loc 
  |> Md.mk ~loc {txt=name;loc}
  |> Sig.module_  ~loc 

		  
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

module Sig_map = struct
  include( Map.Make(struct type t=array_type let compare=compare end) )
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

let trust_me = function
  | Ok x -> x
  | Error x -> assert false
					     
let mk_op kind arity = {kind;arity}
let scan_operator { txt; loc }  = match txt with 
  |  "get" | "get_1"  -> mk_op Get (!!1)
  | "set" | "set_1" -> mk_op Set (!!1)
  | "get_2" ->  mk_op Get ( !!2 )
  | "set_2" ->  mk_op Set ( !!2 )
  | "get_3" ->  mk_op Get ( !!3 )
  | "set_3" ->  mk_op Set ( !! 3 )
  | "get_n" ->  mk_op Get Arbitrary
  | "set_n" ->  mk_op Set Arbitrary
  | s -> localize loc @@ `Unknown_identifiant s

let translate_indexop kind op_name =
  let op = scan_operator op_name in 
  let n = op.arity in
  let base_name = translate_kind n kind in
  match op.kind with
  | Get -> base_name
  | Set -> base_name ^ "<-"

			 
let opkind_to_str  = function
  | Get -> "get"
  | Set -> "set"

let op_to_str op = opkind_to_str op.kind

let with_binding f ( {pvb_pat;pvb_loc;_ } as b )  = 
  match pvb_pat.ppat_desc with
  | Ppat_var var -> 
     let updater var' = { b with pvb_pat = { pvb_pat with ppat_desc = Ppat_var var' } } in f updater var
  | Ppat_constraint ( { ppat_desc = Ppat_var var; _ } as inner , ty ) ->
     let updater var' =
       let ppat_desc = Ppat_constraint( { inner with ppat_desc = Ppat_var var' } , ty ) in 
       { b with pvb_pat = { pvb_pat with ppat_desc } } in f updater var
  | _ -> localize pvb_loc `Incorrect_structure_item 	   

let rewrite_sig f s =
  let sn = s.pval_name in
  { s with pval_name = { sn with txt = f sn } }  

let rewrite_binding rewriter updater sloc =
  let txt = rewriter sloc in
  updater { txt; loc = sloc.loc } 
		       

let register_binding  m updater sloc =
  let op = scan_operator sloc in 
  let name = opkind_to_str op.kind in
  let b' = rewrite_binding  (fun _ -> name) updater sloc in 
  let b'' = rewrite_binding (fun _ ->  "unsafe_" ^ name ) updater sloc in
  ArityMap.( m <+ (op.arity, [b';b'']) )
 
let duplicate_unsafe updater {loc;txt} =
     updater {loc; txt = "unsafe_" ^ txt}

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

let (@?) opt l = match opt with
  | Some x -> x::l
  | None -> l
			  
let encapsulate_bigarray make str_map =
  let add_submodule arity pstr acc =
    match pstr with
    | [] -> acc
    | item::items -> 
       let loc = item.pstr_loc in
       let sub_typ = bigarray_submodule arity ><! loc in
       (make sub_typ pstr) @? acc in
  ArityMap.fold add_submodule str_map ([])
  |>  make "Bigarray"
		

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

let update_sig_val sig_item val_desc =
  { sig_item with psig_desc = Psig_value val_desc }

let split_sig = function
  | { psig_loc; psig_desc = Psig_value val_desc  } as sig_item -> update_sig_val sig_item, val_desc
  | {psig_loc; _ } -> localize psig_loc `Incorrect_sig_item
    
let split_str =  function
  | { pstr_loc; pstr_desc= Pstr_value (rec_flag, bindings )  } as str_item ->
     (update_binding str_item rec_flag, bindings )
  | {pstr_loc; _} -> localize pstr_loc `Incorrect_structure_item

    
let rewrite_str_item_ante kind str_item=
  let updater, bindings = split_str str_item in
  let full_bindings = List.fold_left ( fun l x -> (with_binding duplicate_unsafe x)::l  ) (bindings) bindings in
  let str_item = updater full_bindings in
  str_item


let rewrite_str_ante kind str =
  str
  |> List.map (rewrite_str_item_ante kind)
  |> encapsulate_simple kind

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
  |> encapsulate_bigarray make_module

let rewrite_str_post kind str=
  let rewrite_item str_item =
    let updater, bindings = split_str str_item in
    bindings
    |> List.map (with_binding @@ rewrite_binding @@ translate_indexop kind )
    |> updater
  in
  List.map rewrite_item str

	   
let select kind str global_str =
  if ocaml_version <% impl then
    match kind with
    | Bigarray -> (rewrite_str_bigarray str) @? global_str 
    | kind -> (rewrite_str_ante kind str) @? global_str 
  else
    (rewrite_str_post kind str) @ global_str

let extension_type = function
  | "indexop"|"indexop.bigarraylike" -> Some Bigarray
  | "indexop.arraylike" -> Some Array
  | "indexop.stringlike" -> Some String
  | txt -> None    

let rec find_attribute = function
    | (name, PStr [])::q -> ( match extension_type name.txt with Some x -> Some x | None ->  find_attribute q )  
    | a::q -> find_attribute q
    | [] -> None
		 
let structure_fold mapper str = function
  | { pstr_desc = Pstr_extension ( ({txt;loc}, PStr pstr) , l  ) } as x ->
     begin  match extension_type txt with
	    | Some typ -> select typ pstr str
	    | None ->  x::str
     end
  | x -> (default_mapper.structure_item mapper x)::str		     


let ( |>| ) f g x = g ( f x )
						     
let extend_sig sig_val =
  let updater, s_op = split_sig sig_val in
  let name = scan_operator |>| op_to_str in
  let op = rewrite_sig name s_op  in
  let op' = rewrite_sig (fun n -> "unsafe_" ^ name n) s_op in
  [ updater op; updater op' ]								   
  

let signature_destruct mapper (indexop_sign, signature)= function
  | {psig_desc= Psig_value sig_val  ; psig_loc } as sig_item ->
     begin
       match find_attribute sig_val.pval_attributes with
       | Some typ -> let sig_op = scan_operator sig_val.pval_name in Sig_map.( indexop_sign <+ ( { typ; dim=sig_op.arity }, extend_sig sig_item) ) , signature 
       | None -> indexop_sign, sig_item::signature
     end
  | x -> indexop_sign, (default_mapper.signature_item mapper x)::signature
								   
let recreate_sig ( op_map, l ) =
  let folder {typ;dim} signature (big_l,l) = match typ with
    | Array -> big_l, (make_module_sig "Array" signature) @? l
    | String -> big_l, (make_module_sig "String" signature) @? l
    | Bigarray -> let smod = trust_me @@ bigarray_submodule dim in
		  (make_module_sig smod signature) @? big_l, l in
  let big_l, l = Sig_map.fold folder op_map ([] ,l ) in
  List.rev @@ ( make_module_sig "Bigarray" big_l ) @? l 

let signature_rewrite_ante mapper sig_items =
  List.fold_left (signature_destruct mapper) (Sig_map.empty, [] ) sig_items
  |> recreate_sig



let signature_rewrite_post mapper signature =
  let map_f = function 
  | {psig_desc= Psig_value sig_val; psig_loc } as sig_item ->
     begin
       match find_attribute sig_val.pval_attributes with
       | Some typ -> let item = rewrite_sig (translate_indexop typ) sig_val  in { sig_item with psig_desc = Psig_value item } 
       | None ->  mapper.signature_item mapper sig_item
     end
  | x -> mapper.signature_item mapper x in
  List.map map_f signature

let signature_rewrite =
  if ocaml_version <% impl then
    signature_rewrite_ante
  else
    signature_rewrite_post
								   						   
let indexop_mapper argv =  {
  default_mapper with
  structure = (fun mapper str ->
	       str
	       |> List.fold_left (structure_fold mapper) []
	       |> List.rev
	      ) ;
  signature = signature_rewrite
}

let () = register "indexop" indexop_mapper
  

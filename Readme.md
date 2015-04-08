ppx_indexop is a simple ppx rewriter which provides an unified way to write custom access operators for array-like type for ocaml versions `≥4.02`.

For instance, bigarray-like operators (i.e., `.{}` and `.{}<-` ) can be defined using
```Ocaml
[%%indexop
let get t x = Hashtbl.find t x 
let set t x y = Hashtbl.add t x y
] (*or let%indexop get ... and set ... *) 
let h =Hashtbl.create 10
let () = h.{"first"}<-1 (* h.{x}<-y  is equivalent to set h x y *) 
let x = h.{"first"} (* h.{x} is equivalent to get h x *)
```

Array-like (`.()`) and string-like operators (`.[]`) can be customized using `[%%indexop.arraylike]` and `[%%indexop.stringlike]` extension respectively.
Bigarray multi-indices operators can be provided using `get_2`,`get_3` or `get_n` identifiants and the equivalent variants for `set`.
In signature, it is required to mark these special functions with an `[@@indexop]` attribute.
```Ocaml
val get : ('a,'b) Hastbl -> 'a -> 'b [@@indexop]
val set : ('a,'b) Hastbl -> 'a -> 'b -> unit [@@indexop]
```

In ocaml 4.02 mode, ppx_indexop has two majors limitations. First, index operator definitions mask the equivalent standard modules.
In other words,
```Ocaml
let%indexop.arraylike get a x = ...
and set a x y = ...
```
masks the Array module. Second, all the operators of a given type needs to be defined in the same extension node, e.g.
```
let%indexop get ...
let%indexop set ...
```
is invalid.

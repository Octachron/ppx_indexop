
let a = [| 0; 0 |];;

[%%indexop
 let get a n= a.(n)
 let set a n x  = a.(n) <- x
 and set_2 a n m x = a.(n*m) <- x
 let get_2 a n m = a.(n*m)
]

module Bigarray2= struct
  module Array1 = struct
    let get v x = ()
    end
end

let _ =
  a.{1}<-2;
  Printf.printf "%d\n" a.{1}
	     

(* These functions mimic runtime memory. It is untyped (i.e., always contains
   integers), just like real physical memory. However, in order to help help
   more easily debug errors, uninitialized reads will trigger a Not_found
   exception. *)

type storable = int;;
type location = int;;

(* Store provides two operations:

     read: provided using the function value_at: store -> location -> storable
     write: provided using insert_value: store -> location -> value -> store

   Note that in C-flat, you need to organize memory into two areas: static
   and stack. The static area is where all the global variables (i.e., variables
   delcared at the top-level) will go. You should use the lowest addresses
   in the store for static variables.

   All activation records will go on the stack. You can start the stack at
   the highest possible address, and the stack will grow down. 
*)

(* We implement store using an OCaml library that provides associative arrays *)
module IntMap = Map.Make(struct type t = int let compare = compare end);;
type store = int IntMap.t;;
let value_at store loc = IntMap.find loc store;;
let insert_value store loc v =  IntMap.add loc v store;;

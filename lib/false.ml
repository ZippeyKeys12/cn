open Pp

type t = False
(* [@@deriving eq, ord] *)

let subst _substitution = function False -> False

let free_vars = function False -> Sym.Set.empty

let pp = function False -> if !unicode then !^"\u{22A5}" else !^"false"

(* let dtree False = Cerb_frontend.Pp_ast.Dleaf !^"False" *)

module CF = Cerb_frontend
module A = CF.AilSyntax
module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module SymGraph = Graph.Persistent.Digraph.Concrete (Sym)
module StringMap = Map.Make (String)

type t =
  | Uniform of { bt : BT.t }
  | Pick of
      { bt : BT.t;
        choices : (Z.t * t) list
      }
  | Alloc
  | Call of
      { fsym : Sym.t;
        iargs : (Sym.t * Sym.t) list;
        oarg_bt : BT.t;
        sized : (int * Sym.t) option
      }
  | Asgn of
      { addr : IT.t;
        sct : Sctypes.t;
        value : IT.t;
        rest : t
      }
  | LetStar of
      { x : Sym.t;
        x_bt : BT.t;
        value : t;
        rest : t
      }
  | Return of { value : IT.t }
  | Assert of
      { prop : LC.t;
        rest : t
      }
  | ITE of
      { bt : BT.t;
        cond : IT.t;
        t : t;
        f : t
      }
  | Map of
      { i : Sym.t;
        bt : BT.t;
        perm : IT.t;
        inner : t
      }
  | SplitSize of
      { syms : Sym.Set.t;
        rest : t
      }
[@@deriving eq, ord]

let is_return (tm : t) : bool = match tm with Return _ -> true | _ -> false

let rec free_vars (tm : t) : Sym.Set.t =
  match tm with
  | Uniform _ | Alloc -> Sym.Set.empty
  | Pick { bt = _; choices } -> free_vars_list (List.map snd choices)
  | Call { fsym = _; iargs; oarg_bt = _; sized = _ } ->
    Sym.Set.of_list (List.map snd iargs)
  | Asgn { addr; sct = _; value; rest } ->
    Sym.Set.union (IT.free_vars_list [ addr; value ]) (free_vars rest)
  | LetStar { x; x_bt = _; value; rest } ->
    Sym.Set.union (free_vars value) (Sym.Set.remove x (free_vars rest))
  | Return { value } -> IT.free_vars value
  | Assert { prop; rest } -> Sym.Set.union (LC.free_vars prop) (free_vars rest)
  | ITE { bt = _; cond; t; f } ->
    Sym.Set.union (IT.free_vars cond) (free_vars_list [ t; f ])
  | Map { i; bt = _; perm; inner } ->
    Sym.Set.remove i (Sym.Set.union (IT.free_vars_list [ perm ]) (free_vars inner))
  | SplitSize { syms = _; rest } -> free_vars rest


and free_vars_list : t list -> Sym.Set.t =
  fun xs -> List.fold_left (fun ss t -> Sym.Set.union ss (free_vars t)) Sym.Set.empty xs


let rec pp (tm : t) : Pp.document =
  let open Pp in
  match tm with
  | Uniform { bt } -> !^"uniform" ^^ angles (BT.pp bt) ^^ parens empty
  | Pick { bt; choices } ->
    !^"pick"
    ^^ parens
         (brackets
            (nest
               2
               (break 1
                ^^ c_comment (BT.pp bt)
                ^/^ separate_map
                      (semi ^^ break 1)
                      (fun (w, gt) ->
                         parens (z w ^^ comma ^^ braces (nest 2 (break 1 ^^ pp gt))))
                      choices)))
  | Alloc -> !^"alloc" ^^ parens empty
  | Call { fsym; iargs; oarg_bt; sized } ->
    parens
      (Sym.pp fsym
       ^^ optional (fun (n, sym) -> brackets (int n ^^ comma ^^^ Sym.pp sym)) sized
       ^^ parens
            (nest
               2
               (separate_map
                  (comma ^^ break 1)
                  (fun (x, y) -> Sym.pp x ^^ colon ^^^ Sym.pp y)
                  iargs))
       ^^^ colon
       ^^^ BT.pp oarg_bt)
  | Asgn { addr; sct; value; rest } ->
    Sctypes.pp sct ^^^ IT.pp addr ^^^ !^":=" ^^^ IT.pp value ^^ semi ^/^ pp rest
  | LetStar { x : Sym.t; x_bt : BT.t; value : t; rest : t } ->
    !^"let*"
    ^^^ Sym.pp x
    ^^^ colon
    ^^^ BT.pp x_bt
    ^^^ equals
    ^^ nest 2 (break 1 ^^ pp value)
    ^^ semi
    ^/^ pp rest
  | Return { value : IT.t } -> !^"return" ^^^ IT.pp value
  | Assert { prop : LC.t; rest : t } ->
    !^"assert" ^^ parens (nest 2 (break 1 ^^ LC.pp prop) ^^ break 1) ^^ semi ^/^ pp rest
  | ITE { bt : BT.t; cond : IT.t; t : t; f : t } ->
    !^"if"
    ^^^ parens (IT.pp cond)
    ^^^ braces (nest 2 (break 1 ^^ c_comment (BT.pp bt) ^/^ pp t) ^^ break 1)
    ^^^ !^"else"
    ^^^ braces (nest 2 (break 1 ^^ pp f) ^^ break 1)
  | Map { i; bt; perm; inner } ->
    let i_bt, _ = BT.map_bt bt in
    !^"map"
    ^^^ parens (BT.pp i_bt ^^^ Sym.pp i ^^ semi ^^^ IT.pp perm)
    ^^ braces (c_comment (BT.pp bt) ^^ nest 2 (break 1 ^^ pp inner) ^^ break 1)
  | SplitSize { syms; rest } ->
    !^"split_size"
    ^^ parens
         (separate_map (comma ^^ space) Sym.pp (syms |> Sym.Set.to_seq |> List.of_seq))
    ^^ semi
    ^/^ pp rest

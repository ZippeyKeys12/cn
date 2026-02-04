module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints

module Make (AD : Domain.T) = struct
  module Ctx = Ctx.Make (AD)
  module Def = Def.Make (AD)
  module Term = Term.Make (AD)

  (** Compute free vars of only the immediate expression, not continuations.
      This prevents variables from being forced too early.
      Adapted for pre-elaboration AST (Stage 2 constructs). *)
  let rec immediate_fv_bts (gt : Term.t) : BT.t Sym.Map.t =
    let (GenTerms.Annot (gt_, _, _, _)) = gt in
    match gt_ with
    | `LetStar ((_, gt1), _) -> immediate_fv_bts gt1
    | `Assert (lc, _) -> LC.free_vars_bts lc
    | `ITE (it, _, _) -> IT.free_vars_bts it
    | `Asgn ((it_addr, _), it_val, _) -> IT.free_vars_bts_list [ it_addr; it_val ]
    | `Map ((i, _, it_perm), gt_body) ->
      Sym.Map.remove
        i
        (Sym.Map.union
           (fun _ bt1 bt2 ->
              assert (BT.equal bt1 bt2);
              Some bt1)
           (IT.free_vars_bts it_perm)
           (Term.free_vars_bts gt_body))
    | `Pick _ -> Sym.Map.empty
    | `Force _ -> failwith ("unreachable @ " ^ __LOC__)
    | `Return it -> IT.free_vars_bts it
    | `Eager | `Symbolic | `Lazy -> Sym.Map.empty
    | `Call (_fsym, iargs) ->
      iargs
      |> List.filter (fun it -> Option.is_none (IT.is_sym it))
      |> IT.free_vars_bts_list


  let transform_gt (gt : Term.t) : Term.t =
    let rec aux (forced : Sym.Set.t) (gt : Term.t) : Term.t =
      let (GenTerms.Annot (gt_, tag, _bt, loc)) = gt in
      (* Identify which variables appear in the immediate expression *)
      let fv_bts = immediate_fv_bts gt in
      let newly_used = fv_bts |> Sym.Map.filter (fun x _ -> not (Sym.Set.mem x forced)) in
      (* Only create Force nodes for types that could be lazy *)
      let to_force =
        newly_used |> Sym.Map.filter (fun _ -> Term.is_arbitrary_supported_bt)
      in
      (* Mark ALL newly used variables as forced (including unsupported types) *)
      let forced' = Sym.Map.fold (fun x _ acc -> Sym.Set.add x acc) newly_used forced in
      (* Recursively transform sub-terms with updated forced set *)
      let transformed_gt_ =
        match gt_ with
        | `Eager -> `Eager
        | `Symbolic -> `Symbolic
        | `Lazy -> `Lazy
        | `Call (fsym, its) -> `Call (fsym, its)
        | `Return it -> `Return it
        | `Asgn ((addr, sct), it, gt') -> `Asgn ((addr, sct), it, aux forced' gt')
        | `LetStar ((x, gt1), gt2) ->
          (* Only mark x as forced if gt1 produces a concrete value.
             If gt1 is Eager or Symbolic (lazy placeholders), x still needs
             a force before its first use in the continuation. *)
          let next_forced =
            match gt1 with
            | GenTerms.Annot (`Lazy, _, _, _) -> forced'
            | GenTerms.Annot (`Eager, _, _, _)
            | Annot ((`Call _ | `Return _ | `Map _), _, _, _) ->
              Sym.Set.add x forced'
            | GenTerms.Annot (`Symbolic, _, _, _) -> failwith ("unsupported @ " ^ __LOC__)
            | _ -> failwith ("unreachable @ " ^ __LOC__)
          in
          `LetStar ((x, gt1), aux next_forced gt2)
        | `Assert (lc, gt') -> `Assert (lc, aux forced' gt')
        | `ITE (it, gt_then, gt_else) ->
          (* Both branches see the same variables as forced *)
          `ITE (it, aux forced' gt_then, aux forced' gt_else)
        | `Map ((i, bt, perm), gt') ->
          `Map ((i, bt, perm), aux (Sym.Set.add i forced') gt')
        | `Pick choices ->
          (* All choices see the same variables as forced *)
          `Pick (List.map (aux forced') choices)
        | `Force ((x, gt_inner), gt_rest) ->
          (* Mark x as forced for the continuation *)
          `Force ((x, gt_inner), aux (Sym.Set.add x forced') gt_rest)
      in
      let transformed = GenTerms.Annot (transformed_gt_, tag, Term.basetype gt, loc) in
      (* Insert Force nodes for newly used variables *)
      Sym.Map.fold
        (fun x inst_bt acc -> Term.force_ ((x, Term.eager_ tag inst_bt loc), acc) tag loc)
        to_force
        transformed
    in
    aux Sym.Set.empty gt


  let transform_gd (gd : Def.t) : Def.t = { gd with body = transform_gt gd.body }

  let transform (ctx : Ctx.t) : Ctx.t = List.map_snd transform_gd ctx
end

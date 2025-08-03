module Make (GT : GenTerms.T) (I : Domain.Interpreter with module AD = GT.AD) = struct
  open struct
    module AD = GT.AD
  end

  let interpret
        (ctx : AD.t Sym.Map.t)
        (tm :
          ( 'tag,
              ([< ('tag, 'recur) GenTerms.Make(AD).Inner.ast ] as 'recur) )
            GenTerms.annot)
    : AD.t
    =
    let rec interp
              (ctx : AD.t Sym.Map.t)
              (tm :
                ( 'tag,
                    ([< ('tag, 'recur) GenTerms.Make(AD).Inner.ast ] as 'recur) )
                  GenTerms.annot)
              (d : AD.t)
      : AD.t
      =
      let (GenTerms.Annot (tm_, tag, bt, loc)) = tm in
      match tm_ with
      (* Base cases that produce abstract values *)
      | `Arbitrary | `Return _ | `Call (_, _) | `CallSized (_, _, _) | `Map _ | `MapElab _
        ->
        I.abs_stmt ctx tm d
      (* Assignment: execute assignment then continue *)
      | `Asgn (_, _, gt')
      | `AsgnElab (_, _, _, gt')
      | `Assert (_, gt')
      | `AssertDomain (_, _, _, gt')
      | `SplitSize (_, gt')
      | `SplitSizeElab (_, _, gt') ->
        let d' = I.abs_stmt ctx tm d in
        interp ctx gt' d'
      (* Sequential composition: interpret first, then second *)
      | `LetStar ((x, gt1), gt2) ->
        let d' = interp ctx gt1 d in
        let d'' = AD.rename ~from:GenTerms.Domain.ret_sym ~to_:x d' in
        interp ctx gt2 d''
      (* Conditional: interpret both branches and join results *)
      | `ITE (_it_if, gt_then, gt_else) ->
        (* For forward analysis: join the results from both branches *)
        let d_then = interp ctx gt_then d in
        let d_else = interp ctx gt_else d in
        AD.join d_then d_else
      (* Pick: interpret all options and join results *)
      | `Pick gts ->
        (match gts with
         | [] -> AD.bottom
         | gt :: gts' ->
           List.fold_left
             (fun acc gt ->
                let d' = interp ctx gt d in
                AD.join acc d')
             (interp ctx gt d)
             gts')
      (* Weighted pick: interpret all options and join results *)
      | `PickSized wgts | `PickSizedElab (_, wgts) ->
        interp ctx (Annot (`Pick (List.map snd wgts), tag, bt, loc)) d
    in
    let rec loop d =
      let d' = interp ctx tm d in
      if AD.equal d d' then d else loop d'
    in
    (* Start with top for backward analysis *)
    loop AD.top
end

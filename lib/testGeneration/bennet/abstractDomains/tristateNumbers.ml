module BT = BaseTypes
module IT = IndexTerms

module TNumBasis = struct
  let name = "tristate"

  let c_name = "tnum"

  type t =
    { bt : BT.t;
      value : int64;
      mask : int64
    }
  [@@deriving eq, ord]

  let supported (bt : BT.t) = match bt with Bits _ -> true | _ -> false

  let bt { bt; _ } = bt

  (* Constructors *)
  let const bt value = { bt; value; mask = 0L }

  let unknown bt = { bt; value = 0L; mask = Int64.minus_one }

  (* Helper function for fls64 equivalent - find last set bit *)
  let fls64 x =
    if Int64.equal x 0L then
      0
    else (
      let rec loop n acc =
        if Int64.equal n 0L then
          acc
        else
          loop (Int64.shift_right_logical n 1) (acc + 1)
      in
      loop x 0)


  let range bt min_val max_val =
    let chi = Int64.logxor min_val max_val in
    let bits = fls64 chi in
    if bits > 63 then
      unknown bt
    else (
      let delta = Int64.sub (Int64.shift_left 1L bits) 1L in
      { bt; value = Int64.logand min_val (Int64.lognot delta); mask = delta })


  let bottom bt = { bt; value = 1L; mask = 1L }

  let top bt = unknown bt

  let is_bottom { mask; value; _ } =
    not (Int64.equal (Int64.logand value mask) Int64.zero)


  let is_top { mask; value; _ } =
    Int64.equal value Int64.zero && Int64.equal mask Int64.minus_one


  (* Predicates *)
  let is_const { mask; _ } = Int64.equal mask 0L

  let equals_const { value; mask; _ } c =
    is_const { value; mask; bt = BT.Bits (Signed, 64) } && Int64.equal value c


  let is_aligned { value; mask; _ } size =
    if Int64.equal size 0L then
      true
    else (
      let align_mask = Int64.sub size 1L in
      Int64.equal (Int64.logand (Int64.logor value mask) align_mask) 0L)


  let tnum_in a b =
    if Int64.compare (Int64.logand b.mask (Int64.lognot a.mask)) 0L <> 0 then
      false
    else (
      let b_masked = Int64.logand b.value (Int64.lognot a.mask) in
      Int64.equal a.value b_masked)


  (* Bitwise Operations *)
  let tnum_and a b =
    assert (BT.equal a.bt b.bt);
    if is_bottom a || is_bottom b then
      bottom a.bt
    else (
      let alpha = Int64.logor a.value a.mask in
      let beta = Int64.logor b.value b.mask in
      let v = Int64.logand a.value b.value in
      { bt = a.bt;
        value = v;
        mask = Int64.logand (Int64.logand alpha beta) (Int64.lognot v)
      })


  let tnum_or a b =
    assert (BT.equal a.bt b.bt);
    let v = Int64.logor a.value b.value in
    let mu = Int64.logor a.mask b.mask in
    { bt = a.bt; value = v; mask = Int64.logand mu (Int64.lognot v) }


  let tnum_xor a b =
    assert (BT.equal a.bt b.bt);
    let v = Int64.logxor a.value b.value in
    let mu = Int64.logor a.mask b.mask in
    { bt = a.bt; value = Int64.logand v (Int64.lognot mu); mask = mu }


  let tnum_add a b =
    assert (BT.equal a.bt b.bt);
    let sm = Int64.add a.mask b.mask in
    let sv = Int64.add a.value b.value in
    let sigma = Int64.add sm sv in
    let chi = Int64.logxor sigma sv in
    let mu = Int64.logor (Int64.logor chi a.mask) b.mask in
    { bt = a.bt; value = Int64.logand sv (Int64.lognot mu); mask = mu }


  let tnum_sub a b =
    assert (BT.equal a.bt b.bt);
    let dv = Int64.sub a.value b.value in
    let alpha = Int64.add dv a.mask in
    let beta = Int64.sub dv b.mask in
    let chi = Int64.logxor alpha beta in
    let mu = Int64.logor (Int64.logor chi a.mask) b.mask in
    { bt = a.bt; value = Int64.logand dv (Int64.lognot mu); mask = mu }


  let tnum_lshift a shift =
    { bt = a.bt;
      value = Int64.shift_left a.value shift;
      mask = Int64.shift_left a.mask shift
    }


  let tnum_rshift a shift =
    match BT.is_bits_bt a.bt with
    | Some (BT.Signed, _) ->
      { bt = a.bt;
        value = Int64.shift_right a.value shift;
        mask = Int64.shift_right_logical a.mask shift
      }
    | Some (BT.Unsigned, _) ->
      { bt = a.bt;
        value = Int64.shift_right_logical a.value shift;
        mask = Int64.shift_right_logical a.mask shift
      }
    | _ -> failwith "tnum_rshift: unsupported base type"


  let tnum_arshift a min_shift insn_bitness =
    (* Arithmetic right shift with minimum shift amount and instruction bitness *)
    if insn_bitness = 32 then (
      (* For 32-bit: cast to s32, shift, cast back to u32 *)
      let mask_32 = 0xFFFFFFFFL in
      let sign_bit_32 = 0x80000000L in
      (* Convert to signed 32-bit for arithmetic shift *)
      let to_s32 x =
        if Int64.compare (Int64.logand x sign_bit_32) 0L <> 0 then
          Int64.logor x (Int64.shift_left (-1L) 32) (* Sign extend *)
        else
          Int64.logand x mask_32
      in
      let value_s32 = to_s32 a.value in
      let mask_s32 = to_s32 a.mask in
      let shifted_value = Int64.shift_right value_s32 min_shift in
      let shifted_mask = Int64.shift_right mask_s32 min_shift in
      { bt = a.bt; value = shifted_value; mask = shifted_mask })
    else
      { (* For 64-bit: arithmetic shift as s64 *)
        bt = a.bt;
        value = Int64.shift_right a.value min_shift;
        mask = Int64.shift_right a.mask min_shift
      }


  let tnum_cast a target_bt =
    match (BT.is_bits_bt a.bt, BT.is_bits_bt target_bt) with
    | Some (src_sign, src_bits), Some (_, dst_bits) ->
      if src_bits = dst_bits then
        { a with bt = target_bt } (* Same size, just change type *)
      else if src_bits > dst_bits then (
        (* Narrowing cast - truncate *)
        let cast_mask = Int64.sub (Int64.shift_left 1L dst_bits) 1L in
        { bt = target_bt;
          value = Int64.logand a.value cast_mask;
          mask = Int64.logand a.mask cast_mask
        })
      else (
        (* Widening cast - need sign/zero extension *)
        let sign_bit_pos = src_bits - 1 in
        let sign_bit_mask = Int64.shift_left 1L sign_bit_pos in
        let src_mask = Int64.sub (Int64.shift_left 1L src_bits) 1L in
        if BT.equal_sign src_sign BT.Signed then (
          (* Sign extension for signed types *)
          let needs_sign_extension =
            (not (Int64.equal (Int64.logand a.value sign_bit_mask) 0L))
            || not (Int64.equal (Int64.logand a.mask sign_bit_mask) 0L)
          in
          if needs_sign_extension then (
            (* If sign bit is set or uncertain, extend with 1s *)
            let extension_mask = Int64.lognot src_mask in
            { bt = target_bt;
              value = Int64.logor a.value extension_mask;
              mask = Int64.logor a.mask extension_mask
            })
          else (* Sign bit is clear, zero extend *)
            { bt = target_bt; value = a.value; mask = a.mask })
        else (* Zero extension for unsigned types *)
          { bt = target_bt; value = a.value; mask = a.mask })
    | _ -> a (* Fallback for non-bits types *)


  let tnum_mul a b =
    assert (BT.equal a.bt b.bt);
    if is_bottom a || is_bottom b then
      bottom a.bt
    else (
      let acc_v = Int64.mul a.value b.value in
      let acc_m = ref { bt = a.bt; value = 0L; mask = 0L } in
      let a_ref = ref a in
      let b_ref = ref b in
      while not (Int64.equal !a_ref.value 0L && Int64.equal !a_ref.mask 0L) do
        (* LSB of tnum a is a certain 1 *)
        if Int64.equal (Int64.logand !a_ref.value 1L) 1L then
          acc_m := tnum_add !acc_m { bt = a.bt; value = 0L; mask = !b_ref.mask }
        (* LSB of tnum a is uncertain *)
        else if Int64.equal (Int64.logand !a_ref.mask 1L) 1L then
          acc_m
          := tnum_add
               !acc_m
               { bt = a.bt; value = 0L; mask = Int64.logor !b_ref.value !b_ref.mask };
        (* Note: no case for LSB is certain 0 *)
        (* Use logical shifts to ensure termination *)
        a_ref
        := { bt = !a_ref.bt;
             value = Int64.shift_right_logical !a_ref.value 1;
             mask = Int64.shift_right_logical !a_ref.mask 1
           };
        b_ref := tnum_lshift !b_ref 1
      done;
      tnum_add { bt = a.bt; value = acc_v; mask = 0L } !acc_m)


  let leq a b =
    assert (BT.equal a.bt b.bt);
    if is_bottom a then
      true
    else if is_bottom b then
      false
    else if is_top b then
      true
    else if is_top a then
      false
    else if
      (* Check if a is more precise than b: a's mask is subset of b's mask, and values agree *)
      Int64.compare (Int64.logand a.mask (Int64.lognot b.mask)) 0L <> 0
    then
      false
    else (
      let a_masked = Int64.logand a.value (Int64.lognot b.mask) in
      let b_masked = Int64.logand b.value (Int64.lognot b.mask) in
      Int64.equal a_masked b_masked)


  let join d1 d2 =
    { bt = d1.bt;
      value = Int64.logand d1.value d2.value;
      mask =
        (let combined_mask = Int64.logor d1.mask d2.mask in
         let eta = Int64.lognot combined_mask in
         let delta =
           Int64.logxor (Int64.logand d1.value eta) (Int64.logand d2.value eta)
         in
         Int64.logor combined_mask delta)
    }


  let meet a b =
    assert (BT.equal a.bt b.bt);
    if is_bottom a || is_bottom b then
      bottom a.bt
    else
      { bt = a.bt;
        value = Int64.logor a.value b.value;
        mask = Int64.logand a.mask b.mask
      }


  let join_many = function
    | [] -> failwith "join_many: empty list"
    | x :: xs -> List.fold_left join x xs


  let meet_many = function
    | [] -> failwith "meet_many: empty list"
    | x :: xs -> List.fold_left meet x xs


  let of_interval bt min_val max_val =
    if Z.equal min_val max_val then
      const bt (Z.to_int64 min_val)
    else
      range bt (Z.to_int64 min_val) (Z.to_int64 max_val)


  let pp { bt; value; mask } =
    Pp.(!^"tnum[" ^^ BT.pp bt ^^ !^"]" ^^ parens (int64 value ^^ comma ^^^ int64 mask))


  let forward_abs_binop (op : IT.binop) (b1 : t) (b2 : t) : t option =
    assert (BT.equal b1.bt b2.bt);
    if is_bottom b1 || is_bottom b2 then
      Some (bottom b1.bt)
    else (
      match op with
      | Add -> Some (tnum_add b1 b2)
      | Sub -> Some (tnum_sub b1 b2)
      | Mul -> Some (tnum_mul b1 b2)
      (* | Div | DivNoSMT -> failwith "TODO" *)
      (* | Mod -> failwith "TODO" *)
      | BW_And -> Some (tnum_and b1 b2)
      | BW_Or -> Some (tnum_or b1 b2)
      | BW_Xor -> Some (tnum_xor b1 b2)
      | ShiftLeft ->
        if is_const b2 then (
          (* Only handle constant shift amounts *)
          let shift_amount = Int64.to_int b2.value in
          if shift_amount >= 0 && shift_amount < 64 then
            Some (tnum_lshift b1 shift_amount)
          else (* Large or negative shifts produce unpredictable results *)
            Some (top b1.bt))
        else (* Non-constant shift amounts are too complex to handle precisely *)
          Some (top b1.bt)
      | ShiftRight ->
        if is_const b2 then (
          (* Only handle constant shift amounts *)
          let shift_amount = Int64.to_int b2.value in
          if shift_amount >= 0 && shift_amount < 64 then
            Some (tnum_rshift b1 shift_amount)
          else (* Large or negative shifts produce unpredictable results *)
            Some (top b1.bt))
        else (* Non-constant shift amounts are too complex to handle precisely *)
          Some (top b1.bt)
      | _ -> None)


  let forward_abs_unop (op : IT.unop) (_b : t) : t option =
    match op with BW_Compl -> failwith "TODO" | Negate -> failwith "TODO" | _ -> None


  let forward_abs_it (it : IT.t) (b_args : t list) : t option =
    let (IT (it_, bt, _loc)) = it in
    match it_ with
    | Const (Bits (_, n)) -> Some (const bt (Z.to_int64 n))
    | Binop (op, _, _) ->
      let b1, b2 =
        match b_args with
        | [ b1; b2 ] -> (b1, b2)
        | _ -> failwith "Incorrect number of arguments"
      in
      if not (BT.equal b1.bt b2.bt) then (
        print_endline
          Pp.(
            plain
              (IT.pp it
               ^^^ pp b1
               ^^ parens (BT.pp b1.bt)
               ^^^ pp b2
               ^^ parens (BT.pp b2.bt)));
        failwith __LOC__);
      forward_abs_binop op b1 b2
    | Unop (op, _) ->
      let b =
        match b_args with
        | [ b ] -> b
        | _ -> failwith "Incorrect number of arguments for unop"
      in
      forward_abs_unop op b
    | Cast (dst_bt, _) ->
      let source_tnum =
        match b_args with
        | [ b ] -> b
        | _ -> failwith "Cast requires exactly one argument"
      in
      if is_bottom source_tnum then
        Some (bottom dst_bt)
      else if not (supported dst_bt) then
        None
      else
        Some (tnum_cast source_tnum dst_bt)
    | _ -> None


  let rec backward_abs_it (it : IT.t) (bs : t list) =
    let (IT (it_, _, loc)) = it in
    match it_ with
    | Binop (EQ, it', _) ->
      let bt = IT.get_bt it' in
      if Option.is_none (BT.is_bits_bt bt) then
        bs
      else (
        let b1, b2 = match bs with [ b1; b2 ] -> (b1, b2) | _ -> failwith __LOC__ in
        let b = meet b1 b2 in
        [ b; b ])
    | Binop (LE, _it', _) -> failwith "TODO"
    | Binop (LT, _it', _) -> failwith "TODO"
    | Unop (Not, IT (Binop (LE, it1, it2), _, _)) ->
      backward_abs_it (IT.lt_ (it2, it1) loc) bs
    | Unop (Not, IT (Binop (LT, it1, it2), _, _)) ->
      backward_abs_it (IT.le_ (it2, it1) loc) bs
    | _ ->
      if BT.equal BT.Bool (IT.get_bt it) then
        bs
      else
        List.tl bs


  let widen a b = join a b (* Simple widening for now *)

  let narrow a b = meet a b (* Simple narrowing for now *)

  let pp_params () = "ty tnum_value, ty tnum_mask"

  let pp_sym_args () = "tnum_value, tnum_mask"

  let pp_args { value; mask; _ } = Printf.sprintf "(%Ld, %Ld)" value mask

  let definitions () = Pp.empty
end

(* Create the full domain using the NonRelational functor *)
module Inner = NonRelational.Make (TNumBasis)

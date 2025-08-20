(** Tests for TristateNumbers domain *)

open OUnit2
open QCheck
module BT = Cn.BaseTypes
module Sym = Cn.Sym
module IT = Cn.IndexTerms

module NonRelational =
  Cn.TestGeneration.Private.Bennet.Private.AbstractDomains.Private.NonRelational

module TNumBasis =
  Cn.TestGeneration.Private.Bennet.Private.AbstractDomains.Private.TristateNumbers
  .TNumBasis

module TNumDomain = NonRelational.Make (TNumBasis)

(** Helper functions for creating test data *)
let test_loc = Cerb_location.unknown

(** Test bit types *)
let test_bt_u8 = BT.Bits (Unsigned, 8)

let test_bt_u16 = BT.Bits (Unsigned, 16)

let test_bt_u32 = BT.Bits (Unsigned, 32)

let test_bt_s8 = BT.Bits (Signed, 8)

let test_bt_s16 = BT.Bits (Signed, 16)

let test_bt_s32 = BT.Bits (Signed, 32)

let test_bt_s64 = BT.Bits (Signed, 64)

(** Helper to convert byte size to signed base type *)
let size_to_signed_bt = function
  | 1 -> test_bt_s8
  | 2 -> test_bt_s16
  | 3 | 4 -> test_bt_s32 (* Map 3 and 4 to 32-bit *)
  | 5 | 6 | 7 | 8 -> test_bt_s64 (* Map 5-8 to 64-bit *)
  | 0 -> test_bt_s8 (* Map 0 to smallest size *)
  | _ -> test_bt_s64 (* Default to largest size for any other case *)


(** Helper to get bit width from base type *)
let bt_to_bit_width = function
  | BT.Bits (_, bits) -> bits
  | _ -> 64 (* Default for non-bits types *)


(** Helper to create tnums *)
let make_tnum bt value mask = { TNumBasis.bt; value; mask }

(** Helper for pretty printing tnums *)
let pp_tnum tnum = Cn.Pp.plain (TNumBasis.pp tnum)

(** Custom equality for tnums with better error messages *)
let assert_tnum_equal ~msg expected actual =
  assert_equal ~cmp:TNumBasis.equal ~printer:pp_tnum ~msg expected actual


(** Test basic tnum creation and properties *)
let test_basic_creation _ =
  let bt = test_bt_s32 in
  let bottom = TNumBasis.bottom bt in
  let top = TNumBasis.top bt in
  assert_bool "Bottom should be bottom" (TNumBasis.is_bottom bottom);
  assert_bool "Top should be top" (TNumBasis.is_top top);
  assert_bool "Bottom should not be top" (not (TNumBasis.is_top bottom));
  assert_bool "Top should not be bottom" (not (TNumBasis.is_bottom top));
  (* Test constant *)
  let const42 = TNumBasis.const bt 42L in
  assert_bool "Constant should not be bottom" (not (TNumBasis.is_bottom const42));
  assert_bool "Constant should not be top" (not (TNumBasis.is_top const42));
  assert_bool "Constant should be const" (TNumBasis.is_const const42);
  assert_bool "Constant should equal 42" (TNumBasis.equals_const const42 42L)


(** Test bitwise AND operation *)
let test_bitwise_and _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 0xAL in
  (* 1010 binary *)
  let b = TNumBasis.const bt 0xCL in
  (* 1100 binary *)
  let result = TNumBasis.tnum_and a b in
  (* 1010 AND 1100 = 1000 = 8 *)
  assert_bool "AND result should be const" (TNumBasis.is_const result);
  assert_bool "AND result should be 8" (TNumBasis.equals_const result 0x8L)


(** Test bitwise OR operation *)
let test_bitwise_or _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 0xAL in
  (* 1010 binary *)
  let b = TNumBasis.const bt 0xCL in
  (* 1100 binary *)
  let result = TNumBasis.tnum_or a b in
  (* 1010 OR 1100 = 1110 = 14 *)
  assert_bool "OR result should be const" (TNumBasis.is_const result);
  assert_bool "OR result should be 14" (TNumBasis.equals_const result 0xEL)


(** Test bitwise XOR operation *)
let test_bitwise_xor _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 0xAL in
  (* 1010 binary *)
  let b = TNumBasis.const bt 0xCL in
  (* 1100 binary *)
  let result = TNumBasis.tnum_xor a b in
  (* 1010 XOR 1100 = 0110 = 6 *)
  assert_bool "XOR result should be const" (TNumBasis.is_const result);
  assert_bool "XOR result should be 6" (TNumBasis.equals_const result 0x6L)


(** Test range construction *)
let test_range _ =
  let bt = test_bt_s32 in
  let t = TNumBasis.range bt 8L 15L in
  (* Values 8-15 have pattern 1xxx in lower 4 bits *)
  (* 8 = 1000, 15 = 1111, so value = 1000, mask = 0111 *)
  assert_equal ~msg:"Range value should be 8" 8L t.value;
  assert_equal ~msg:"Range mask should be 7" 7L t.mask


(** Test lattice join operation *)
let test_join _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 0xAL in
  (* 1010 *)
  let b = TNumBasis.const bt 0xCL in
  (* 1100 *)
  let result = TNumBasis.join a b in
  (* Join should create uncertainty where values differ *)
  assert_bool "Join result should not be const" (not (TNumBasis.is_const result));
  (* Expected: value = 1000 (bits that are same), mask = 0110 (bits that differ) *)
  assert_equal ~msg:"Join value should be 8" 8L result.value;
  assert_equal ~msg:"Join mask should be 6" 6L result.mask


(** Test lattice meet operation *)
let test_meet _ =
  let bt = test_bt_s32 in
  let a = make_tnum bt 8L 6L in
  (* Represents 8,10,14 (8 OR mask possibilities) *)
  let b = make_tnum bt 8L 2L in
  (* Represents 8,10 *)
  let result = TNumBasis.meet a b in
  (* Meet should intersect the possibilities *)
  assert_bool "Meet result should not be bottom" (not (TNumBasis.is_bottom result))


(** Test subset relation (leq) *)
let test_leq _ =
  let bt = test_bt_s32 in
  let const8 = TNumBasis.const bt 8L in
  let range_8_15 = TNumBasis.range bt 8L 15L in
  let top = TNumBasis.top bt in
  (* Constants should be ≤ ranges that contain them *)
  assert_bool "const 8 should be ≤ range [8,15]" (TNumBasis.leq const8 range_8_15);
  (* Everything should be ≤ top *)
  assert_bool "const should be ≤ top" (TNumBasis.leq const8 top);
  assert_bool "range should be ≤ top" (TNumBasis.leq range_8_15 top)


(** Test alignment predicate *)
let test_alignment _ =
  let bt = test_bt_s32 in
  let aligned16 = TNumBasis.const bt 16L in
  let unaligned17 = TNumBasis.const bt 17L in
  assert_bool "16 should be 8-byte aligned" (TNumBasis.is_aligned aligned16 8L);
  assert_bool "16 should be 4-byte aligned" (TNumBasis.is_aligned aligned16 4L);
  assert_bool
    "17 should not be 8-byte aligned"
    (not (TNumBasis.is_aligned unaligned17 8L));
  assert_bool
    "17 should not be 4-byte aligned"
    (not (TNumBasis.is_aligned unaligned17 4L))


(** Test of_interval constructor *)
let test_of_interval _ =
  let bt = test_bt_s32 in
  let single = TNumBasis.of_interval bt (Z.of_int 42) (Z.of_int 42) in
  let range = TNumBasis.of_interval bt (Z.of_int 8) (Z.of_int 15) in
  assert_bool "Single interval should be const" (TNumBasis.is_const single);
  assert_bool "Single interval should equal 42" (TNumBasis.equals_const single 42L);
  assert_bool "Range interval should not be const" (not (TNumBasis.is_const range))


(** Test operations with uncertain bits *)
let test_uncertain_operations _ =
  let bt = test_bt_s32 in
  (* Create tnum representing {8, 9, 10, 11} = 8 | {0,1,2,3} *)
  let uncertain = make_tnum bt 8L 3L in
  let const2 = TNumBasis.const bt 2L in
  (* AND with 2 should restrict possibilities *)
  let and_result = TNumBasis.tnum_and uncertain const2 in
  assert_bool
    "AND with uncertain should not be const"
    (not (TNumBasis.is_const and_result));
  (* OR with 1 should expand possibilities *)
  let or_result = TNumBasis.tnum_or uncertain (TNumBasis.const bt 1L) in
  assert_bool "OR with uncertain should not be const" (not (TNumBasis.is_const or_result))


(** Test tnum_add with constants *)
let test_tnum_add_constants _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 5L in
  let b = TNumBasis.const bt 3L in
  let result = TNumBasis.tnum_add a b in
  assert_bool "Add constants should be const" (TNumBasis.is_const result);
  assert_bool "5 + 3 should equal 8" (TNumBasis.equals_const result 8L)


(** Test tnum_add with uncertainty *)
let test_tnum_add_uncertain _ =
  let bt = test_bt_s32 in
  (* Create tnum representing {0, 1} = 0 | {0,1} *)
  let uncertain_a = make_tnum bt 0L 1L in
  (* Create tnum representing {0, 2} = 0 | {0,2} *)
  let uncertain_b = make_tnum bt 0L 2L in
  let result = TNumBasis.tnum_add uncertain_a uncertain_b in
  (* Result should capture uncertainty in the sum *)
  assert_bool "Add uncertain should not be const" (not (TNumBasis.is_const result))


(** Test tnum_add with carry propagation *)
let test_tnum_add_carry _ =
  let bt = test_bt_s32 in
  (* Test case that exercises carry propagation *)
  let a = TNumBasis.const bt 0xFFFFFFFFL in
  (* Large value close to overflow *)
  let b = TNumBasis.const bt 1L in
  let result = TNumBasis.tnum_add a b in
  (* Should result in 0x100000000L in 64-bit arithmetic *)
  assert_bool "Overflow add should be const" (TNumBasis.is_const result);
  assert_bool "Should result in 0x100000000L" (TNumBasis.equals_const result 0x100000000L)


(** Test tnum_add identity *)
let test_tnum_add_identity _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 42L in
  let zero = TNumBasis.const bt 0L in
  let result = TNumBasis.tnum_add a zero in
  assert_bool "Add zero should preserve value" (TNumBasis.equals_const result 42L)


(** Test tnum_sub with constants *)
let test_tnum_sub_constants _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 10L in
  let b = TNumBasis.const bt 3L in
  let result = TNumBasis.tnum_sub a b in
  assert_bool "Sub constants should be const" (TNumBasis.is_const result);
  assert_bool "10 - 3 should equal 7" (TNumBasis.equals_const result 7L)


(** Test tnum_sub with uncertainty *)
let test_tnum_sub_uncertain _ =
  let bt = test_bt_s32 in
  (* Create tnum representing {2, 3} = 2 | {0,1} *)
  let uncertain_a = make_tnum bt 2L 1L in
  (* Create tnum representing {0, 1} = 0 | {0,1} *)
  let uncertain_b = make_tnum bt 0L 1L in
  let result = TNumBasis.tnum_sub uncertain_a uncertain_b in
  (* Result should capture uncertainty in the difference *)
  assert_bool "Sub uncertain should not be const" (not (TNumBasis.is_const result))


(** Test tnum_sub with potential underflow *)
let test_tnum_sub_underflow _ =
  let bt = test_bt_s32 in
  (* Test case that exercises underflow in 32-bit arithmetic *)
  let a = TNumBasis.const bt 0L in
  let b = TNumBasis.const bt 1L in
  let result = TNumBasis.tnum_sub a b in
  (* Should underflow to 0xFFFFFFFF (-1 in 32-bit signed) *)
  assert_bool "Underflow sub should be const" (TNumBasis.is_const result);
  assert_bool "0 - 1 should wrap to -1" (TNumBasis.equals_const result (-1L))


(** Test tnum_sub identity (x - 0 = x) *)
let test_tnum_sub_identity _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 42L in
  let zero = TNumBasis.const bt 0L in
  let result = TNumBasis.tnum_sub a zero in
  assert_bool "Sub zero should preserve value" (TNumBasis.equals_const result 42L)


(** Test tnum_sub self (x - x = 0) *)
let test_tnum_sub_self _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 42L in
  let result = TNumBasis.tnum_sub a a in
  assert_bool "Sub self should be zero" (TNumBasis.equals_const result 0L)


(** Test tnum_sub with edge values *)
let test_tnum_sub_edge_cases _ =
  let bt = test_bt_s32 in
  (* Test large positive minus large positive *)
  let large1 = TNumBasis.const bt 0x7FFFFFFFL in
  let large2 = TNumBasis.const bt 0x7FFFFFFEL in
  let result1 = TNumBasis.tnum_sub large1 large2 in
  assert_bool "Large - large should be const" (TNumBasis.is_const result1);
  assert_bool "Should equal 1" (TNumBasis.equals_const result1 1L);
  (* Test negative minus positive *)
  let neg = TNumBasis.const bt (-10L) in
  let pos = TNumBasis.const bt 5L in
  let result2 = TNumBasis.tnum_sub neg pos in
  assert_bool "Negative - positive should be const" (TNumBasis.is_const result2);
  assert_bool "Should equal -15" (TNumBasis.equals_const result2 (-15L))


(** Test tnum_sub with range values *)
let test_tnum_sub_range _ =
  let bt = test_bt_s32 in
  (* Create a range that represents values 8-15 *)
  let range_a = TNumBasis.range bt 8L 15L in
  let const_b = TNumBasis.const bt 4L in
  let result = TNumBasis.tnum_sub range_a const_b in
  (* Result should be range 4-11 with some uncertainty *)
  assert_bool "Range - const should not be const" (not (TNumBasis.is_const result))


(** ================= COMPREHENSIVE TNUM_MUL TESTS ================= *)

(** Test tnum_mul with constants *)
let test_tnum_mul_constants _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 6L in
  let b = TNumBasis.const bt 7L in
  let result = TNumBasis.tnum_mul a b in
  assert_bool "Mul constants should be const" (TNumBasis.is_const result);
  assert_bool "6 * 7 should equal 42" (TNumBasis.equals_const result 42L)


(** Test tnum_mul with zero - should be absorbing element *)
let test_tnum_mul_zero _ =
  let bt = test_bt_s32 in
  let zero = TNumBasis.const bt 0L in
  let arbitrary = TNumBasis.const bt 0x5A5AL in
  let result1 = TNumBasis.tnum_mul zero arbitrary in
  let result2 = TNumBasis.tnum_mul arbitrary zero in
  assert_bool "Mul with zero should be zero (left)" (TNumBasis.equals_const result1 0L);
  assert_bool "Mul with zero should be zero (right)" (TNumBasis.equals_const result2 0L)


(** Test tnum_mul with one - should be identity element *)
let test_tnum_mul_one _ =
  let bt = test_bt_s32 in
  let one = TNumBasis.const bt 1L in
  let test_val = TNumBasis.const bt 0x12345678L in
  let result1 = TNumBasis.tnum_mul one test_val in
  let result2 = TNumBasis.tnum_mul test_val one in
  assert_bool
    "Mul with one should be identity (left)"
    (TNumBasis.equals_const result1 0x12345678L);
  assert_bool
    "Mul with one should be identity (right)"
    (TNumBasis.equals_const result2 0x12345678L)


(** Test tnum_mul with powers of 2 (should behave like left shift) *)
let test_tnum_mul_power_of_2 _ =
  let bt = test_bt_s32 in
  let val_a = TNumBasis.const bt 5L in
  let pow2_1 = TNumBasis.const bt 2L in
  (* 2^1 *)
  let pow2_2 = TNumBasis.const bt 4L in
  (* 2^2 *)
  let pow2_3 = TNumBasis.const bt 8L in
  (* 2^3 *)
  let result1 = TNumBasis.tnum_mul val_a pow2_1 in
  let result2 = TNumBasis.tnum_mul val_a pow2_2 in
  let result3 = TNumBasis.tnum_mul val_a pow2_3 in
  assert_bool "5 * 2 should equal 10" (TNumBasis.equals_const result1 10L);
  assert_bool "5 * 4 should equal 20" (TNumBasis.equals_const result2 20L);
  assert_bool "5 * 8 should equal 40" (TNumBasis.equals_const result3 40L)


(** Test tnum_mul commutative property *)
let test_tnum_mul_commutative _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 12L in
  let b = TNumBasis.const bt 15L in
  let result1 = TNumBasis.tnum_mul a b in
  let result2 = TNumBasis.tnum_mul b a in
  assert_tnum_equal ~msg:"Mul should be commutative" result1 result2;
  assert_bool "12 * 15 should equal 180" (TNumBasis.equals_const result1 180L)


(** Test tnum_mul with uncertainty in multiplier *)
let test_tnum_mul_uncertain_multiplier _ =
  let bt = test_bt_s32 in
  (* Create tnum representing {2, 3} = 2 | {0,1} *)
  let uncertain_a = make_tnum bt 2L 1L in
  let const_b = TNumBasis.const bt 5L in
  let result = TNumBasis.tnum_mul uncertain_a const_b in
  (* Result should capture uncertainty: {2*5, 3*5} = {10, 15} *)
  assert_bool "Mul with uncertain should not be const" (not (TNumBasis.is_const result))


(** Test tnum_mul with uncertainty in multiplicand *)
let test_tnum_mul_uncertain_multiplicand _ =
  let bt = test_bt_s32 in
  let const_a = TNumBasis.const bt 4L in
  (* Create tnum representing {6, 7} = 6 | {0,1} *)
  let uncertain_b = make_tnum bt 6L 1L in
  let result = TNumBasis.tnum_mul const_a uncertain_b in
  (* Result should capture uncertainty: {4*6, 4*7} = {24, 28} *)
  assert_bool "Mul with uncertain should not be const" (not (TNumBasis.is_const result))


(** Test tnum_mul with uncertainty in both operands *)
let test_tnum_mul_both_uncertain _ =
  let bt = test_bt_s32 in
  (* Create tnum representing {2, 3} = 2 | {0,1} *)
  let uncertain_a = make_tnum bt 2L 1L in
  (* Create tnum representing {4, 5} = 4 | {0,1} *)
  let uncertain_b = make_tnum bt 4L 1L in
  let result = TNumBasis.tnum_mul uncertain_a uncertain_b in
  (* Result should capture uncertainty: {2*4, 2*5, 3*4, 3*5} = {8, 10, 12, 15} *)
  assert_bool
    "Mul with both uncertain should not be const"
    (not (TNumBasis.is_const result))


(** Test tnum_mul with small values to verify algorithm *)
let test_tnum_mul_algorithm_verification _ =
  let bt = test_bt_s32 in
  (* Test case to verify the bit-by-bit multiplication algorithm *)
  let a = TNumBasis.const bt 5L in
  (* 101 binary *)
  let b = TNumBasis.const bt 3L in
  (* 011 binary *)
  let result = TNumBasis.tnum_mul a b in
  (* Manual verification: 5 * 3 = 15 *)
  assert_bool "5 * 3 should equal 15" (TNumBasis.equals_const result 15L)


(** Test tnum_mul with larger values *)
let test_tnum_mul_large_values _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 123L in
  let b = TNumBasis.const bt 456L in
  let result = TNumBasis.tnum_mul a b in
  let expected = Int64.mul 123L 456L in
  assert_bool
    "Large multiplication should be correct"
    (TNumBasis.equals_const result expected)


(** Test tnum_mul with negative values *)
let test_tnum_mul_negative _ =
  let bt = test_bt_s32 in
  let neg_a = TNumBasis.const bt (-5L) in
  let pos_b = TNumBasis.const bt 7L in
  let result1 = TNumBasis.tnum_mul neg_a pos_b in
  assert_bool
    "Negative * positive should be negative"
    (TNumBasis.equals_const result1 (-35L));
  let neg_b = TNumBasis.const bt (-3L) in
  let result2 = TNumBasis.tnum_mul neg_a neg_b in
  assert_bool
    "Negative * negative should be positive"
    (TNumBasis.equals_const result2 15L)


(** Test tnum_mul with range values *)
let test_tnum_mul_range _ =
  let bt = test_bt_s32 in
  let range_a = TNumBasis.range bt 2L 3L in
  (* {2, 3} *)
  let const_b = TNumBasis.const bt 4L in
  let result = TNumBasis.tnum_mul range_a const_b in
  (* Result should represent {8, 12} with some uncertainty pattern *)
  assert_bool "Range * const should not be const" (not (TNumBasis.is_const result))


(** Test tnum_mul edge case: very small uncertain bits *)
let test_tnum_mul_small_uncertainty _ =
  let bt = test_bt_s32 in
  (* Create tnum with minimal uncertainty: {0, 1} = 0 | {0,1} *)
  let small_uncertain = make_tnum bt 0L 1L in
  let const_val = TNumBasis.const bt 100L in
  let result = TNumBasis.tnum_mul small_uncertain const_val in
  (* Result should represent {0, 100} *)
  assert_bool
    "Small uncertainty * const should not be const"
    (not (TNumBasis.is_const result))


(** Test tnum_mul associative property for constants *)
let test_tnum_mul_associative_constants _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 2L in
  let b = TNumBasis.const bt 3L in
  let c = TNumBasis.const bt 5L in
  (* Test (a * b) * c = a * (b * c) *)
  let ab = TNumBasis.tnum_mul a b in
  let result1 = TNumBasis.tnum_mul ab c in
  let bc = TNumBasis.tnum_mul b c in
  let result2 = TNumBasis.tnum_mul a bc in
  assert_tnum_equal ~msg:"Mul should be associative for constants" result1 result2;
  assert_bool "2 * 3 * 5 should equal 30" (TNumBasis.equals_const result1 30L)


(** Test tnum_mul distributive over addition (for constants) *)
let test_tnum_mul_distributive _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 3L in
  let b = TNumBasis.const bt 4L in
  let c = TNumBasis.const bt 5L in
  (* Test a * (b + c) = (a * b) + (a * c) *)
  let bc_sum = TNumBasis.tnum_add b c in
  let left_side = TNumBasis.tnum_mul a bc_sum in
  let ab = TNumBasis.tnum_mul a b in
  let ac = TNumBasis.tnum_mul a c in
  let right_side = TNumBasis.tnum_add ab ac in
  assert_tnum_equal ~msg:"Mul should be distributive over add" left_side right_side;
  assert_bool "3 * (4 + 5) should equal 27" (TNumBasis.equals_const left_side 27L)


(** Test tnum_mul overflow behavior *)
let test_tnum_mul_overflow _ =
  let bt = test_bt_s32 in
  (* Test values that will overflow 32-bit but fit in 64-bit *)
  let large1 = TNumBasis.const bt 0x10000L in
  let large2 = TNumBasis.const bt 0x10000L in
  let result = TNumBasis.tnum_mul large1 large2 in
  let expected = Int64.mul 0x10000L 0x10000L in
  assert_bool
    "Large multiplication should handle overflow"
    (TNumBasis.equals_const result expected)


(** Test tnum_mul with top (maximum uncertainty) *)
let test_tnum_mul_with_top _ =
  let bt = test_bt_s32 in
  let top = TNumBasis.top bt in
  let const_val = TNumBasis.const bt 5L in
  let result = TNumBasis.tnum_mul top const_val in
  (* Result should have significant uncertainty *)
  assert_bool "top * const should not be const" (not (TNumBasis.is_const result));
  assert_bool "top * const should not be bottom" (not (TNumBasis.is_bottom result))


(** Test tnum_mul with bottom (should not occur in practice) *)
let test_tnum_mul_with_bottom _ =
  let bt = test_bt_s32 in
  let bottom = TNumBasis.bottom bt in
  let normal = TNumBasis.const bt 42L in
  let result1 = TNumBasis.tnum_mul bottom normal in
  let result2 = TNumBasis.tnum_mul normal bottom in
  (* bottom represents no possible values, so multiplication should give bottom *)
  assert_bool "bottom * x should be bottom" (TNumBasis.is_bottom result1);
  assert_bool "x * bottom should be bottom" (TNumBasis.is_bottom result2)


(** ================= COMPREHENSIVE TNUM_AND TESTS ================= *)

(** Test tnum_and with zero - should be absorbing element *)
let test_tnum_and_zero _ =
  let bt = test_bt_s32 in
  let zero = TNumBasis.const bt 0L in
  let arbitrary = TNumBasis.const bt 0x5A5AL in
  (* arbitrary bit pattern *)
  let result1 = TNumBasis.tnum_and zero arbitrary in
  let result2 = TNumBasis.tnum_and arbitrary zero in
  assert_bool "AND with zero should be zero (left)" (TNumBasis.equals_const result1 0L);
  assert_bool "AND with zero should be zero (right)" (TNumBasis.equals_const result2 0L)


(** Test tnum_and with all-ones (identity under AND) *)
let test_tnum_and_all_ones _ =
  let bt = test_bt_s32 in
  let all_ones = TNumBasis.const bt (-1L) in
  (* 0xFFFFFFFFFFFFFFFF *)
  let test_val = TNumBasis.const bt 0x12345678L in
  let result1 = TNumBasis.tnum_and all_ones test_val in
  let result2 = TNumBasis.tnum_and test_val all_ones in
  assert_bool
    "AND with all-ones should be identity (left)"
    (TNumBasis.equals_const result1 0x12345678L);
  assert_bool
    "AND with all-ones should be identity (right)"
    (TNumBasis.equals_const result2 0x12345678L)


(** Test tnum_and commutative property *)
let test_tnum_and_commutative _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 0xAAAAL in
  (* 1010101010101010 *)
  let b = TNumBasis.const bt 0x5555L in
  (* 0101010101010101 *)
  let result1 = TNumBasis.tnum_and a b in
  let result2 = TNumBasis.tnum_and b a in
  assert_tnum_equal ~msg:"AND should be commutative" result1 result2;
  assert_bool "a AND b should be 0" (TNumBasis.equals_const result1 0L)


(** Test tnum_and associative property *)
let test_tnum_and_associative _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 0xF0F0L in
  let b = TNumBasis.const bt 0xFF00L in
  let c = TNumBasis.const bt 0xF00FL in
  (* Test (a AND b) AND c = a AND (b AND c) *)
  let ab = TNumBasis.tnum_and a b in
  let result1 = TNumBasis.tnum_and ab c in
  let bc = TNumBasis.tnum_and b c in
  let result2 = TNumBasis.tnum_and a bc in
  assert_tnum_equal ~msg:"AND should be associative" result1 result2


(** Test tnum_and idempotent property (x AND x = x) *)
let test_tnum_and_idempotent _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 0x12345678L in
  let result = TNumBasis.tnum_and a a in
  assert_tnum_equal ~msg:"AND should be idempotent" a result


(** Test tnum_and with uncertain bits - core algorithm verification *)
let test_tnum_and_uncertain_algorithm _ =
  let bt = test_bt_s32 in
  (* Test case from C algorithm: 
   * a = {value=4, mask=3} represents {4,5,6,7} = 100 | {000,001,010,011}
   * b = {value=2, mask=1} represents {2,3} = 10 | {0,1}
   *
   * Manual calculation following C algorithm:
   * alpha = a.value | a.mask = 4 | 3 = 7 (111 binary)
   * beta = b.value | b.mask = 2 | 1 = 3 (011 binary)  
   * v = a.value & b.value = 4 & 2 = 0 (000 binary)
   * mask = alpha & beta & ~v = 7 & 3 & ~0 = 3 & 7 = 3 (011 binary)
   * result = {value=0, mask=3} representing {0,1,2,3}
  *)
  let a = make_tnum bt 4L 3L in
  (* represents {4,5,6,7} *)
  let b = make_tnum bt 2L 1L in
  (* represents {2,3} *)
  let result = TNumBasis.tnum_and a b in
  (* Verify the algorithm step by step *)
  assert_equal ~msg:"Result value should be 0" 0L result.value;
  assert_equal ~msg:"Result mask should be 3" 3L result.mask;
  (* Verify this matches expected concrete results:
   * 4 & 2 = 0, 4 & 3 = 0, 5 & 2 = 0, 5 & 3 = 1,
   * 6 & 2 = 2, 6 & 3 = 2, 7 & 2 = 2, 7 & 3 = 3
   * So possible results are {0,1,2,3} = 0 | {0,1,2,3} = {value=0, mask=3}
  *)
  assert_bool "Result should not be const" (not (TNumBasis.is_const result))


(** Test tnum_and with partial overlap in uncertain bits *)
let test_tnum_and_partial_overlap _ =
  let bt = test_bt_s32 in
  (* a represents {8,9} = 8 | {0,1} = 1000 | {0,1} = {1000, 1001}
   * b represents {10,11} = 10 | {0,1} = 1010 | {0,1} = {1010, 1011}
   *
   * Manual calculation:
   * alpha = 8 | 1 = 9 (1001)
   * beta = 10 | 1 = 11 (1011)
   * v = 8 & 10 = 8 (1000)
   * mask = 9 & 11 & ~8 = 9 & 3 = 1 (0001)
   * result = {value=8, mask=1} representing {8,9}
  *)
  let a = make_tnum bt 8L 1L in
  (* {8,9} *)
  let b = make_tnum bt 10L 1L in
  (* {10,11} *)
  let result = TNumBasis.tnum_and a b in
  (* Concrete verification: 8&10=8, 8&11=8, 9&10=8, 9&11=9 -> {8,9} *)
  assert_equal ~msg:"Result value should be 8" 8L result.value;
  assert_equal ~msg:"Result mask should be 1" 1L result.mask


(** Test tnum_and where result has no uncertainty *)
let test_tnum_and_no_uncertainty _ =
  let bt = test_bt_s32 in
  (* a represents {12,13} = 12 | {0,1} = 1100 | {0,1}
   * b represents {3} = 3 | {} = 0011
   *
   * Manual calculation:
   * alpha = 12 | 1 = 13 (1101)
   * beta = 3 | 0 = 3 (0011)
   * v = 12 & 3 = 0 (0000)
   * mask = 13 & 3 & ~0 = 1 & 7 = 1 (0001)
   * 
   * Wait, let me recalculate:
   * mask = 13 & 3 & ~0 = 1 & 3 = 1
   * So result = {value=0, mask=1} representing {0,1}
  *)
  let a = make_tnum bt 12L 1L in
  (* {12,13} *)
  let b = TNumBasis.const bt 3L in
  (* {3} *)
  let result = TNumBasis.tnum_and a b in
  (* Concrete verification: 12&3=0, 13&3=1 -> {0,1} *)
  assert_equal ~msg:"Result value should be 0" 0L result.value;
  assert_equal ~msg:"Result mask should be 1" 1L result.mask


(** Test tnum_and with large uncertain ranges *)
let test_tnum_and_large_ranges _ =
  let bt = test_bt_s32 in
  (* Test with ranges that have significant uncertainty *)
  let range_a = TNumBasis.range bt 16L 31L in
  (* 16-31: 10000 to 11111 *)
  let range_b = TNumBasis.range bt 24L 39L in
  (* 24-39: 11000 to 100111 *)
  let result = TNumBasis.tnum_and range_a range_b in
  (* Should produce some uncertainty but be bounded by the intersection *)
  assert_bool "Large range AND should not be const" (not (TNumBasis.is_const result));
  assert_bool "Result should not be bottom" (not (TNumBasis.is_bottom result))


(** Test tnum_and with range and constant *)
let test_tnum_and_range_constant _ =
  let bt = test_bt_s32 in
  let range = TNumBasis.range bt 8L 15L in
  (* {8,9,10,11,12,13,14,15} *)
  let mask_const = TNumBasis.const bt 12L in
  (* 1100 binary *)
  let result = TNumBasis.tnum_and range mask_const in
  (* Each value 8-15 AND 12:
   * 8&12=8, 9&12=8, 10&12=8, 11&12=8, 12&12=12, 13&12=12, 14&12=12, 15&12=12
   * Results: {8,12} = 8 | {0,4} but that's not quite right...
   * Let me think: 1000&1100=1000(8), 1001&1100=1000(8), 1010&1100=1000(8), 1011&1100=1000(8)
   *               1100&1100=1100(12), 1101&1100=1100(12), 1110&1100=1100(12), 1111&1100=1100(12)
   * So results are {8,12}
  *)
  assert_bool "Range AND const should not be const" (not (TNumBasis.is_const result))


(** Test tnum_and edge case: all bits uncertain vs constant *)
let test_tnum_and_top_vs_const _ =
  let bt = test_bt_s32 in
  let top = TNumBasis.top bt in
  (* all bits uncertain *)
  let const_val = TNumBasis.const bt 0x5A5AL in
  let result = TNumBasis.tnum_and top const_val in
  (* top represents all possible values, AND with const should give range [0, const_val] *)
  assert_bool "top AND const should not be const" (not (TNumBasis.is_const result))


(** Test tnum_and with bottom (should not occur in practice but test for completeness) *)
let test_tnum_and_with_bottom _ =
  let bt = test_bt_s32 in
  let bottom = TNumBasis.bottom bt in
  let normal = TNumBasis.const bt 42L in
  (* Note: bottom should not occur in normal operation, but if it does, 
   * the algorithm should still work mathematically *)
  let result1 = TNumBasis.tnum_and bottom normal in
  let result2 = TNumBasis.tnum_and normal bottom in
  (* bottom = {value=0, mask=0}, so AND with anything gives {value=0&x, mask=0&?&~(0&x)} = {0,0} *)
  assert_tnum_equal ~msg:"bottom AND x should equal bottom" bottom result1;
  assert_tnum_equal ~msg:"x AND bottom should equal bottom" bottom result2


(** Test tnum_and manual algorithm verification *)
let test_tnum_and_manual_verification _ =
  let bt = test_bt_s32 in
  (* Carefully chosen test case to verify each step of the algorithm *)
  let a = make_tnum bt 0x30L 0x0FL in
  (* 110000 | 001111 = {48-63} *)
  let b = make_tnum bt 0x55L 0xAAL in
  (* 1010101 | 1010101x *)
  (* Step by step following C algorithm:
   * alpha = a.value | a.mask = 0x30 | 0x0F = 0x3F (111111)
   * beta = b.value | b.mask = 0x55 | 0xAA = 0xFF (11111111)
   * v = a.value & b.value = 0x30 & 0x55 = 0x10 (010000)
   * mask = alpha & beta & ~v = 0x3F & 0xFF & ~0x10 = 0x3F & 0xEF = 0x2F (101111)
   * result = {value=0x10, mask=0x2F}
  *)
  let result = TNumBasis.tnum_and a b in
  assert_equal ~msg:"Algorithm verification: value should be 0x10" 0x10L result.value;
  assert_equal ~msg:"Algorithm verification: mask should be 0x2F" 0x2FL result.mask


(** Test tnum_and with different bit widths conceptually *)
let test_tnum_and_different_patterns _ =
  let bt = test_bt_s32 in
  (* Test complementary bit patterns *)
  let pattern1 = TNumBasis.const bt 0xF0F0F0F0L in
  (* 11110000 repeated *)
  let pattern2 = TNumBasis.const bt 0x0F0F0F0FL in
  (* 00001111 repeated *)
  let result = TNumBasis.tnum_and pattern1 pattern2 in
  assert_bool "Complementary patterns AND should be 0" (TNumBasis.equals_const result 0L);
  (* Test alternating bit patterns *)
  let alt1 = TNumBasis.const bt 0xAAAAAAAAL in
  (* 10101010 repeated *)
  let alt2 = TNumBasis.const bt 0x55555555L in
  (* 01010101 repeated *)
  let result2 = TNumBasis.tnum_and alt1 alt2 in
  assert_bool "Alternating patterns AND should be 0" (TNumBasis.equals_const result2 0L);
  (* Test overlapping patterns *)
  let over1 = TNumBasis.const bt 0xFF00FF00L in
  let over2 = TNumBasis.const bt 0xF0F0F0F0L in
  let result3 = TNumBasis.tnum_and over1 over2 in
  let expected = Int64.logand 0xFF00FF00L 0xF0F0F0F0L in
  assert_bool
    "Overlapping patterns should AND correctly"
    (TNumBasis.equals_const result3 expected)


(** ================= COMPREHENSIVE TNUM_LSHIFT TESTS ================= **)

(** Test tnum_lshift with constants **)
let test_tnum_lshift_constants _ =
  let bt = test_bt_s32 in
  let a = TNumBasis.const bt 5L in
  (* 101 binary *)
  let result1 = TNumBasis.tnum_lshift a 1 in
  (* 5 << 1 = 10 *)
  let result2 = TNumBasis.tnum_lshift a 2 in
  (* 5 << 2 = 20 *)
  let result3 = TNumBasis.tnum_lshift a 3 in
  (* 5 << 3 = 40 *)
  assert_bool "Lshift constants should be const" (TNumBasis.is_const result1);
  assert_bool "5 << 1 should equal 10" (TNumBasis.equals_const result1 10L);
  assert_bool "5 << 2 should equal 20" (TNumBasis.equals_const result2 20L);
  assert_bool "5 << 3 should equal 40" (TNumBasis.equals_const result3 40L)


(** Test tnum_lshift with zero - should be absorbing for shift amount **)
let test_tnum_lshift_zero_value _ =
  let bt = test_bt_s32 in
  let zero = TNumBasis.const bt 0L in
  let result1 = TNumBasis.tnum_lshift zero 1 in
  let result2 = TNumBasis.tnum_lshift zero 5 in
  let result3 = TNumBasis.tnum_lshift zero 10 in
  assert_bool "Zero << 1 should be zero" (TNumBasis.equals_const result1 0L);
  assert_bool "Zero << 5 should be zero" (TNumBasis.equals_const result2 0L);
  assert_bool "Zero << 10 should be zero" (TNumBasis.equals_const result3 0L)


(** Test tnum_lshift with shift by 0 - should be identity **)
let test_tnum_lshift_zero_shift _ =
  let bt = test_bt_s32 in
  let test_vals = [ 42L; 0xAAAAL; 0x12345678L ] in
  List.iter
    (fun v ->
       let tnum = TNumBasis.const bt v in
       let result = TNumBasis.tnum_lshift tnum 0 in
       assert_tnum_equal ~msg:(Printf.sprintf "%Ld << 0 should be identity" v) tnum result)
    test_vals


(** Test tnum_lshift with power of 2 multiplication equivalence **)
let test_tnum_lshift_power_of_2_equiv _ =
  let bt = test_bt_s32 in
  let test_val = TNumBasis.const bt 7L in
  (* Test that x << n == x * (2^n) for small shifts *)
  let shift1_result = TNumBasis.tnum_lshift test_val 1 in
  let mult2_result = TNumBasis.tnum_mul test_val (TNumBasis.const bt 2L) in
  assert_tnum_equal ~msg:"x << 1 should equal x * 2" shift1_result mult2_result;
  let shift2_result = TNumBasis.tnum_lshift test_val 2 in
  let mult4_result = TNumBasis.tnum_mul test_val (TNumBasis.const bt 4L) in
  assert_tnum_equal ~msg:"x << 2 should equal x * 4" shift2_result mult4_result;
  let shift3_result = TNumBasis.tnum_lshift test_val 3 in
  let mult8_result = TNumBasis.tnum_mul test_val (TNumBasis.const bt 8L) in
  assert_tnum_equal ~msg:"x << 3 should equal x * 8" shift3_result mult8_result


(** Test tnum_lshift with uncertain bits **)
let test_tnum_lshift_uncertain _ =
  let bt = test_bt_s32 in
  (* Create tnum representing {4, 5} = 4 | {0,1} *)
  let uncertain = make_tnum bt 4L 1L in
  let result = TNumBasis.tnum_lshift uncertain 1 in
  (* Should represent {8, 10} = 8 | {0,2} *)
  assert_bool "Lshift uncertain should not be const" (not (TNumBasis.is_const result));
  assert_equal ~msg:"Lshift uncertain value should be 8" 8L result.value;
  assert_equal ~msg:"Lshift uncertain mask should be 2" 2L result.mask


(** Test tnum_lshift with range values **)
let test_tnum_lshift_range _ =
  let bt = test_bt_s32 in
  let range = TNumBasis.range bt 2L 3L in
  (* {2, 3} *)
  let result = TNumBasis.tnum_lshift range 2 in
  (* Should represent {8, 12} shifted *)
  assert_bool "Range << 2 should not be const" (not (TNumBasis.is_const result))


(** Test tnum_lshift preserves uncertainty pattern **)
let test_tnum_lshift_preserves_pattern _ =
  let bt = test_bt_s32 in
  (* Create tnum with alternating uncertainty: {0xA, 0xB} = 0xA | {0,1} *)
  let pattern = make_tnum bt 0xAL 0x1L in
  let result = TNumBasis.tnum_lshift pattern 4 in
  (* Should become {0xA0, 0xB0} = 0xA0 | {0,0x10} *)
  assert_equal ~msg:"Lshift should preserve pattern in value" 0xA0L result.value;
  assert_equal ~msg:"Lshift should preserve pattern in mask" 0x10L result.mask


(** Test tnum_lshift with large shifts **)
let test_tnum_lshift_large_shifts _ =
  let bt = test_bt_s32 in
  let small_val = TNumBasis.const bt 1L in
  (* Test shifting into high bits *)
  let result1 = TNumBasis.tnum_lshift small_val 31 in
  assert_bool "1 << 31 should be const" (TNumBasis.is_const result1);
  assert_bool
    "1 << 31 should equal 0x80000000"
    (TNumBasis.equals_const result1 (Int64.shift_left 1L 31));
  (* Test that shifting by 32 or more gives predictable results *)
  let result2 = TNumBasis.tnum_lshift small_val 32 in
  assert_bool "1 << 32 should be const" (TNumBasis.is_const result2);
  assert_bool
    "1 << 32 should equal 0x100000000"
    (TNumBasis.equals_const result2 (Int64.shift_left 1L 32))


(** Test tnum_lshift with negative values **)
let test_tnum_lshift_negative _ =
  let bt = test_bt_s32 in
  let neg_val = TNumBasis.const bt (-1L) in
  let result = TNumBasis.tnum_lshift neg_val 1 in
  assert_bool "(-1) << 1 should be const" (TNumBasis.is_const result);
  assert_bool "(-1) << 1 should equal -2" (TNumBasis.equals_const result (-2L))


(** Test tnum_lshift chain operations **)
let test_tnum_lshift_chain _ =
  let bt = test_bt_s32 in
  let initial = TNumBasis.const bt 3L in
  (* Test that (x << a) << b == x << (a + b) *)
  let result1 = TNumBasis.tnum_lshift (TNumBasis.tnum_lshift initial 2) 3 in
  let result2 = TNumBasis.tnum_lshift initial 5 in
  assert_tnum_equal ~msg:"(x << 2) << 3 should equal x << 5" result1 result2;
  assert_bool "3 << 5 should equal 96" (TNumBasis.equals_const result2 96L)


(** Test tnum_lshift with maximum uncertainty **)
let test_tnum_lshift_max_uncertainty _ =
  let bt = test_bt_s32 in
  let max_uncertain = make_tnum bt 0L 0xFFL in
  (* All lower 8 bits uncertain *)
  let result = TNumBasis.tnum_lshift max_uncertain 2 in
  (* Should shift uncertainty pattern *)
  assert_bool "Max uncertain << 2 should not be const" (not (TNumBasis.is_const result));
  assert_equal ~msg:"Max uncertain << 2 value should be 0" 0L result.value;
  assert_equal
    ~msg:"Max uncertain << 2 mask should be shifted"
    (Int64.shift_left 0xFFL 2)
    result.mask


(** Test tnum_lshift with bit boundaries **)
let test_tnum_lshift_bit_boundaries _ =
  let bt = test_bt_s32 in
  (* Test values near bit boundaries *)
  let boundary_vals =
    [ (0x7FFFFFFFL, 1);
      (* Max positive 32-bit << 1 *)
      (0xFFFFFFFFL, 1);
      (* Max 32-bit value << 1 *)
      (0x1L, 63) (* 1 << 63 (max shift for 64-bit) *)
    ]
  in
  List.iter
    (fun (v, shift) ->
       let tnum = TNumBasis.const bt v in
       let result = TNumBasis.tnum_lshift tnum shift in
       let expected = Int64.shift_left v shift in
       assert_bool
         (Printf.sprintf "%Ld << %d should equal %Ld" v shift expected)
         (TNumBasis.equals_const result expected))
    boundary_vals


(** Test tnum_lshift preserves base type **)
let test_tnum_lshift_preserves_bt _ =
  let bt = test_bt_s32 in
  let test_val = TNumBasis.const bt 42L in
  let result = TNumBasis.tnum_lshift test_val 3 in
  assert_bool "Lshift should preserve base type" (BT.equal bt result.bt)


(** Test tnum_lshift with edge case: shift by maximum amount **)
let test_tnum_lshift_max_shift _ =
  let bt = test_bt_s32 in
  let test_val = TNumBasis.const bt 1L in
  (* OCaml Int64.shift_left handles large shifts by taking modulo 64 *)
  let result = TNumBasis.tnum_lshift test_val 63 in
  assert_bool "1 << 63 should be const" (TNumBasis.is_const result);
  let expected = Int64.shift_left 1L 63 in
  assert_bool
    "1 << 63 should equal expected value"
    (TNumBasis.equals_const result expected)


(** ================= COMPREHENSIVE TNUM_ARSHIFT TESTS ================= **)

(** Test tnum_arshift with 32-bit constants **)
let test_tnum_arshift_32bit_constants _ =
  let bt = test_bt_s32 in
  (* Test positive value: 16 >> 2 = 4 *)
  let val16 = TNumBasis.const bt 16L in
  let result1 = TNumBasis.tnum_arshift val16 2 32 in
  assert_bool "16 >> 2 should be const" (TNumBasis.is_const result1);
  assert_bool "16 >> 2 should equal 4" (TNumBasis.equals_const result1 4L);
  (* Test another positive value: 1024 >> 3 = 128 *)
  let val1024 = TNumBasis.const bt 1024L in
  let result2 = TNumBasis.tnum_arshift val1024 3 32 in
  assert_bool "1024 >> 3 should be const" (TNumBasis.is_const result2);
  assert_bool "1024 >> 3 should equal 128" (TNumBasis.equals_const result2 128L)


(** Test tnum_arshift with 64-bit constants **)
let test_tnum_arshift_64bit_constants _ =
  let bt = test_bt_s64 in
  (* Test positive value: 32 >> 2 = 8 *)
  let val32 = TNumBasis.const bt 32L in
  let result1 = TNumBasis.tnum_arshift val32 2 64 in
  assert_bool "32 >> 2 should be const" (TNumBasis.is_const result1);
  assert_bool "32 >> 2 should equal 8" (TNumBasis.equals_const result1 8L);
  (* Test large value: 0x8000000000000000 >> 1 *)
  let large_val = Int64.shift_left 1L 63 in
  (* Most significant bit set *)
  let large_tnum = TNumBasis.const bt large_val in
  let result2 = TNumBasis.tnum_arshift large_tnum 1 64 in
  assert_bool "Large >> 1 should be const" (TNumBasis.is_const result2);
  let expected = Int64.shift_right large_val 1 in
  assert_bool "Large >> 1 should preserve sign" (TNumBasis.equals_const result2 expected)


(** Test tnum_arshift with 32-bit negative values **)
let test_tnum_arshift_32bit_negative _ =
  let bt = test_bt_s32 in
  (* Test -8 >> 2 = -2 (arithmetic right shift) *)
  let neg8 = TNumBasis.const bt (-8L) in
  let result1 = TNumBasis.tnum_arshift neg8 2 32 in
  assert_bool "-8 >> 2 should be const" (TNumBasis.is_const result1);
  (* In 32-bit arithmetic shift, -8 >> 2 = -2 *)
  assert_bool "-8 >> 2 should equal -2" (TNumBasis.equals_const result1 (-2L))


(** Test tnum_arshift with 64-bit negative values **)
let test_tnum_arshift_64bit_negative _ =
  let bt = test_bt_s64 in
  (* Test -16 >> 2 = -4 (arithmetic right shift) *)
  let neg16 = TNumBasis.const bt (-16L) in
  let result1 = TNumBasis.tnum_arshift neg16 2 64 in
  assert_bool "-16 >> 2 should be const" (TNumBasis.is_const result1);
  let expected = Int64.shift_right (-16L) 2 in
  assert_bool "-16 >> 2 should equal -4" (TNumBasis.equals_const result1 expected)


(** Test tnum_arshift with zero values **)
let test_tnum_arshift_32bit_zero _ =
  let bt = test_bt_s32 in
  let zero = TNumBasis.const bt 0L in
  let result1 = TNumBasis.tnum_arshift zero 5 32 in
  let result2 = TNumBasis.tnum_arshift zero 10 32 in
  assert_bool "0 >> 5 should be 0" (TNumBasis.equals_const result1 0L);
  assert_bool "0 >> 10 should be 0" (TNumBasis.equals_const result2 0L)


let test_tnum_arshift_64bit_zero _ =
  let bt = test_bt_s64 in
  let zero = TNumBasis.const bt 0L in
  let result1 = TNumBasis.tnum_arshift zero 3 64 in
  let result2 = TNumBasis.tnum_arshift zero 15 64 in
  assert_bool "0 >> 3 should be 0" (TNumBasis.equals_const result1 0L);
  assert_bool "0 >> 15 should be 0" (TNumBasis.equals_const result2 0L)


(** Test tnum_arshift identity (x >> 0 = x) **)
let test_tnum_arshift_identity _ =
  let bt = test_bt_s32 in
  let test_vals = [ 42L; -10L; 0L; 0x7FFFFFFFL ] in
  List.iter
    (fun v ->
       let tnum = TNumBasis.const bt v in
       let result32 = TNumBasis.tnum_arshift tnum 0 32 in
       let result64 = TNumBasis.tnum_arshift tnum 0 64 in
       assert_tnum_equal
         ~msg:(Printf.sprintf "%Ld >> 0 should be identity (32-bit)" v)
         tnum
         result32;
       assert_tnum_equal
         ~msg:(Printf.sprintf "%Ld >> 0 should be identity (64-bit)" v)
         tnum
         result64)
    test_vals


(** Test tnum_arshift sign extension behavior **)
let test_tnum_arshift_sign_extension _ =
  let bt = test_bt_s32 in
  (* Test 32-bit sign extension *)
  let val_with_high_bit = TNumBasis.const bt 0x80000001L in
  (* -2147483647 in 32-bit *)
  let result = TNumBasis.tnum_arshift val_with_high_bit 1 32 in
  assert_bool "Sign extension should preserve const" (TNumBasis.is_const result);
  (* Should sign-extend the 32-bit value properly *)
  let expected_32 = Int64.shift_right (Int64.of_int32 (Int64.to_int32 0x80000001L)) 1 in
  let sign_bit_32 = 0x80000000L in
  let sign_extend_mask = Int64.shift_left 0xFFFFFFFFL 32 in
  let extended =
    if Int64.compare (Int64.logand expected_32 sign_bit_32) 0L <> 0 then
      Int64.logor expected_32 sign_extend_mask
    else
      expected_32
  in
  assert_bool
    "Sign extension should work correctly"
    (TNumBasis.equals_const result extended)


(** Test tnum_arshift preserves base type **)
let test_tnum_arshift_preserves_bt _ =
  let bt = test_bt_s32 in
  let test_val = TNumBasis.const bt 42L in
  let result32 = TNumBasis.tnum_arshift test_val 3 32 in
  let result64 = TNumBasis.tnum_arshift test_val 3 64 in
  assert_bool "arshift should preserve base type (32-bit)" (BT.equal bt result32.bt);
  assert_bool "arshift should preserve base type (64-bit)" (BT.equal bt result64.bt)


(** Test tnum_arshift with large shifts **)
let test_tnum_arshift_large_shifts _ =
  let bt = test_bt_s32 in
  let test_val = TNumBasis.const bt 0x12345678L in
  (* Test various large shift amounts *)
  let result1 = TNumBasis.tnum_arshift test_val 31 32 in
  let result2 = TNumBasis.tnum_arshift test_val 63 64 in
  assert_bool "Large shift 31 should be const" (TNumBasis.is_const result1);
  assert_bool "Large shift 63 should be const" (TNumBasis.is_const result2)


(** Test tnum_arshift with uncertain values **)
let test_tnum_arshift_uncertain _ =
  let bt = test_bt_s32 in
  (* Create uncertain tnum: value = 16, mask = 7 represents {16,17,18,19,20,21,22,23} *)
  let uncertain = make_tnum bt 16L 7L in
  let result32 = TNumBasis.tnum_arshift uncertain 1 32 in
  let result64 = TNumBasis.tnum_arshift uncertain 1 64 in
  (* Should still have some uncertainty after shift by 1 *)
  assert_bool
    "arshift uncertain should not be const (32-bit)"
    (not (TNumBasis.is_const result32));
  assert_bool
    "arshift uncertain should not be const (64-bit)"
    (not (TNumBasis.is_const result64))


(** Test tnum_arshift with specific bit patterns **)
let test_tnum_arshift_bit_patterns _ =
  let bt = test_bt_s32 in
  (* Test with alternating bits *)
  let pattern = TNumBasis.const bt 0xAAAAAAAAL in
  let result32 = TNumBasis.tnum_arshift pattern 1 32 in
  let result64 = TNumBasis.tnum_arshift pattern 1 64 in
  assert_bool "Pattern shift should be const (32-bit)" (TNumBasis.is_const result32);
  assert_bool "Pattern shift should be const (64-bit)" (TNumBasis.is_const result64);
  (* Verify the pattern is preserved correctly *)
  let expected_32 = Int64.shift_right (Int64.of_int32 (Int64.to_int32 0xAAAAAAAAL)) 1 in
  let sign_bit_32 = 0x80000000L in
  let sign_extend_mask = Int64.shift_left 0xFFFFFFFFL 32 in
  let extended_32 =
    if Int64.compare (Int64.logand expected_32 sign_bit_32) 0L <> 0 then
      Int64.logor expected_32 sign_extend_mask
    else
      expected_32
  in
  let expected_64 = Int64.shift_right 0xAAAAAAAAL 1 in
  assert_bool
    "32-bit pattern shift should match expected"
    (TNumBasis.equals_const result32 extended_32);
  assert_bool
    "64-bit pattern shift should match expected"
    (TNumBasis.equals_const result64 expected_64)


(** ================= COMPREHENSIVE TNUM_CAST TESTS ================= **)

(** Test tnum_cast with constants - basic functionality **)
let test_tnum_cast_constants _ =
  let bt = test_bt_s64 in
  (* Test casting 64-bit value to 32-bit *)
  let val64 = TNumBasis.const bt 0x123456789ABCDEFL in
  let result32 = TNumBasis.tnum_cast val64 test_bt_s32 in
  (* Should keep lower 32 bits: 0x89ABCDEF *)
  assert_bool "64->32 cast should be const" (TNumBasis.is_const result32);
  assert_bool
    "64->32 cast should preserve lower 32 bits"
    (TNumBasis.equals_const result32 0x89ABCDEFL)


(** Test tnum_cast to different sizes **)
let test_tnum_cast_different_sizes _ =
  let bt = test_bt_s64 in
  let val64 = TNumBasis.const bt 0x123456789ABCDEFL in
  (* Cast to 1 byte (8 bits) *)
  let result8 = TNumBasis.tnum_cast val64 test_bt_s8 in
  assert_bool "64->8 cast should be const" (TNumBasis.is_const result8);
  assert_bool
    "64->8 cast should preserve lower 8 bits"
    (TNumBasis.equals_const result8 0xEFL);
  (* Cast to 2 bytes (16 bits) *)
  let result16 = TNumBasis.tnum_cast val64 test_bt_s16 in
  assert_bool "64->16 cast should be const" (TNumBasis.is_const result16);
  assert_bool
    "64->16 cast should preserve lower 16 bits"
    (TNumBasis.equals_const result16 0xCDEFL);
  (* Cast to 4 bytes (32 bits) *)
  let result32 = TNumBasis.tnum_cast val64 test_bt_s32 in
  assert_bool "64->32 cast should be const" (TNumBasis.is_const result32);
  assert_bool
    "64->32 cast should preserve lower 32 bits"
    (TNumBasis.equals_const result32 0x89ABCDEFL);
  (* Cast to 8 bytes (64 bits) - should be identity *)
  let result64 = TNumBasis.tnum_cast val64 test_bt_s64 in
  assert_tnum_equal ~msg:"64->64 cast should be identity" val64 result64


(** Test tnum_cast with uncertain values **)
let test_tnum_cast_uncertain _ =
  let bt = test_bt_s64 in
  (* Create tnum with uncertainty in upper bits that should be removed *)
  let uncertain_upper = make_tnum bt 0x123456789ABCDE00L 0x00000000000000FFL in
  let result = TNumBasis.tnum_cast uncertain_upper test_bt_s32 in
  (* After casting to 32 bits, upper uncertainty should be gone *)
  assert_bool "Cast uncertain should not be const" (not (TNumBasis.is_const result));
  assert_equal ~msg:"Cast should preserve lower value bits" 0x9ABCDE00L result.value;
  assert_equal ~msg:"Cast should preserve lower mask bits" 0xFFL result.mask


(** Test tnum_cast preserves uncertainty in lower bits **)
let test_tnum_cast_preserves_lower_uncertainty _ =
  let bt = test_bt_s64 in
  (* Create tnum with uncertainty in lower bits *)
  let uncertain_lower = make_tnum bt 0x1234567800000000L 0x00000000FFFFFFFFL in
  let result = TNumBasis.tnum_cast uncertain_lower test_bt_s32 in
  (* After casting to 32 bits, lower uncertainty should be preserved *)
  assert_bool "Cast should preserve lower uncertainty" (not (TNumBasis.is_const result));
  assert_equal ~msg:"Cast should zero upper value bits" 0x00000000L result.value;
  assert_equal ~msg:"Cast should preserve full lower mask" 0xFFFFFFFFL result.mask


(** Test tnum_cast removes uncertainty in upper bits **)
let test_tnum_cast_removes_upper_uncertainty _ =
  let bt = test_bt_s64 in
  (* Create tnum with uncertainty spanning across cast boundary *)
  let mixed_uncertain = make_tnum bt 0x0000000100000000L 0xFFFFFFFF00000000L in
  let result = TNumBasis.tnum_cast mixed_uncertain test_bt_s32 in
  (* After casting to 32 bits, upper uncertainty should be completely removed *)
  assert_bool
    "Cast should result in zero after removing upper bits"
    (TNumBasis.equals_const result 0L)


(** Test tnum_cast with maximum values **)
let test_tnum_cast_max_values _ =
  let bt = test_bt_s64 in
  (* Test with all bits set *)
  let all_ones = TNumBasis.const bt (-1L) in
  (* 0xFFFFFFFFFFFFFFFF *)
  (* Cast to 1 byte *)
  let result8 = TNumBasis.tnum_cast all_ones test_bt_s8 in
  assert_bool "Max->8 cast should equal 0xFF" (TNumBasis.equals_const result8 0xFFL);
  (* Cast to 2 bytes *)
  let result16 = TNumBasis.tnum_cast all_ones test_bt_s16 in
  assert_bool "Max->16 cast should equal 0xFFFF" (TNumBasis.equals_const result16 0xFFFFL);
  (* Cast to 4 bytes *)
  let result32 = TNumBasis.tnum_cast all_ones test_bt_s32 in
  assert_bool
    "Max->32 cast should equal 0xFFFFFFFF"
    (TNumBasis.equals_const result32 0xFFFFFFFFL)


(** Test tnum_cast with zero - should be identity for value **)
let test_tnum_cast_zero _ =
  let bt = test_bt_s64 in
  let zero = TNumBasis.const bt 0L in
  (* Zero should remain zero regardless of cast size *)
  let result8 = TNumBasis.tnum_cast zero test_bt_s8 in
  let result16 = TNumBasis.tnum_cast zero test_bt_s16 in
  let result32 = TNumBasis.tnum_cast zero test_bt_s32 in
  let result64 = TNumBasis.tnum_cast zero test_bt_s64 in
  assert_bool "Zero cast to 8 should be zero" (TNumBasis.equals_const result8 0L);
  assert_bool "Zero cast to 16 should be zero" (TNumBasis.equals_const result16 0L);
  assert_bool "Zero cast to 32 should be zero" (TNumBasis.equals_const result32 0L);
  assert_bool "Zero cast to 64 should be zero" (TNumBasis.equals_const result64 0L)


(** Test tnum_cast mask computation **)
let test_tnum_cast_mask_computation _ =
  let bt = test_bt_s64 in
  (* Test specific mask patterns *)
  let test_val = make_tnum bt 0xAAAAAAAAAAAAAAAAL 0x5555555555555555L in
  (* Cast to 4 bytes should apply mask 0xFFFFFFFF *)
  let result = TNumBasis.tnum_cast test_val test_bt_s32 in
  assert_equal
    ~msg:"Cast should apply mask to value"
    (Int64.logand 0xAAAAAAAAAAAAAAAAL 0xFFFFFFFFL)
    result.value;
  assert_equal
    ~msg:"Cast should apply mask to mask"
    (Int64.logand 0x5555555555555555L 0xFFFFFFFFL)
    result.mask


(** Test tnum_cast with boundary values **)
let test_tnum_cast_boundary_values _ =
  let bt = test_bt_s64 in
  (* Test value exactly at 32-bit boundary *)
  let boundary_val = TNumBasis.const bt 0x100000000L in
  (* 2^32 *)
  let result = TNumBasis.tnum_cast boundary_val test_bt_s32 in
  assert_bool "Boundary value cast should be zero" (TNumBasis.equals_const result 0L);
  (* Test value just under 32-bit boundary *)
  let under_boundary = TNumBasis.const bt 0xFFFFFFFFL in
  (* 2^32 - 1 *)
  let result2 = TNumBasis.tnum_cast under_boundary test_bt_s32 in
  assert_bool
    "Under boundary cast should preserve value"
    (TNumBasis.equals_const result2 0xFFFFFFFFL)


(** Test tnum_cast with ranges **)
let test_tnum_cast_with_ranges _ =
  let bt = test_bt_s64 in
  (* Create a range that spans across cast boundary *)
  let range_val = TNumBasis.range bt 0xFFFFFFFEL 0x100000001L in
  (* Range spans 32-bit boundary *)
  let result = TNumBasis.tnum_cast range_val test_bt_s32 in
  (* Should preserve uncertainty in lower 32 bits *)
  assert_bool "Range cast should not be const" (not (TNumBasis.is_const result))


(** Test tnum_cast is idempotent for smaller sizes **)
let test_tnum_cast_idempotent _ =
  let bt = test_bt_s32 in
  let val32 = TNumBasis.const bt 0x12345678L in
  (* Casting 32-bit value to 32-bit should be identity *)
  let result32 = TNumBasis.tnum_cast val32 test_bt_s32 in
  assert_tnum_equal ~msg:"32->32 cast should be identity" val32 result32;
  (* Casting 32-bit value to larger size should preserve value but change type *)
  let result64 = TNumBasis.tnum_cast val32 test_bt_s64 in
  assert_bool
    "32->64 cast should preserve value"
    (TNumBasis.equals_const result64 0x12345678L);
  assert_bool
    "32->64 cast should change to target base type"
    (BT.equal test_bt_s64 result64.bt)


(** Test tnum_cast with negative values **)
let test_tnum_cast_negative _ =
  let bt = test_bt_s64 in
  let neg_val = TNumBasis.const bt (-1L) in
  (* 0xFFFFFFFFFFFFFFFF *)
  (* Cast to 32 bits should preserve lower 32 bits *)
  let result = TNumBasis.tnum_cast neg_val test_bt_s32 in
  assert_bool
    "Negative cast should preserve sign bits in lower portion"
    (TNumBasis.equals_const result 0xFFFFFFFFL)


(** Test tnum_cast with top (maximum uncertainty) **)
let test_tnum_cast_with_top _ =
  let bt = test_bt_s64 in
  let top = TNumBasis.top bt in
  let result = TNumBasis.tnum_cast top test_bt_s32 in
  (* Should reduce uncertainty to 32-bit range *)
  assert_bool "top cast should not be const" (not (TNumBasis.is_const result));
  assert_bool "top cast should not be bottom" (not (TNumBasis.is_bottom result));
  assert_equal ~msg:"top cast should have 32-bit mask" 0xFFFFFFFFL result.mask


(** Test tnum_cast edge case: 1-bit cast **)
let test_tnum_cast_single_bit _ =
  let bt = test_bt_s64 in
  (* This is a conceptual test - 1 bit would be size=0.125, but we'll test minimum 1 byte *)
  let val_with_bits = TNumBasis.const bt 0x123456789ABCDEFL in
  let result = TNumBasis.tnum_cast val_with_bits test_bt_s8 in
  (* Should keep only lowest 8 bits *)
  assert_bool "Single byte cast should be const" (TNumBasis.is_const result);
  assert_bool
    "Single byte cast should preserve lowest byte"
    (TNumBasis.equals_const result (Int64.logand 0x123456789ABCDEFL 0xFFL))


(** Test tnum_cast preserves base type **)
let test_tnum_cast_preserves_bt _ =
  let bt = test_bt_s32 in
  let test_val = TNumBasis.const bt 42L in
  let result = TNumBasis.tnum_cast test_val test_bt_s16 in
  assert_bool "Cast should result in target base type" (BT.equal test_bt_s16 result.bt)


(** Property test: tnum_and should be commutative *)
let tnum_and_commutative_property =
  Test.make
    ~count:100
    ~name:"tnum_and should be commutative"
    (pair int64 int64)
    (fun (v1, v2) ->
       let bt = test_bt_s32 in
       let t1 = TNumBasis.const bt v1 in
       let t2 = TNumBasis.const bt v2 in
       let result1 = TNumBasis.tnum_and t1 t2 in
       let result2 = TNumBasis.tnum_and t2 t1 in
       TNumBasis.equal result1 result2)


(** Property test: tnum_and should be associative *)
let tnum_and_associative_property =
  Test.make
    ~count:100
    ~name:"tnum_and should be associative"
    (triple int64 int64 int64)
    (fun (v1, v2, v3) ->
       let bt = test_bt_s32 in
       let t1 = TNumBasis.const bt v1 in
       let t2 = TNumBasis.const bt v2 in
       let t3 = TNumBasis.const bt v3 in
       let result1 = TNumBasis.tnum_and (TNumBasis.tnum_and t1 t2) t3 in
       let result2 = TNumBasis.tnum_and t1 (TNumBasis.tnum_and t2 t3) in
       TNumBasis.equal result1 result2)


(** Property test: tnum_and should be idempotent *)
let tnum_and_idempotent_property =
  Test.make ~count:100 ~name:"tnum_and should be idempotent" int64 (fun v ->
    let bt = test_bt_s32 in
    let t = TNumBasis.const bt v in
    let result = TNumBasis.tnum_and t t in
    TNumBasis.equal t result)


(** Property test: zero should be absorbing element for tnum_and *)
let tnum_and_zero_absorbing_property =
  Test.make ~count:100 ~name:"zero should be absorbing for tnum_and" int64 (fun v ->
    let bt = test_bt_s32 in
    let t = TNumBasis.const bt v in
    let zero = TNumBasis.const bt 0L in
    let result1 = TNumBasis.tnum_and t zero in
    let result2 = TNumBasis.tnum_and zero t in
    TNumBasis.equals_const result1 0L && TNumBasis.equals_const result2 0L)


(** Property test: all-ones should be identity for tnum_and *)
let tnum_and_identity_property =
  Test.make ~count:100 ~name:"all-ones should be identity for tnum_and" int64 (fun v ->
    let bt = test_bt_s32 in
    let t = TNumBasis.const bt v in
    let all_ones = TNumBasis.const bt (-1L) in
    let result1 = TNumBasis.tnum_and t all_ones in
    let result2 = TNumBasis.tnum_and all_ones t in
    TNumBasis.equals_const result1 v && TNumBasis.equals_const result2 v)


(** Property test: constants should satisfy is_const *)
let const_property =
  Test.make ~count:50 ~name:"constants should be is_const" int64 (fun value ->
    let bt = test_bt_s32 in
    let tnum = TNumBasis.const bt value in
    TNumBasis.is_const tnum && TNumBasis.equals_const tnum value)


(** Property test: join should be commutative *)
let join_commutative_property =
  Test.make
    ~count:50
    ~name:"join should be commutative"
    (pair int64 int64)
    (fun (v1, v2) ->
       let bt = test_bt_s32 in
       let t1 = TNumBasis.const bt v1 in
       let t2 = TNumBasis.const bt v2 in
       let join12 = TNumBasis.join t1 t2 in
       let join21 = TNumBasis.join t2 t1 in
       TNumBasis.equal join12 join21)


(** Property test: bitwise operations should be sound *)
let bitwise_soundness_property =
  Test.make
    ~count:50
    ~name:"bitwise operations should be sound"
    (pair int64 int64)
    (fun (v1, v2) ->
       let bt = test_bt_s32 in
       let t1 = TNumBasis.const bt v1 in
       let t2 = TNumBasis.const bt v2 in
       (* AND operation *)
       let and_result = TNumBasis.tnum_and t1 t2 in
       let expected_and = Int64.logand v1 v2 in
       let and_sound = TNumBasis.equals_const and_result expected_and in
       (* OR operation *)
       let or_result = TNumBasis.tnum_or t1 t2 in
       let expected_or = Int64.logor v1 v2 in
       let or_sound = TNumBasis.equals_const or_result expected_or in
       (* XOR operation *)
       let xor_result = TNumBasis.tnum_xor t1 t2 in
       let expected_xor = Int64.logxor v1 v2 in
       let xor_sound = TNumBasis.equals_const xor_result expected_xor in
       and_sound && or_sound && xor_sound)


(** Property test: addition should be sound for constants *)
let add_soundness_property =
  Test.make
    ~count:100
    ~name:"addition should be sound for constants"
    (pair int64 int64)
    (fun (v1, v2) ->
       let bt = test_bt_s32 in
       let t1 = TNumBasis.const bt v1 in
       let t2 = TNumBasis.const bt v2 in
       let add_result = TNumBasis.tnum_add t1 t2 in
       let expected_add = Int64.add v1 v2 in
       TNumBasis.equals_const add_result expected_add)


(** Property test: addition should be commutative *)
let add_commutative_property =
  Test.make
    ~count:50
    ~name:"addition should be commutative"
    (pair int64 int64)
    (fun (v1, v2) ->
       let bt = test_bt_s32 in
       let t1 = TNumBasis.const bt v1 in
       let t2 = TNumBasis.const bt v2 in
       let add12 = TNumBasis.tnum_add t1 t2 in
       let add21 = TNumBasis.tnum_add t2 t1 in
       TNumBasis.equal add12 add21)


(** Property test: addition identity *)
let add_identity_property =
  Test.make ~count:50 ~name:"addition identity" int64 (fun value ->
    let bt = test_bt_s32 in
    let tnum = TNumBasis.const bt value in
    let zero = TNumBasis.const bt 0L in
    let result = TNumBasis.tnum_add tnum zero in
    TNumBasis.equals_const result value)


(** Property test: subtraction should be sound for constants *)
let sub_soundness_property =
  Test.make
    ~count:100
    ~name:"subtraction should be sound for constants"
    (pair int64 int64)
    (fun (v1, v2) ->
       let bt = test_bt_s32 in
       let t1 = TNumBasis.const bt v1 in
       let t2 = TNumBasis.const bt v2 in
       let sub_result = TNumBasis.tnum_sub t1 t2 in
       let expected_sub = Int64.sub v1 v2 in
       TNumBasis.equals_const sub_result expected_sub)


(** Property test: subtraction identity (x - 0 = x) *)
let sub_identity_property =
  Test.make ~count:50 ~name:"subtraction identity" int64 (fun value ->
    let bt = test_bt_s32 in
    let tnum = TNumBasis.const bt value in
    let zero = TNumBasis.const bt 0L in
    let result = TNumBasis.tnum_sub tnum zero in
    TNumBasis.equals_const result value)


(** Property test: subtraction self (x - x = 0) *)
let sub_self_property =
  Test.make ~count:50 ~name:"subtraction self" int64 (fun value ->
    let bt = test_bt_s32 in
    let tnum = TNumBasis.const bt value in
    let result = TNumBasis.tnum_sub tnum tnum in
    TNumBasis.equals_const result 0L)


(** Property test: addition and subtraction inverse relation *)
let add_sub_inverse_property =
  Test.make
    ~count:50
    ~name:"addition and subtraction inverse"
    (pair int64 int64)
    (fun (v1, v2) ->
       let bt = test_bt_s32 in
       let t1 = TNumBasis.const bt v1 in
       let t2 = TNumBasis.const bt v2 in
       let sum = TNumBasis.tnum_add t1 t2 in
       let diff = TNumBasis.tnum_sub sum t2 in
       TNumBasis.equals_const diff v1)


(** Property test: multiplication should be sound for constants *)
let mul_soundness_property =
  Test.make
    ~count:100
    ~name:"multiplication should be sound for constants"
    (pair int64 int64)
    (fun (v1, v2) ->
       let bt = test_bt_s32 in
       let t1 = TNumBasis.const bt v1 in
       let t2 = TNumBasis.const bt v2 in
       let mul_result = TNumBasis.tnum_mul t1 t2 in
       let expected_mul = Int64.mul v1 v2 in
       TNumBasis.equals_const mul_result expected_mul)


(** Property test: multiplication should be commutative *)
let mul_commutative_property =
  Test.make
    ~count:50
    ~name:"multiplication should be commutative"
    (pair int64 int64)
    (fun (v1, v2) ->
       let bt = test_bt_s32 in
       let t1 = TNumBasis.const bt v1 in
       let t2 = TNumBasis.const bt v2 in
       let mul12 = TNumBasis.tnum_mul t1 t2 in
       let mul21 = TNumBasis.tnum_mul t2 t1 in
       TNumBasis.equal mul12 mul21)


(** Property test: multiplication should be associative for constants *)
let mul_associative_property =
  Test.make
    ~count:50
    ~name:"multiplication should be associative"
    (triple int64 int64 int64)
    (fun (v1, v2, v3) ->
       let bt = test_bt_s32 in
       let t1 = TNumBasis.const bt v1 in
       let t2 = TNumBasis.const bt v2 in
       let t3 = TNumBasis.const bt v3 in
       let result1 = TNumBasis.tnum_mul (TNumBasis.tnum_mul t1 t2) t3 in
       let result2 = TNumBasis.tnum_mul t1 (TNumBasis.tnum_mul t2 t3) in
       TNumBasis.equal result1 result2)


(** Property test: multiplication identity (x * 1 = x) *)
let mul_identity_property =
  Test.make ~count:50 ~name:"multiplication identity" int64 (fun value ->
    let bt = test_bt_s32 in
    let tnum = TNumBasis.const bt value in
    let one = TNumBasis.const bt 1L in
    let result = TNumBasis.tnum_mul tnum one in
    TNumBasis.equals_const result value)


(** Property test: zero should be absorbing element for multiplication *)
let mul_zero_absorbing_property =
  Test.make ~count:50 ~name:"zero should be absorbing for multiplication" int64 (fun v ->
    let bt = test_bt_s32 in
    let t = TNumBasis.const bt v in
    let zero = TNumBasis.const bt 0L in
    let result1 = TNumBasis.tnum_mul t zero in
    let result2 = TNumBasis.tnum_mul zero t in
    TNumBasis.equals_const result1 0L && TNumBasis.equals_const result2 0L)


(** Property test: multiplication distributes over addition *)
let mul_distributive_property =
  Test.make
    ~count:30
    ~name:"multiplication distributes over addition"
    (triple int64 int64 int64)
    (fun (a, b, c) ->
       let bt = test_bt_s32 in
       let ta = TNumBasis.const bt a in
       let tb = TNumBasis.const bt b in
       let tc = TNumBasis.const bt c in
       (* Test a * (b + c) = (a * b) + (a * c) *)
       let bc_sum = TNumBasis.tnum_add tb tc in
       let left_side = TNumBasis.tnum_mul ta bc_sum in
       let ab = TNumBasis.tnum_mul ta tb in
       let ac = TNumBasis.tnum_mul ta tc in
       let right_side = TNumBasis.tnum_add ab ac in
       TNumBasis.equal left_side right_side)


(** Property test: leq should be reflexive *)
let leq_reflexive_property =
  Test.make ~count:50 ~name:"leq should be reflexive" int64 (fun value ->
    let bt = test_bt_s32 in
    let tnum = TNumBasis.const bt value in
    TNumBasis.leq tnum tnum)


(** Property test: tnum_cast should preserve constants for non-truncating casts **)
let tnum_cast_preserves_constants_property =
  Test.make
    ~count:100
    ~name:"tnum_cast should preserve constants for non-truncating casts"
    int64
    (fun value ->
       let bt = test_bt_s64 in
       let tnum = TNumBasis.const bt value in
       (* Cast to 8 bytes (64 bits) should be identity *)
       let result = TNumBasis.tnum_cast tnum test_bt_s64 in
       TNumBasis.equals_const result value)


(** Property test: tnum_cast should be sound for constants **)
let tnum_cast_soundness_property =
  Test.make
    ~count:100
    ~name:"tnum_cast should be sound for constants"
    (pair int64 (int_range 1 8))
    (fun (value, size) ->
       let bt = test_bt_s64 in
       let tnum = TNumBasis.const bt value in
       let target_bt = size_to_signed_bt size in
       let result = TNumBasis.tnum_cast tnum target_bt in
       (* Create expected mask based on actual target bit width *)
       let target_bit_width = bt_to_bit_width target_bt in
       let expected_value =
         if target_bit_width >= 64 then
           value
         else (
           let expected_mask = Int64.sub (Int64.shift_left 1L target_bit_width) 1L in
           Int64.logand value expected_mask)
       in
       TNumBasis.equals_const result expected_value)


(** Property test: tnum_cast should be idempotent for same size **)
let tnum_cast_idempotent_property =
  Test.make
    ~count:50
    ~name:"tnum_cast should be idempotent for same size"
    (pair int64 (int_range 1 8))
    (fun (value, size) ->
       let bt = test_bt_s64 in
       let tnum = TNumBasis.const bt value in
       let cast_once = TNumBasis.tnum_cast tnum (size_to_signed_bt size) in
       let cast_twice = TNumBasis.tnum_cast cast_once (size_to_signed_bt size) in
       TNumBasis.equal cast_once cast_twice)


(** Property test: tnum_cast should be monotonic (smaller cast = larger cast followed by smaller cast) **)
let tnum_cast_monotonic_property =
  Test.make
    ~count:50
    ~name:"tnum_cast should be monotonic"
    (triple int64 (int_range 1 8) (int_range 1 8))
    (fun (value, size1, size2) ->
       let bt = test_bt_s64 in
       let tnum = TNumBasis.const bt value in
       let min_size = min size1 size2 in
       let max_size = max size1 size2 in
       (* Cast to smaller size directly *)
       let direct_cast = TNumBasis.tnum_cast tnum (size_to_signed_bt min_size) in
       (* Cast to larger size then to smaller size *)
       let intermediate = TNumBasis.tnum_cast tnum (size_to_signed_bt max_size) in
       let indirect_cast =
         TNumBasis.tnum_cast intermediate (size_to_signed_bt min_size)
       in
       TNumBasis.equal direct_cast indirect_cast)


(** Property test: tnum_cast with zero should always result in zero **)
let tnum_cast_zero_property =
  Test.make
    ~count:50
    ~name:"tnum_cast with zero should always result in zero"
    (int_range 1 8)
    (fun size ->
       let bt = test_bt_s64 in
       let zero = TNumBasis.const bt 0L in
       let result = TNumBasis.tnum_cast zero (size_to_signed_bt size) in
       TNumBasis.equals_const result 0L)


(** Property test: tnum_cast should preserve base type **)
let tnum_cast_preserves_bt_property =
  Test.make
    ~count:50
    ~name:"tnum_cast should preserve base type"
    (pair int64 (int_range 1 8))
    (fun (value, size) ->
       let bt = test_bt_s32 in
       let tnum = TNumBasis.const bt value in
       let target_bt = size_to_signed_bt size in
       let result = TNumBasis.tnum_cast tnum target_bt in
       BT.equal target_bt result.bt)


(** Property test: larger cast sizes should preserve smaller cast results **)
let tnum_cast_size_preservation_property =
  Test.make
    ~count:50
    ~name:"larger cast sizes should preserve smaller cast results"
    (triple int64 (int_range 1 4) (int_range 5 8))
    (fun (value, small_size, large_size) ->
       let bt = test_bt_s64 in
       let tnum = TNumBasis.const bt value in
       (* Cast to small size first *)
       let small_cast = TNumBasis.tnum_cast tnum (size_to_signed_bt small_size) in
       (* Cast original to large size *)
       let large_cast = TNumBasis.tnum_cast tnum (size_to_signed_bt large_size) in
       (* Cast large result to small size *)
       let large_then_small =
         TNumBasis.tnum_cast large_cast (size_to_signed_bt small_size)
       in
       TNumBasis.equal small_cast large_then_small)


(** Property test: tnum_lshift should be sound for constants **)
let tnum_lshift_soundness_property =
  Test.make
    ~count:100
    ~name:"tnum_lshift should be sound for constants"
    (pair int64 (int_range 0 31))
    (fun (value, shift) ->
       let bt = test_bt_s32 in
       let tnum = TNumBasis.const bt value in
       let result = TNumBasis.tnum_lshift tnum shift in
       let expected = Int64.shift_left value shift in
       TNumBasis.equals_const result expected)


(** Property test: tnum_lshift should preserve zero **)
let tnum_lshift_zero_property =
  Test.make
    ~count:50
    ~name:"tnum_lshift should preserve zero"
    (int_range 0 31)
    (fun shift ->
       let bt = test_bt_s32 in
       let zero = TNumBasis.const bt 0L in
       let result = TNumBasis.tnum_lshift zero shift in
       TNumBasis.equals_const result 0L)


(** Property test: tnum_lshift identity (x << 0 = x) **)
let tnum_lshift_identity_property =
  Test.make ~count:50 ~name:"tnum_lshift identity" int64 (fun value ->
    let bt = test_bt_s32 in
    let tnum = TNumBasis.const bt value in
    let result = TNumBasis.tnum_lshift tnum 0 in
    TNumBasis.equals_const result value)


(** Property test: tnum_lshift associative for constants **)
let tnum_lshift_associative_property =
  Test.make
    ~count:50
    ~name:"tnum_lshift should be associative"
    (triple int64 (int_range 0 15) (int_range 0 15))
    (fun (value, shift1, shift2) ->
       let bt = test_bt_s32 in
       let tnum = TNumBasis.const bt value in
       (* Test (x << a) << b == x << (a + b) *)
       let left_result =
         TNumBasis.tnum_lshift (TNumBasis.tnum_lshift tnum shift1) shift2
       in
       let right_result = TNumBasis.tnum_lshift tnum (shift1 + shift2) in
       TNumBasis.equal left_result right_result)


(** Property test: tnum_lshift should preserve base type **)
let tnum_lshift_preserves_bt_property =
  Test.make
    ~count:50
    ~name:"tnum_lshift should preserve base type"
    (pair int64 (int_range 0 31))
    (fun (value, shift) ->
       let bt = test_bt_s32 in
       let tnum = TNumBasis.const bt value in
       let result = TNumBasis.tnum_lshift tnum shift in
       BT.equal bt result.bt)


(** Property test: tnum_lshift should be equivalent to multiplication by powers of 2 **)
let tnum_lshift_mult_equiv_property =
  Test.make
    ~count:50
    ~name:"tnum_lshift should be equivalent to multiplication by powers of 2"
    (pair int64 (int_range 0 10))
    (fun (value, shift) ->
       let bt = test_bt_s32 in
       let tnum = TNumBasis.const bt value in
       let shift_result = TNumBasis.tnum_lshift tnum shift in
       let mult_factor = Int64.shift_left 1L shift in
       let mult_result = TNumBasis.tnum_mul tnum (TNumBasis.const bt mult_factor) in
       TNumBasis.equal shift_result mult_result)


(** Property test: tnum_rshift should be sound for constants - signed **)
let tnum_rshift_soundness_property_signed =
  Test.make
    ~count:100
    ~name:"tnum_rshift should be sound for constants (signed)"
    (pair int64 (int_range 0 31))
    (fun (value, shift) ->
       let bt = test_bt_s32 in
       let tnum = TNumBasis.const bt value in
       let result = TNumBasis.tnum_rshift tnum shift in
       let expected = Int64.shift_right value shift in
       TNumBasis.equals_const result expected)


(** Property test: tnum_rshift should be sound for constants - unsigned **)
let tnum_rshift_soundness_property_unsigned =
  Test.make
    ~count:100
    ~name:"tnum_rshift should be sound for constants (unsigned)"
    (pair int64 (int_range 0 31))
    (fun (value, shift) ->
       let bt = BT.Bits (BT.Unsigned, 32) in
       let tnum = TNumBasis.const bt value in
       let result = TNumBasis.tnum_rshift tnum shift in
       let expected = Int64.shift_right_logical value shift in
       TNumBasis.equals_const result expected)


(** Property test: tnum_rshift should preserve zero **)
let tnum_rshift_zero_property =
  Test.make
    ~count:50
    ~name:"tnum_rshift should preserve zero"
    (int_range 0 31)
    (fun shift ->
       let bt = test_bt_s32 in
       let zero = TNumBasis.const bt 0L in
       let result = TNumBasis.tnum_rshift zero shift in
       TNumBasis.equals_const result 0L)


(** Property test: tnum_rshift identity (x >> 0 = x) **)
let tnum_rshift_identity_property =
  Test.make ~count:50 ~name:"tnum_rshift identity" int64 (fun value ->
    let bt = test_bt_s32 in
    let tnum = TNumBasis.const bt value in
    let result = TNumBasis.tnum_rshift tnum 0 in
    TNumBasis.equals_const result value)


(** Property test: tnum_rshift should preserve base type **)
let tnum_rshift_preserves_bt_property =
  Test.make
    ~count:50
    ~name:"tnum_rshift should preserve base type"
    (pair int64 (int_range 0 31))
    (fun (value, shift) ->
       let bt = test_bt_s32 in
       let tnum = TNumBasis.const bt value in
       let result = TNumBasis.tnum_rshift tnum shift in
       BT.equal (TNumBasis.bt result) bt)


(** Property test: tnum_rshift followed by lshift should be idempotent for powers of 2 **)
let tnum_rshift_lshift_idempotent_property =
  Test.make
    ~count:50
    ~name:"tnum_rshift followed by lshift should be idempotent for aligned values"
    (pair int64 (int_range 0 10))
    (fun (value, shift) ->
       let bt = test_bt_s32 in
       (* Create value aligned to shift boundary *)
       let aligned_value =
         Int64.logand value (Int64.lognot (Int64.sub (Int64.shift_left 1L shift) 1L))
       in
       let tnum = TNumBasis.const bt aligned_value in
       let rshift_result = TNumBasis.tnum_rshift tnum shift in
       let lshift_result = TNumBasis.tnum_lshift rshift_result shift in
       TNumBasis.equals_const lshift_result aligned_value)


(** Unit Tests *)
let unit_tests =
  "TNum Basis Unit Tests"
  >::: [ "basic creation" >:: test_basic_creation;
         "bitwise and" >:: test_bitwise_and;
         "bitwise or" >:: test_bitwise_or;
         "bitwise xor" >:: test_bitwise_xor;
         "range construction" >:: test_range;
         "lattice join" >:: test_join;
         "lattice meet" >:: test_meet;
         "subset relation" >:: test_leq;
         "alignment predicate" >:: test_alignment;
         "of_interval constructor" >:: test_of_interval;
         "uncertain operations" >:: test_uncertain_operations;
         "tnum add constants" >:: test_tnum_add_constants;
         "tnum add uncertain" >:: test_tnum_add_uncertain;
         "tnum add carry" >:: test_tnum_add_carry;
         "tnum add identity" >:: test_tnum_add_identity;
         "tnum sub constants" >:: test_tnum_sub_constants;
         "tnum sub uncertain" >:: test_tnum_sub_uncertain;
         "tnum sub underflow" >:: test_tnum_sub_underflow;
         "tnum sub identity" >:: test_tnum_sub_identity;
         "tnum sub self" >:: test_tnum_sub_self;
         "tnum sub edge cases" >:: test_tnum_sub_edge_cases;
         "tnum sub range" >:: test_tnum_sub_range;
         (* ===== COMPREHENSIVE tnum_mul TESTS ===== *)
         "tnum_mul constants" >:: test_tnum_mul_constants;
         "tnum_mul with zero" >:: test_tnum_mul_zero;
         "tnum_mul with one" >:: test_tnum_mul_one;
         "tnum_mul power of 2" >:: test_tnum_mul_power_of_2;
         "tnum_mul commutative" >:: test_tnum_mul_commutative;
         "tnum_mul uncertain multiplier" >:: test_tnum_mul_uncertain_multiplier;
         "tnum_mul uncertain multiplicand" >:: test_tnum_mul_uncertain_multiplicand;
         "tnum_mul both uncertain" >:: test_tnum_mul_both_uncertain;
         "tnum_mul algorithm verification" >:: test_tnum_mul_algorithm_verification;
         "tnum_mul large values" >:: test_tnum_mul_large_values;
         "tnum_mul negative" >:: test_tnum_mul_negative;
         "tnum_mul range" >:: test_tnum_mul_range;
         "tnum_mul small uncertainty" >:: test_tnum_mul_small_uncertainty;
         "tnum_mul associative constants" >:: test_tnum_mul_associative_constants;
         "tnum_mul distributive" >:: test_tnum_mul_distributive;
         "tnum_mul overflow" >:: test_tnum_mul_overflow;
         "tnum_mul with top" >:: test_tnum_mul_with_top;
         "tnum_mul with bottom" >:: test_tnum_mul_with_bottom;
         (* ===== COMPREHENSIVE tnum_lshift TESTS ===== *)
         "tnum_lshift constants" >:: test_tnum_lshift_constants;
         "tnum_lshift zero value" >:: test_tnum_lshift_zero_value;
         "tnum_lshift zero shift" >:: test_tnum_lshift_zero_shift;
         "tnum_lshift power of 2 equiv" >:: test_tnum_lshift_power_of_2_equiv;
         "tnum_lshift uncertain" >:: test_tnum_lshift_uncertain;
         "tnum_lshift range" >:: test_tnum_lshift_range;
         "tnum_lshift preserves pattern" >:: test_tnum_lshift_preserves_pattern;
         "tnum_lshift large shifts" >:: test_tnum_lshift_large_shifts;
         "tnum_lshift negative" >:: test_tnum_lshift_negative;
         "tnum_lshift chain" >:: test_tnum_lshift_chain;
         "tnum_lshift max uncertainty" >:: test_tnum_lshift_max_uncertainty;
         "tnum_lshift bit boundaries" >:: test_tnum_lshift_bit_boundaries;
         "tnum_lshift preserves bt" >:: test_tnum_lshift_preserves_bt;
         "tnum_lshift max shift" >:: test_tnum_lshift_max_shift;
         (* ===== COMPREHENSIVE tnum_arshift TESTS ===== *)
         "tnum_arshift 32-bit constants" >:: test_tnum_arshift_32bit_constants;
         "tnum_arshift 64-bit constants" >:: test_tnum_arshift_64bit_constants;
         "tnum_arshift 32-bit negative" >:: test_tnum_arshift_32bit_negative;
         "tnum_arshift 64-bit negative" >:: test_tnum_arshift_64bit_negative;
         "tnum_arshift 32-bit zero" >:: test_tnum_arshift_32bit_zero;
         "tnum_arshift 64-bit zero" >:: test_tnum_arshift_64bit_zero;
         "tnum_arshift identity" >:: test_tnum_arshift_identity;
         "tnum_arshift sign extension" >:: test_tnum_arshift_sign_extension;
         "tnum_arshift preserves bt" >:: test_tnum_arshift_preserves_bt;
         "tnum_arshift large shifts" >:: test_tnum_arshift_large_shifts;
         "tnum_arshift uncertain values" >:: test_tnum_arshift_uncertain;
         "tnum_arshift bit patterns" >:: test_tnum_arshift_bit_patterns;
         (* ===== COMPREHENSIVE tnum_and TESTS ===== *)
         "tnum_and with zero" >:: test_tnum_and_zero;
         "tnum_and with all-ones" >:: test_tnum_and_all_ones;
         "tnum_and commutative" >:: test_tnum_and_commutative;
         "tnum_and associative" >:: test_tnum_and_associative;
         "tnum_and idempotent" >:: test_tnum_and_idempotent;
         "tnum_and uncertain algorithm" >:: test_tnum_and_uncertain_algorithm;
         "tnum_and partial overlap" >:: test_tnum_and_partial_overlap;
         "tnum_and no uncertainty" >:: test_tnum_and_no_uncertainty;
         "tnum_and large ranges" >:: test_tnum_and_large_ranges;
         "tnum_and range constant" >:: test_tnum_and_range_constant;
         "tnum_and top vs const" >:: test_tnum_and_top_vs_const;
         "tnum_and with bottom" >:: test_tnum_and_with_bottom;
         "tnum_and manual verification" >:: test_tnum_and_manual_verification;
         "tnum_and different patterns" >:: test_tnum_and_different_patterns;
         (* ===== COMPREHENSIVE tnum_cast TESTS ===== *)
         "tnum_cast constants" >:: test_tnum_cast_constants;
         "tnum_cast different sizes" >:: test_tnum_cast_different_sizes;
         "tnum_cast uncertain" >:: test_tnum_cast_uncertain;
         "tnum_cast preserves lower uncertainty"
         >:: test_tnum_cast_preserves_lower_uncertainty;
         "tnum_cast removes upper uncertainty"
         >:: test_tnum_cast_removes_upper_uncertainty;
         "tnum_cast max values" >:: test_tnum_cast_max_values;
         "tnum_cast zero" >:: test_tnum_cast_zero;
         "tnum_cast mask computation" >:: test_tnum_cast_mask_computation;
         "tnum_cast boundary values" >:: test_tnum_cast_boundary_values;
         "tnum_cast with ranges" >:: test_tnum_cast_with_ranges;
         "tnum_cast idempotent" >:: test_tnum_cast_idempotent;
         "tnum_cast negative" >:: test_tnum_cast_negative;
         "tnum_cast with top" >:: test_tnum_cast_with_top;
         "tnum_cast single bit" >:: test_tnum_cast_single_bit;
         "tnum_cast preserves bt" >:: test_tnum_cast_preserves_bt
       ]


(** Property Tests *)
let property_tests =
  "TNum Basis Property Tests"
  >::: [ QCheck_ounit.to_ounit2_test const_property;
         QCheck_ounit.to_ounit2_test join_commutative_property;
         QCheck_ounit.to_ounit2_test bitwise_soundness_property;
         QCheck_ounit.to_ounit2_test leq_reflexive_property;
         QCheck_ounit.to_ounit2_test add_soundness_property;
         QCheck_ounit.to_ounit2_test add_commutative_property;
         QCheck_ounit.to_ounit2_test add_identity_property;
         QCheck_ounit.to_ounit2_test sub_soundness_property;
         QCheck_ounit.to_ounit2_test sub_identity_property;
         QCheck_ounit.to_ounit2_test sub_self_property;
         QCheck_ounit.to_ounit2_test add_sub_inverse_property;
         (* ===== tnum_mul PROPERTY TESTS ===== *)
         QCheck_ounit.to_ounit2_test mul_soundness_property;
         QCheck_ounit.to_ounit2_test mul_commutative_property;
         QCheck_ounit.to_ounit2_test mul_associative_property;
         QCheck_ounit.to_ounit2_test mul_identity_property;
         QCheck_ounit.to_ounit2_test mul_zero_absorbing_property;
         QCheck_ounit.to_ounit2_test mul_distributive_property;
         (* ===== tnum_and PROPERTY TESTS ===== *)
         QCheck_ounit.to_ounit2_test tnum_and_commutative_property;
         QCheck_ounit.to_ounit2_test tnum_and_associative_property;
         QCheck_ounit.to_ounit2_test tnum_and_idempotent_property;
         QCheck_ounit.to_ounit2_test tnum_and_zero_absorbing_property;
         QCheck_ounit.to_ounit2_test tnum_and_identity_property;
         (* ===== tnum_cast PROPERTY TESTS ===== *)
         QCheck_ounit.to_ounit2_test tnum_cast_preserves_constants_property;
         QCheck_ounit.to_ounit2_test tnum_cast_soundness_property;
         QCheck_ounit.to_ounit2_test tnum_cast_idempotent_property;
         QCheck_ounit.to_ounit2_test tnum_cast_monotonic_property;
         QCheck_ounit.to_ounit2_test tnum_cast_zero_property;
         QCheck_ounit.to_ounit2_test tnum_cast_preserves_bt_property;
         QCheck_ounit.to_ounit2_test tnum_cast_size_preservation_property;
         (* ===== tnum_lshift PROPERTY TESTS ===== *)
         QCheck_ounit.to_ounit2_test tnum_lshift_soundness_property;
         QCheck_ounit.to_ounit2_test tnum_lshift_zero_property;
         QCheck_ounit.to_ounit2_test tnum_lshift_identity_property;
         QCheck_ounit.to_ounit2_test tnum_lshift_associative_property;
         QCheck_ounit.to_ounit2_test tnum_lshift_preserves_bt_property;
         QCheck_ounit.to_ounit2_test tnum_lshift_mult_equiv_property;
         (* ===== tnum_rshift PROPERTY TESTS ===== *)
         QCheck_ounit.to_ounit2_test tnum_rshift_soundness_property_signed;
         QCheck_ounit.to_ounit2_test tnum_rshift_soundness_property_unsigned;
         QCheck_ounit.to_ounit2_test tnum_rshift_zero_property;
         QCheck_ounit.to_ounit2_test tnum_rshift_identity_property;
         QCheck_ounit.to_ounit2_test tnum_rshift_preserves_bt_property;
         QCheck_ounit.to_ounit2_test tnum_rshift_lshift_idempotent_property
       ]


(** Test forward_abs_binop ShiftLeft integration **)
let test_forward_abs_binop_shiftleft _ =
  let bt = test_bt_s32 in
  (* Test x << 2 where x is constant 5 *)
  let x_val = TNumBasis.const bt 5L in
  let shift_val = TNumBasis.const bt 2L in
  let result = TNumBasis.forward_abs_binop IT.ShiftLeft x_val shift_val in
  match result with
  | Some res ->
    assert_bool "5 << 2 should be const" (TNumBasis.is_const res);
    assert_bool "5 << 2 should equal 20" (TNumBasis.equals_const res 20L)
  | None -> assert_failure "ShiftLeft should return a result"


(** Test forward_abs_binop ShiftLeft with non-constant shift **)
let test_forward_abs_binop_shiftleft_nonconst _ =
  let bt = test_bt_s32 in
  let x_val = TNumBasis.const bt 5L in
  let shift_val = TNumBasis.range bt 1L 3L in
  (* Non-constant shift *)
  let result = TNumBasis.forward_abs_binop IT.ShiftLeft x_val shift_val in
  match result with
  | Some res ->
    assert_bool "Non-constant shift should result in top" (TNumBasis.is_top res)
  | None -> assert_failure "ShiftLeft should return a result"


(** Test forward_abs_binop ShiftLeft with large shift **)
let test_forward_abs_binop_shiftleft_large _ =
  let bt = test_bt_s32 in
  let x_val = TNumBasis.const bt 5L in
  let large_shift = TNumBasis.const bt 70L in
  (* Shift > 64 *)
  let result = TNumBasis.forward_abs_binop IT.ShiftLeft x_val large_shift in
  match result with
  | Some res -> assert_bool "Large shift should result in top" (TNumBasis.is_top res)
  | None -> assert_failure "ShiftLeft should return a result"


(** Test forward_abs_binop ShiftRight integration - signed **)
let test_forward_abs_binop_shiftright _ =
  let bt = test_bt_s32 in
  (* Test x >> 2 where x is constant 20 (signed arithmetic shift) *)
  let x_val = TNumBasis.const bt 20L in
  let shift_val = TNumBasis.const bt 2L in
  let result = TNumBasis.forward_abs_binop IT.ShiftRight x_val shift_val in
  match result with
  | Some res ->
    assert_bool "20 >> 2 should be const" (TNumBasis.is_const res);
    assert_bool "20 >> 2 should equal 5" (TNumBasis.equals_const res 5L)
  | None -> assert_failure "ShiftRight should return a result"


(** Test forward_abs_binop ShiftRight integration - unsigned **)
let test_forward_abs_binop_shiftright_unsigned _ =
  let bt = BT.Bits (BT.Unsigned, 32) in
  (* Test x >> 2 where x is constant 20 (unsigned logical shift) *)
  let x_val = TNumBasis.const bt 20L in
  let shift_val = TNumBasis.const bt 2L in
  let result = TNumBasis.forward_abs_binop IT.ShiftRight x_val shift_val in
  match result with
  | Some res ->
    assert_bool "20u >> 2 should be const" (TNumBasis.is_const res);
    assert_bool "20u >> 2 should equal 5" (TNumBasis.equals_const res 5L)
  | None -> assert_failure "ShiftRight should return a result"


(** Test forward_abs_binop ShiftRight with negative values - signed **)
let test_forward_abs_binop_shiftright_negative _ =
  let bt = test_bt_s32 in
  (* Test -8 >> 2 (arithmetic shift preserves sign) *)
  let x_val = TNumBasis.const bt (-8L) in
  let shift_val = TNumBasis.const bt 2L in
  let result = TNumBasis.forward_abs_binop IT.ShiftRight x_val shift_val in
  match result with
  | Some res ->
    assert_bool "-8 >> 2 should be const" (TNumBasis.is_const res);
    assert_bool "-8 >> 2 should equal -2" (TNumBasis.equals_const res (-2L))
  | None -> assert_failure "ShiftRight should return a result"


(** Test forward_abs_binop ShiftRight with non-constant shift **)
let test_forward_abs_binop_shiftright_nonconst _ =
  let bt = test_bt_s32 in
  let x_val = TNumBasis.const bt 20L in
  let shift_val = TNumBasis.range bt 1L 3L in
  (* Non-constant shift *)
  let result = TNumBasis.forward_abs_binop IT.ShiftRight x_val shift_val in
  match result with
  | Some res ->
    assert_bool "Non-constant shift should result in top" (TNumBasis.is_top res)
  | None -> assert_failure "ShiftRight should return a result"


(** Test forward_abs_binop ShiftRight with large shift **)
let test_forward_abs_binop_shiftright_large _ =
  let bt = test_bt_s32 in
  let x_val = TNumBasis.const bt 20L in
  let large_shift = TNumBasis.const bt 70L in
  (* Shift > 64 *)
  let result = TNumBasis.forward_abs_binop IT.ShiftRight x_val large_shift in
  match result with
  | Some res -> assert_bool "Large shift should result in top" (TNumBasis.is_top res)
  | None -> assert_failure "ShiftRight should return a result"


(** Test forward_abs_binop ShiftRight with zero shift **)
let test_forward_abs_binop_shiftright_zero _ =
  let bt = test_bt_s32 in
  let x_val = TNumBasis.const bt 42L in
  let zero_shift = TNumBasis.const bt 0L in
  let result = TNumBasis.forward_abs_binop IT.ShiftRight x_val zero_shift in
  match result with
  | Some res ->
    assert_bool "x >> 0 should be const" (TNumBasis.is_const res);
    assert_bool "x >> 0 should equal x" (TNumBasis.equals_const res 42L)
  | None -> assert_failure "ShiftRight should return a result"


(** Test domain integration via NonRelational functor *)
let test_domain_integration _ =
  let x = Sym.fresh "x" in
  let bt = test_bt_s32 in
  (* Create domain with x mapped to constant 42 *)
  let domain = Some (Sym.Map.singleton x (TNumBasis.const bt 42L)) in
  (* Test relative_to *)
  let relative = TNumDomain.relative_to x bt domain in
  assert_bool "Relative should be const" (TNumBasis.is_const relative);
  assert_bool "Relative should equal 42" (TNumBasis.equals_const relative 42L)


let test_domain_join _ =
  let x = Sym.fresh "x" in
  let y = Sym.fresh "y" in
  let bt = test_bt_s32 in
  let domain1 = Some (Sym.Map.singleton x (TNumBasis.const bt 8L)) in
  let domain2 = Some (Sym.Map.singleton y (TNumBasis.const bt 16L)) in
  let joined = TNumDomain.join domain1 domain2 in
  (* Should result in empty domain since no common variables *)
  match joined with
  | Some map -> assert_bool "Joined domain should be empty" (Sym.Map.is_empty map)
  | None -> assert_failure "Join should not produce bottom"


let test_domain_meet _ =
  let x = Sym.fresh "x" in
  let bt = test_bt_s32 in
  let domain1 = Some (Sym.Map.singleton x (TNumBasis.const bt 8L)) in
  let domain2 = Some (Sym.Map.singleton x (TNumBasis.range bt 8L 15L)) in
  let meet_result = TNumDomain.meet domain1 domain2 in
  match meet_result with
  | Some map ->
    (match Sym.Map.find_opt x map with
     | Some tnum -> assert_bool "Meet should preserve constant" (TNumBasis.is_const tnum)
     | None -> assert_failure "Meet should preserve variable x")
  | None -> assert_failure "Meet should not produce bottom"


(** Domain Integration Tests *)
let domain_tests =
  "TNum Domain Integration Tests"
  >::: [ "domain relative_to" >:: test_domain_integration;
         "domain join" >:: test_domain_join;
         "domain meet" >:: test_domain_meet;
         "forward_abs_binop ShiftLeft" >:: test_forward_abs_binop_shiftleft;
         "forward_abs_binop ShiftLeft nonconst"
         >:: test_forward_abs_binop_shiftleft_nonconst;
         "forward_abs_binop ShiftLeft large" >:: test_forward_abs_binop_shiftleft_large;
         "forward_abs_binop ShiftRight" >:: test_forward_abs_binop_shiftright;
         "forward_abs_binop ShiftRight unsigned"
         >:: test_forward_abs_binop_shiftright_unsigned;
         "forward_abs_binop ShiftRight negative"
         >:: test_forward_abs_binop_shiftright_negative;
         "forward_abs_binop ShiftRight nonconst"
         >:: test_forward_abs_binop_shiftright_nonconst;
         "forward_abs_binop ShiftRight large" >:: test_forward_abs_binop_shiftright_large;
         "forward_abs_binop ShiftRight zero" >:: test_forward_abs_binop_shiftright_zero
       ]


let suite =
  "TNum (Tristate Numbers) Tests" >::: [ unit_tests; property_tests; domain_tests ]

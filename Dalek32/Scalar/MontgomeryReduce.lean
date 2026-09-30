/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Aeneas.Command.Decompose
import Dalek32.Auxiliary
import Dalek32.Constants.L
import Dalek32.Constants.Lfactor
import Dalek32.Lint.Basic
import Dalek32.Scalar.Index
import Dalek32.Scalar.M
import Dalek32.Scalar.Sub
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Spec theorem for `montgomery_reduce`

Montgomery reduction of seventeen radix-`2^29` coefficients.
Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 328-369.

The generated function is one long straight-line computation, so `#decompose` splits it into

* `montgomery_reduce_adjust`, the nine `part1` rows that produce the Montgomery quotient
  digits `n0, …, n8` and cancel the low nine radix digits, and
* `montgomery_reduce_extract`, the eight `part2` rows that read off the result digits
  `r0, …, r7` and the top carry.

Each half is verified against its own half of the Montgomery identity
(`adjust_identity` and `extract_identity`); `montgomery_reduce_spec` multiplies the second
by `limbRadix ^ 9`, adds the first, and finishes with the usual conditional subtraction.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

/-- Indexing a fixed-size array below its bound always succeeds.

Note: `Dalek32/Scalar/SquareInternal.lean` declares a private lemma of the same name for
`Insts.CoreOpsIndexIndexUsizeU32.index` on `Scalar29`; the two are different statements and
both are local to their file. -/
private theorem index_eq {α : Type} [Inhabited α] {size : Usize}
    (a : Array α size) (i : Usize) (hi : i.val < size.val) :
    Array.index_usize a i = ok a[i.val]! := by
  obtain ⟨result, h_eq, h_result⟩ := spec_imp_exists
    (Array.index_usize_spec a i (by simpa only [Array.length_eq] using hi))
  grind [Array.getElem!_Nat_eq]

namespace montgomery_reduce

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_reduce::part1`**

Cancels the low radix digit and returns the exact carry. -/
@[step]
theorem part1_spec (sum : U64) (h_sum : sum.val < 2 ^ 63 + 2 ^ 61) :
    part1 sum ⦃ (carry : U64) (p : U32) =>
      p.val < limbRadix ∧
      carry.val < 2 ^ 35 ∧
      carry.val * limbRadix = sum.val + p.val * constants.L[0]!.val ⦄ := by
  unfold part1
  step as ⟨low, h_low⟩
  step as ⟨multiple, h_multiple⟩
  step as ⟨shifted, h_shifted⟩
  step as ⟨mask, h_mask⟩
  have h_mask_value : mask.val = limbRadix - 1 := by
    rw [h_mask, h_shifted, U32.size, U32.numBits]
    rfl
  step as ⟨p, h_p⟩
  have h_p_value : p.val = (sum.val * constants.LFACTOR.val) % limbRadix := by
    simp only [h_p, UScalar.val_and, h_mask_value, limbRadix,
      Nat.and_two_pow_sub_one_eq_mod, h_multiple, core.num.U32.wrapping_mul_val_eq,
      h_low, UScalar.cast_val_eq, UScalar.size, UScalarTy.numBits]
    rw [Nat.mod_mul_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 29 ∣ 2 ^ 32)]
  have h_p_bound : p.val < limbRadix := by
    rw [h_p_value]
    exact Nat.mod_lt _ (by decide)
  have h_low_order : order % limbRadix = constants.L[0]!.val % limbRadix := by
    rw [← constants.L_spec]
    unfold asNat Array.uScalarToNatRadix constants.L limbRadix
    decide
  have h_factor : (constants.L[0]!.val * constants.LFACTOR.val + 1) % limbRadix = 0 := by
    have h := constants.LFACTOR_spec.1
    rw [Nat.add_mod, Nat.mul_mod, h_low_order] at h
    rw [Nat.add_mod, Nat.mul_mod]
    exact h
  have h_cancel : (sum.val + p.val * constants.L[0]!.val) % limbRadix = 0 := by
    rw [h_p_value]
    calc
      (sum.val + (sum.val * constants.LFACTOR.val % limbRadix) *
          constants.L[0]!.val) % limbRadix =
          (sum.val * (constants.L[0]!.val * constants.LFACTOR.val + 1)) % limbRadix := by
        rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod]
        congr 1
        ring
      _ = 0 := by
        rw [Nat.mul_mod, h_factor]
        simp only [Nat.mul_zero, Nat.zero_mod]
  step with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨l0, h_l0⟩
  have h_l0_bound : l0.val < limbRadix := by
    simpa only [h_l0, Array.getElem!_Nat_eq] using constants.L_limbs_lt 0 (by decide)
  step with m_spec as ⟨product, h_product⟩
  have h_product_bound : product.val ≤ limbRadix * limbRadix := by
    rw [h_product]
    exact Nat.mul_le_mul h_p_bound.le h_l0_bound.le
  step -threadGrindState -grind with U64.add_spec as ⟨joined, h_joined⟩ by
    simp only [limbRadix, U64.max_eq] at h_product_bound ⊢
    omega
  step as ⟨carry, h_carry⟩
  have h_carry_value : carry.val = joined.val / limbRadix := by
    simpa only [Nat.shiftRight_eq_div_pow, limbRadix] using h_carry
  refine ⟨h_p_bound, ?_, ?_⟩
  · have h_joined_bound : joined.val < 2 ^ 64 := joined.hBounds
    simp only [limbRadix] at h_carry_value
    omega
  · have h_div := Nat.mod_add_div joined.val limbRadix
    have h_joined_value : joined.val = sum.val + p.val * constants.L[0]!.val := by
      simp only [h_joined, h_product, h_l0, Array.getElem!_Nat_eq]
    rw [h_joined_value, h_cancel] at h_div
    rw [h_carry_value, h_joined_value]
    simpa only [Nat.zero_add, Nat.mul_comm] using h_div

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_reduce::part2`**

Splits off one radix digit without losing high bits. -/
@[step]
theorem part2_spec (sum : U64) :
    part2 sum ⦃ (carry : U64) (w : U32) =>
      w.val < limbRadix ∧
      carry.val < 2 ^ 35 ∧
      carry.val * limbRadix + w.val = sum.val ⦄ := by
  unfold part2
  step as ⟨low, h_low⟩
  step as ⟨shifted, h_shifted⟩
  step as ⟨mask, h_mask⟩
  have h_mask_value : mask.val = limbRadix - 1 := by
    rw [h_mask, h_shifted, U32.size, U32.numBits]
    rfl
  step as ⟨w, h_w⟩
  step as ⟨carry, h_carry⟩
  have h_w_value : w.val = sum.val % limbRadix := by
    simp only [h_w, UScalar.val_and, h_mask_value, limbRadix,
      Nat.and_two_pow_sub_one_eq_mod, h_low, UScalar.cast_val_eq, UScalarTy.numBits]
    exact Nat.mod_mod_of_dvd _ (by decide : 2 ^ 29 ∣ 2 ^ 32)
  have h_carry_value : carry.val = sum.val / limbRadix := by
    simpa only [Nat.shiftRight_eq_div_pow, limbRadix] using h_carry
  refine ⟨?_, ?_, ?_⟩
  · rw [h_w_value]
    exact Nat.mod_lt _ (by decide)
  · have h_bound : sum.val < 2 ^ 64 := sum.hBounds
    simp only [limbRadix] at h_carry_value
    omega
  · rw [h_carry_value, h_w_value]
    simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div sum.val limbRadix

end montgomery_reduce

/-! ## Splitting the generated function

The generated body is a single `do` block with 146 let-bindings.  Bindings `0 … 84` are the
nine `part1` rows (the last of them binds `(carry8, n8)`), and the remaining bindings up to
the concluding cast and subtraction are the eight `part2` rows.  Because `#decompose` clauses
apply sequentially, after the first clause the body starts with the `montgomery_reduce_adjust`
call at index `0`, so the second clause skips it and takes the following `144 - 85 + 1 = 60`
bindings.

The five `letRange`-crossing values `i3, i8, i15, i24, i65` are the cached lookups
`constants.L[1]!, constants.L[2]!, constants.L[3]!, constants.L[4]!, constants.L[8]!`, which
is why the adjust phase returns a fourteen-wide tuple.  The quotient digit `n0` is *not*
returned: it is dead after the adjust phase, its whole contribution already being folded into
`carry8`. -/
-- `#decompose` generates declarations rather than querying the environment, so the Mathlib
-- convention that forbids `#`-commands in library files does not apply to it.
set_option linter.hashCommand false in
#decompose montgomery_reduce montgomery_reduce_eq
  letRange 0 85 => montgomery_reduce_adjust
  letRange 1 60 => montgomery_reduce_extract

/-- One `m` multiplication of an accumulation chain. -/
local macro "mont_mul" : tactic =>
  `(tactic|
    (refine spec_bind (m_spec _ _) ?_
     intro product h_product
     try simp only [UScalar.ofNatCore_val_eq] at h_product))

/-- One addition of an accumulation chain, together with its overflow side condition.

The row equations established so far are named so that they can be cleared before `grind`
runs: they are large equations relating every value seen so far, and leaving them in the
context roughly doubles the time the side conditions take. -/
local macro "mont_add" rows:(ppSpace colGt ident)* : tactic =>
  `(tactic|
    (refine spec_bind (U64.add_spec ?_) ?_
     on_goal 1 =>
       clear $rows*
       grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
     intro sum h_sum))

/-- The accumulation chain between two `part1`/`part2` rows: the addition of the next
coefficient followed by `n` multiply-accumulate steps, where `n` is the number of
`n_j * constants.L[k]!` products that the row accumulates. -/
local macro "mont_chain" n:num rows:(ppSpace colGt ident)* : tactic =>
  `(tactic|
    (mont_add $rows*
     iterate $n
       mont_mul
       mont_add $rows*))

/-! ## The adjust phase -/

/-- The nine `part1` rows telescope to the part of the Montgomery identity of weight below
`B ^ 9`: the low nine coefficients plus the low half of `n * L` is exactly `c8 * B ^ 9`. -/
private theorem adjust_identity {B l0 l1 l2 l3 l4 l8 : Nat}
    {t0 t1 t2 t3 t4 t5 t6 t7 t8 : Nat} {n0 n1 n2 n3 n4 n5 n6 n7 n8 : Nat}
    {c0 c1 c2 c3 c4 c5 c6 c7 c8 : Nat}
    (h0 : t0 + n0 * l0 = c0 * B)
    (h1 : c0 + t1 + n0 * l1 + n1 * l0 = c1 * B)
    (h2 : c1 + t2 + n0 * l2 + n1 * l1 + n2 * l0 = c2 * B)
    (h3 : c2 + t3 + n0 * l3 + n1 * l2 + n2 * l1 + n3 * l0 = c3 * B)
    (h4 : c3 + t4 + n0 * l4 + n1 * l3 + n2 * l2 + n3 * l1 + n4 * l0 = c4 * B)
    (h5 : c4 + t5 + n1 * l4 + n2 * l3 + n3 * l2 + n4 * l1 + n5 * l0 = c5 * B)
    (h6 : c5 + t6 + n2 * l4 + n3 * l3 + n4 * l2 + n5 * l1 + n6 * l0 = c6 * B)
    (h7 : c6 + t7 + n3 * l4 + n4 * l3 + n5 * l2 + n6 * l1 + n7 * l0 = c7 * B)
    (h8 : c7 + t8 + n0 * l8 + n4 * l4 + n5 * l3 + n6 * l2 + n7 * l1 + n8 * l0 = c8 * B) :
    t0 + B * t1 + B ^ 2 * t2 + B ^ 3 * t3 + B ^ 4 * t4 + B ^ 5 * t5 + B ^ 6 * t6 +
        B ^ 7 * t7 + B ^ 8 * t8 +
        (n0 * l0 +
          B * (n0 * l1 + n1 * l0) +
          B ^ 2 * (n0 * l2 + n1 * l1 + n2 * l0) +
          B ^ 3 * (n0 * l3 + n1 * l2 + n2 * l1 + n3 * l0) +
          B ^ 4 * (n0 * l4 + n1 * l3 + n2 * l2 + n3 * l1 + n4 * l0) +
          B ^ 5 * (n1 * l4 + n2 * l3 + n3 * l2 + n4 * l1 + n5 * l0) +
          B ^ 6 * (n2 * l4 + n3 * l3 + n4 * l2 + n5 * l1 + n6 * l0) +
          B ^ 7 * (n3 * l4 + n4 * l3 + n5 * l2 + n6 * l1 + n7 * l0) +
          B ^ 8 * (n0 * l8 + n4 * l4 + n5 * l3 + n6 * l2 + n7 * l1 + n8 * l0)) =
      c8 * B ^ 9 := by
  zify at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  linear_combination h0 + h1 * (B : Int) + h2 * (B : Int) ^ 2 + h3 * (B : Int) ^ 3 +
    h4 * (B : Int) ^ 4 + h5 * (B : Int) ^ 5 + h6 * (B : Int) ^ 6 + h7 * (B : Int) ^ 7 +
    h8 * (B : Int) ^ 8

/-- **Spec theorem for the adjust phase of
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_reduce`**

Returns the cached `constants.L` lookups, the Montgomery quotient digits `n1, …, n8` and the
carry out of the ninth row. -/
theorem montgomery_reduce_adjust_spec (limbs : Array U64 17#usize)
    (h_bounds : ∀ i < 17, limbs[i]!.val < 2 ^ 63) :
    montgomery_reduce_adjust limbs ⦃ (i3 n1 i8 n2 i15 n3 i24 n4 n5 n6 n7 i65 : U32)
        (carry8 : U64) (n8 : U32) =>
      i3 = constants.L[1]! ∧ i8 = constants.L[2]! ∧ i15 = constants.L[3]! ∧
      i24 = constants.L[4]! ∧ i65 = constants.L[8]! ∧
      n1.val < limbRadix ∧ n2.val < limbRadix ∧ n3.val < limbRadix ∧ n4.val < limbRadix ∧
      n5.val < limbRadix ∧ n6.val < limbRadix ∧ n7.val < limbRadix ∧ n8.val < limbRadix ∧
      carry8.val < 2 ^ 35 ∧
      ∃ n0 : U32, n0.val < limbRadix ∧
        limbs[0]!.val + limbRadix * limbs[1]!.val + limbRadix ^ 2 * limbs[2]!.val +
            limbRadix ^ 3 * limbs[3]!.val + limbRadix ^ 4 * limbs[4]!.val +
            limbRadix ^ 5 * limbs[5]!.val + limbRadix ^ 6 * limbs[6]!.val +
            limbRadix ^ 7 * limbs[7]!.val + limbRadix ^ 8 * limbs[8]!.val +
            (n0.val * constants.L[0]!.val +
              limbRadix * (n0.val * constants.L[1]!.val + n1.val * constants.L[0]!.val) +
              limbRadix ^ 2 * (n0.val * constants.L[2]!.val + n1.val * constants.L[1]!.val +
                n2.val * constants.L[0]!.val) +
              limbRadix ^ 3 * (n0.val * constants.L[3]!.val + n1.val * constants.L[2]!.val +
                n2.val * constants.L[1]!.val + n3.val * constants.L[0]!.val) +
              limbRadix ^ 4 * (n0.val * constants.L[4]!.val + n1.val * constants.L[3]!.val +
                n2.val * constants.L[2]!.val + n3.val * constants.L[1]!.val +
                n4.val * constants.L[0]!.val) +
              limbRadix ^ 5 * (n1.val * constants.L[4]!.val + n2.val * constants.L[3]!.val +
                n3.val * constants.L[2]!.val + n4.val * constants.L[1]!.val +
                n5.val * constants.L[0]!.val) +
              limbRadix ^ 6 * (n2.val * constants.L[4]!.val + n3.val * constants.L[3]!.val +
                n4.val * constants.L[2]!.val + n5.val * constants.L[1]!.val +
                n6.val * constants.L[0]!.val) +
              limbRadix ^ 7 * (n3.val * constants.L[4]!.val + n4.val * constants.L[3]!.val +
                n5.val * constants.L[2]!.val + n6.val * constants.L[1]!.val +
                n7.val * constants.L[0]!.val) +
              limbRadix ^ 8 * (n0.val * constants.L[8]!.val + n4.val * constants.L[4]!.val +
                n5.val * constants.L[3]!.val + n6.val * constants.L[2]!.val +
                n7.val * constants.L[1]!.val + n8.val * constants.L[0]!.val)) =
          carry8.val * limbRadix ^ 9 ⦄ := by
  simp only [Array.getElem!_Nat_eq] at h_bounds
  unfold montgomery_reduce_adjust Insts.CoreOpsIndexIndexUsizeU32.index
  simp only [index_eq, UScalar.ofNatCore_val_eq, Nat.reduceLT, constants.L,
    Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
    List.getElem!_cons_succ, bind_tc_ok]
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c0, n0, hn0, hc0, row0⟩ by grind only [limbRadix]
  mont_chain 1 row0
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c1, n1, hn1, hc1, row1⟩ by grind only [limbRadix]
  simp only [*, -row1] at row1
  mont_chain 2 row0 row1
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c2, n2, hn2, hc2, row2⟩ by grind only [limbRadix]
  simp only [*, -row2] at row2
  mont_chain 3 row0 row1 row2
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c3, n3, hn3, hc3, row3⟩ by grind only [limbRadix]
  simp only [*, -row3] at row3
  mont_chain 4 row0 row1 row2 row3
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c4, n4, hn4, hc4, row4⟩ by grind only [limbRadix]
  simp only [*, -row4] at row4
  mont_chain 4 row0 row1 row2 row3 row4
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c5, n5, hn5, hc5, row5⟩ by grind only [limbRadix]
  simp only [*, -row5] at row5
  mont_chain 4 row0 row1 row2 row3 row4 row5
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c6, n6, hn6, hc6, row6⟩ by grind only [limbRadix]
  simp only [*, -row6] at row6
  mont_chain 4 row0 row1 row2 row3 row4 row5 row6
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c7, n7, hn7, hc7, row7⟩ by grind only [limbRadix]
  simp only [*, -row7] at row7
  mont_chain 5 row0 row1 row2 row3 row4 row5 row6 row7
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c8, n8, hn8, hc8, row8⟩ by grind only [limbRadix]
  simp only [*, -row8] at row8
  refine ⟨hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hc8, n0, hn0, ?_⟩
  simp only [constants.L, Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
    UScalar.ofNatCore_val_eq] at row0 row1 row2 row3 row4 row5 row6 row7 row8
  exact adjust_identity row0.symm row1.symm row2.symm row3.symm row4.symm row5.symm row6.symm
    row7.symm row8.symm

/-! ## The extract phase -/

/-- The eight `part2` rows telescope to the part of the Montgomery identity of weight at
least `B ^ 9`, divided by `B ^ 9`: the incoming carry plus the high eight coefficients plus
the high half of `n * L` is exactly the result. -/
private theorem extract_identity {B l1 l2 l3 l4 l8 : Nat}
    {t9 t10 t11 t12 t13 t14 t15 t16 : Nat} {n1 n2 n3 n4 n5 n6 n7 n8 : Nat}
    {c8 c9 c10 c11 c12 c13 c14 c15 c16 : Nat} {r0 r1 r2 r3 r4 r5 r6 r7 : Nat}
    (h9 : c8 + t9 + n1 * l8 + n5 * l4 + n6 * l3 + n7 * l2 + n8 * l1 = c9 * B + r0)
    (h10 : c9 + t10 + n2 * l8 + n6 * l4 + n7 * l3 + n8 * l2 = c10 * B + r1)
    (h11 : c10 + t11 + n3 * l8 + n7 * l4 + n8 * l3 = c11 * B + r2)
    (h12 : c11 + t12 + n4 * l8 + n8 * l4 = c12 * B + r3)
    (h13 : c12 + t13 + n5 * l8 = c13 * B + r4)
    (h14 : c13 + t14 + n6 * l8 = c14 * B + r5)
    (h15 : c14 + t15 + n7 * l8 = c15 * B + r6)
    (h16 : c15 + t16 + n8 * l8 = c16 * B + r7) :
    c8 + t9 + B * t10 + B ^ 2 * t11 + B ^ 3 * t12 + B ^ 4 * t13 + B ^ 5 * t14 +
        B ^ 6 * t15 + B ^ 7 * t16 +
        (n1 * l8 + n5 * l4 + n6 * l3 + n7 * l2 + n8 * l1 +
          B * (n2 * l8 + n6 * l4 + n7 * l3 + n8 * l2) +
          B ^ 2 * (n3 * l8 + n7 * l4 + n8 * l3) +
          B ^ 3 * (n4 * l8 + n8 * l4) +
          B ^ 4 * (n5 * l8) + B ^ 5 * (n6 * l8) + B ^ 6 * (n7 * l8) + B ^ 7 * (n8 * l8)) =
      r0 + B * r1 + B ^ 2 * r2 + B ^ 3 * r3 + B ^ 4 * r4 + B ^ 5 * r5 + B ^ 6 * r6 +
        B ^ 7 * r7 + B ^ 8 * c16 := by
  zify at h9 h10 h11 h12 h13 h14 h15 h16 ⊢
  linear_combination h9 + h10 * (B : Int) + h11 * (B : Int) ^ 2 + h12 * (B : Int) ^ 3 +
    h13 * (B : Int) ^ 4 + h14 * (B : Int) ^ 5 + h15 * (B : Int) ^ 6 + h16 * (B : Int) ^ 7

/-- **Spec theorem for the extract phase of
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_reduce`**

Returns the eight low digits of the exact Montgomery quotient together with the top carry. -/
theorem montgomery_reduce_extract_spec (limbs : Array U64 17#usize)
    (i3 n1 i8 n2 i15 n3 i24 n4 n5 n6 n7 i65 : U32) (carry8 : U64) (n8 : U32)
    (h_bounds : ∀ i < 17, limbs[i]!.val < 2 ^ 63)
    (h_l1 : i3 = constants.L[1]!) (h_l2 : i8 = constants.L[2]!)
    (h_l3 : i15 = constants.L[3]!) (h_l4 : i24 = constants.L[4]!)
    (h_l8 : i65 = constants.L[8]!)
    (hn1 : n1.val < limbRadix) (hn2 : n2.val < limbRadix) (hn3 : n3.val < limbRadix)
    (hn4 : n4.val < limbRadix) (hn5 : n5.val < limbRadix) (hn6 : n6.val < limbRadix)
    (hn7 : n7.val < limbRadix) (hn8 : n8.val < limbRadix)
    (h_carry8 : carry8.val < 2 ^ 35) :
    montgomery_reduce_extract limbs i3 n1 i8 n2 i15 n3 i24 n4 n5 n6 n7 i65 carry8 n8
      ⦃ (r0 r1 r2 r3 r4 r5 r6 : U32) (carry16 : U64) (r7 : U32) =>
      r0.val < limbRadix ∧ r1.val < limbRadix ∧ r2.val < limbRadix ∧ r3.val < limbRadix ∧
      r4.val < limbRadix ∧ r5.val < limbRadix ∧ r6.val < limbRadix ∧ r7.val < limbRadix ∧
      carry8.val + limbs[9]!.val + limbRadix * limbs[10]!.val +
          limbRadix ^ 2 * limbs[11]!.val + limbRadix ^ 3 * limbs[12]!.val +
          limbRadix ^ 4 * limbs[13]!.val + limbRadix ^ 5 * limbs[14]!.val +
          limbRadix ^ 6 * limbs[15]!.val + limbRadix ^ 7 * limbs[16]!.val +
          (n1.val * constants.L[8]!.val + n5.val * constants.L[4]!.val +
            n6.val * constants.L[3]!.val + n7.val * constants.L[2]!.val +
            n8.val * constants.L[1]!.val +
            limbRadix * (n2.val * constants.L[8]!.val + n6.val * constants.L[4]!.val +
              n7.val * constants.L[3]!.val + n8.val * constants.L[2]!.val) +
            limbRadix ^ 2 * (n3.val * constants.L[8]!.val + n7.val * constants.L[4]!.val +
              n8.val * constants.L[3]!.val) +
            limbRadix ^ 3 * (n4.val * constants.L[8]!.val + n8.val * constants.L[4]!.val) +
            limbRadix ^ 4 * (n5.val * constants.L[8]!.val) +
            limbRadix ^ 5 * (n6.val * constants.L[8]!.val) +
            limbRadix ^ 6 * (n7.val * constants.L[8]!.val) +
            limbRadix ^ 7 * (n8.val * constants.L[8]!.val)) =
        r0.val + limbRadix * r1.val + limbRadix ^ 2 * r2.val + limbRadix ^ 3 * r3.val +
          limbRadix ^ 4 * r4.val + limbRadix ^ 5 * r5.val + limbRadix ^ 6 * r6.val +
          limbRadix ^ 7 * r7.val + limbRadix ^ 8 * carry16.val ⦄ := by
  simp only [Array.getElem!_Nat_eq] at h_bounds
  -- Put the digit bounds in the numeric form the overflow side conditions below need.
  simp only [limbRadix] at hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8
  unfold montgomery_reduce_extract
  simp only [h_l1, h_l2, h_l3, h_l4, h_l8, index_eq, UScalar.ofNatCore_val_eq, Nat.reduceLT,
    constants.L, Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
    List.getElem!_cons_succ, bind_tc_ok]
  mont_chain 5
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c9, r0, hr0, hc9, row9⟩
  simp only [*, -row9] at row9
  mont_chain 4 row9
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c10, r1, hr1, hc10, row10⟩
  simp only [*, -row10] at row10
  mont_chain 3 row9 row10
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c11, r2, hr2, hc11, row11⟩
  simp only [*, -row11] at row11
  mont_chain 2 row9 row10 row11
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c12, r3, hr3, hc12, row12⟩
  simp only [*, -row12] at row12
  mont_chain 1 row9 row10 row11 row12
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c13, r4, hr4, hc13, row13⟩
  simp only [*, -row13] at row13
  mont_chain 1 row9 row10 row11 row12 row13
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c14, r5, hr5, hc14, row14⟩
  simp only [*, -row14] at row14
  mont_chain 1 row9 row10 row11 row12 row13 row14
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c15, r6, hr6, hc15, row15⟩
  simp only [*, -row15] at row15
  mont_chain 1 row9 row10 row11 row12 row13 row14 row15
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c16, r7, hr7, hc16, row16⟩
  simp only [*, -row16] at row16
  refine ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, ?_⟩
  exact extract_identity row9.symm row10.symm row11.symm row12.symm row13.symm row14.symm
    row15.symm row16.symm

/-! ## Gluing the two halves -/

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_reduce`**

Returns the normalized canonical Montgomery residue. -/
@[step]
theorem montgomery_reduce_spec (limbs : Array U64 17#usize)
    (h_bounds : ∀ i < 17, limbs[i]!.val < 2 ^ 63)
    (h_range : wideAsNat limbs < montgomeryRadix * order) :
    montgomery_reduce limbs ⦃ (result : Scalar29) =>
      (asNat result * montgomeryRadix) % order = wideAsNat limbs % order ∧
      IsNormalized result ∧
      asNat result < order ⦄ := by
  rw [montgomery_reduce_eq]
  step -threadGrindState -grind with montgomery_reduce_adjust_spec
    as ⟨i3, n1, i8, n2, i15, n3, i24, n4, n5, n6, n7, i65, carry8, n8,
        h_l1, h_l2, h_l3, h_l4, h_l8, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hc8,
        n0, hn0, h_adjust⟩
  step -threadGrindState -grind with montgomery_reduce_extract_spec
    as ⟨r0, r1, r2, r3, r4, r5, r6, carry16, r7,
        hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, h_extract⟩
  -- Assemble the exact quotient before narrowing the top carry.
  let adjustment : Scalar29 := Array.make 9#usize [n0, n1, n2, n3, n4, n5, n6, n7, n8]
  let quotient : Nat := r0.val + limbRadix ^ 1 * r1.val + limbRadix ^ 2 * r2.val +
    limbRadix ^ 3 * r3.val + limbRadix ^ 4 * r4.val + limbRadix ^ 5 * r5.val +
    limbRadix ^ 6 * r6.val + limbRadix ^ 7 * r7.val + limbRadix ^ 8 * carry16.val
  have h_adjustment : asNat adjustment < montgomeryRadix := by
    apply asNat_bounded
    intro i hi
    interval_cases i <;>
      simp only [adjustment, Array.getElem!_Nat_eq, Array.make,
        List.getElem!_cons_zero, List.getElem!_cons_succ] <;> assumption
  have h_identity : wideAsNat limbs + asNat adjustment * order = quotient * montgomeryRadix := by
    -- Weighting the extract identity by `limbRadix ^ 9` and adding the adjust identity
    -- recovers the full Montgomery identity.
    have h_poly :
        limbs[0]!.val + limbRadix * limbs[1]!.val + limbRadix ^ 2 * limbs[2]!.val +
            limbRadix ^ 3 * limbs[3]!.val + limbRadix ^ 4 * limbs[4]!.val +
            limbRadix ^ 5 * limbs[5]!.val + limbRadix ^ 6 * limbs[6]!.val +
            limbRadix ^ 7 * limbs[7]!.val + limbRadix ^ 8 * limbs[8]!.val +
            limbRadix ^ 9 * limbs[9]!.val + limbRadix ^ 10 * limbs[10]!.val +
            limbRadix ^ 11 * limbs[11]!.val + limbRadix ^ 12 * limbs[12]!.val +
            limbRadix ^ 13 * limbs[13]!.val + limbRadix ^ 14 * limbs[14]!.val +
            limbRadix ^ 15 * limbs[15]!.val + limbRadix ^ 16 * limbs[16]!.val +
            (n0.val + limbRadix * n1.val + limbRadix ^ 2 * n2.val + limbRadix ^ 3 * n3.val +
                limbRadix ^ 4 * n4.val + limbRadix ^ 5 * n5.val + limbRadix ^ 6 * n6.val +
                limbRadix ^ 7 * n7.val + limbRadix ^ 8 * n8.val) *
              (constants.L[0]!.val + limbRadix * constants.L[1]!.val +
                limbRadix ^ 2 * constants.L[2]!.val + limbRadix ^ 3 * constants.L[3]!.val +
                limbRadix ^ 4 * constants.L[4]!.val + limbRadix ^ 8 * constants.L[8]!.val) =
          (r0.val + limbRadix * r1.val + limbRadix ^ 2 * r2.val + limbRadix ^ 3 * r3.val +
            limbRadix ^ 4 * r4.val + limbRadix ^ 5 * r5.val + limbRadix ^ 6 * r6.val +
            limbRadix ^ 7 * r7.val + limbRadix ^ 8 * carry16.val) * limbRadix ^ 9 := by
      zify at h_adjust h_extract ⊢
      linear_combination h_adjust + (limbRadix : Int) ^ 9 * h_extract
    have h_radix : montgomeryRadix = (2 ^ 29) ^ 9 := by
      rw [← pow_mul]
      exact congrArg (fun n => (2 : Nat) ^ n) (by decide : 261 = 29 * 9)
    rw [← constants.L_spec, h_radix]
    simpa only [wideAsNat, asNat, adjustment, quotient, Array.uScalarToNatRadix,
      UScalar.ofNatCore_val_eq, pow_mul, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, constants.L, Array.getElem!_Nat_eq,
      Array.make, List.getElem!_cons_zero, List.getElem!_cons_succ,
      limbRadix, pow_zero, pow_one, one_mul, mul_one, mul_zero, add_zero] using h_poly
  have h_radix_pos : 0 < montgomeryRadix := pow_pos (by decide : 0 < (2 : Nat)) 261
  have h_quotient : quotient < 2 * order := by
    apply (Nat.mul_lt_mul_right h_radix_pos).mp
    rw [← h_identity]
    calc
      wideAsNat limbs + asNat adjustment * order <
          montgomeryRadix * order + montgomeryRadix * order :=
        Nat.add_lt_add h_range (Nat.mul_lt_mul_of_pos_right h_adjustment order_pos)
      _ = 2 * order * montgomeryRadix := by ring
  have h_small : quotient < 2 ^ 254 := by
    calc
      quotient < 2 * order := h_quotient
      _ < 2 * 2 ^ 253 := Nat.mul_lt_mul_of_pos_left order_lt_two_pow_253 (by decide)
      _ = 2 ^ 254 := by decide
  have h_top_weight : limbRadix ^ 8 * carry16.val ≤ quotient := Nat.le_add_left _ _
  have h_top : carry16.val < 2 ^ 22 := by
    apply (Nat.mul_lt_mul_left (by decide : 0 < 2 ^ 232)).mp
    rw [← pow_add]
    have h_weight : 2 ^ 232 * carry16.val ≤ quotient := by
      simpa only [limbRadix, ← pow_mul, show 29 * 8 = 232 from rfl] using h_top_weight
    exact lt_of_le_of_lt h_weight h_small
  refine spec_bind (UScalar.cast_inBounds_spec .U32 carry16 ?_) ?_
  · rw [UScalar.max_UScalarTy_U32_eq, U32.max_eq]
    exact h_top.le.trans (by decide)
  intro r8 h_r8
  let pre : Scalar29 := Array.make 9#usize [r0, r1, r2, r3, r4, r5, r6, r7, r8]
  have h_pre : asNat pre = quotient := by
    simp only [pre, asNat, Array.uScalarToNatRadix, UScalar.ofNatCore_val_eq,
      pow_mul, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
      List.getElem!_cons_succ, quotient, limbRadix, h_r8, pow_zero, pow_one, one_mul]
  have h_normalized : IsNormalized pre := by
    -- Keep the context small: `interval_cases` below is sensitive to its size.
    clear * - hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 h_r8 h_top
    intro i hi
    interval_cases i <;>
      simp only [pre, Array.getElem!_Nat_eq, Array.make,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
    all_goals first | assumption | (rw [h_r8]; exact h_top.trans (by decide))
  have h_sub_spec := sub_spec pre constants.L h_normalized constants.L_limbs_lt
    (by rw [constants.L_spec]; omega)
    (by rw [constants.L_spec, h_pre]; omega)
  refine spec_mono h_sub_spec ?_
  intro result ⟨h_result, h_sub, h_canonical⟩
  have h_residue : asNat result % order = quotient % order := by
    rw [constants.L_spec, h_pre] at h_sub
    simpa only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod] using h_sub
  have h_scaled : (quotient * montgomeryRadix) % order = wideAsNat limbs % order := by
    have h := congrArg (fun n : Nat => n % order) h_identity
    simpa only [Nat.add_mul_mod_self_right] using h.symm
  refine ⟨?_, h_result, h_canonical⟩
  calc
    (asNat result * montgomeryRadix) % order =
        ((asNat result % order) * (montgomeryRadix % order)) % order := Nat.mul_mod _ _ _
    _ = ((quotient % order) * (montgomeryRadix % order)) % order := by rw [h_residue]
    _ = (quotient * montgomeryRadix) % order := (Nat.mul_mod _ _ _).symm
    _ = wideAsNat limbs % order := h_scaled

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

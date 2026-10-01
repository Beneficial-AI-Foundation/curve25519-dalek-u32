/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Auxiliary
import Dalek32.Constants.L
import Dalek32.Constants.Lfactor
import Dalek32.Lint.Basic
import Dalek32.Scalar.Index
import Dalek32.Scalar.M
import Dalek32.Scalar.Sub
import Mathlib.Tactic.IntervalCases

/-!
# Spec theorem for `montgomery_reduce`

Montgomery reduction of seventeen radix-`2^29` coefficients.
Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 328-369.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

private theorem index_eq {α : Type} [Inhabited α] {size : Usize}
    (a : Array α size) (i : Usize) (hi : i.val < size.val) :
    Array.index_usize a i = ok a[i.val]! := by
  grind [Array.index_usize, Array.getElem!_Nat_eq]

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
    rwa [Nat.add_mod, Nat.mul_mod, h_low_order, ← Nat.mul_mod, ← Nat.add_mod] at h
  have h_cancel : (sum.val + p.val * constants.L[0]!.val) % limbRadix = 0 := by
    rw [h_p_value, Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod,
      Nat.add_comm sum.val, Nat.mul_assoc, Nat.mul_comm constants.LFACTOR.val,
      ← Nat.mul_add_one, Nat.mul_mod, h_factor, Nat.mul_zero, Nat.zero_mod]
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
  have h_bound : joined.val < 2 ^ 64 := joined.hBounds
  simp only [h_joined, h_product, h_l0] at h_bound h_carry
  simp only [Nat.shiftRight_eq_div_pow] at h_carry
  simp only [limbRadix, Array.getElem!_Nat_eq] at h_p_bound h_cancel ⊢
  omega

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
  have h_bound : sum.val < 2 ^ 64 := sum.hBounds
  simp only [Nat.shiftRight_eq_div_pow] at h_carry
  simp only [limbRadix] at h_w_value ⊢
  omega

end montgomery_reduce

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
  simp only [Array.getElem!_Nat_eq] at h_bounds
  unfold montgomery_reduce Insts.CoreOpsIndexIndexUsizeU32.index
  simp only [index_eq, UScalar.ofNatCore_val_eq, Nat.reduceLT, constants.L,
    Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
    List.getElem!_cons_succ, bind_tc_ok]
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c0, n0, hn0, hc0, row0⟩ by
      clear h_range
      grind only [limbRadix]
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 1
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c1, n1, hn1, hc1, row1⟩ by
      clear h_range row0
      grind only [limbRadix]
  simp only [*, -row1] at row1
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 2
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c2, n2, hn2, hc2, row2⟩ by
      clear h_range row0 row1
      grind only [limbRadix]
  simp only [*, -row2] at row2
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 3
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c3, n3, hn3, hc3, row3⟩ by
      clear h_range row0 row1 row2
      grind only [limbRadix]
  simp only [*, -row3] at row3
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 4
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c4, n4, hn4, hc4, row4⟩ by
      clear h_range row0 row1 row2 row3
      grind only [limbRadix]
  simp only [*, -row4] at row4
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 4
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c5, n5, hn5, hc5, row5⟩ by
      clear h_range row0 row1 row2 row3 row4
      grind only [limbRadix]
  simp only [*, -row5] at row5
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4 row5
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 4
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4 row5
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c6, n6, hn6, hc6, row6⟩ by
      clear h_range row0 row1 row2 row3 row4 row5
      grind only [limbRadix]
  simp only [*, -row6] at row6
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4 row5 row6
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 4
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4 row5 row6
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c7, n7, hn7, hc7, row7⟩ by
      clear h_range row0 row1 row2 row3 row4 row5 row6
      grind only [limbRadix]
  simp only [*, -row7] at row7
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4 row5 row6 row7
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 5
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4 row5 row6 row7
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c8, n8, hn8, hc8, row8⟩ by
      clear h_range row0 row1 row2 row3 row4 row5 row6 row7
      grind only [limbRadix]
  simp only [*, -row8] at row8
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 5
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c9, r0, hr0, hc9, row9⟩
  simp only [*, -row9] at row9
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 4
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c10, r1, hr1, hc10, row10⟩
  simp only [*, -row10] at row10
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 3
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c11, r2, hr2, hc11, row11⟩
  simp only [*, -row11] at row11
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 2
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c12, r3, hr3, hc12, row12⟩
  simp only [*, -row12] at row12
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 1
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c13, r4, hr4, hc13, row13⟩
  simp only [*, -row13] at row13
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 1
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c14, r5, hr5, hc14, row14⟩
  simp only [*, -row14] at row14
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 row14
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 1
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 row14
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c15, r6, hr6, hc15, row15⟩
  simp only [*, -row15] at row15
  refine spec_bind (U64.add_spec ?_) ?_
  · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12
      row13 row14 row15
    grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 1
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · clear h_range row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12
        row13 row14 row15
      grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c16, r7, hr7, hc16, row16⟩
  simp only [*, -row16] at row16
  -- Assemble the exact quotient before narrowing the top carry.
  let adjustment : Scalar29 := Array.make 9#usize [n0, n1, n2, n3, n4, n5, n6, n7, n8]
  let quotient : Nat := r0.val + limbRadix ^ 1 * r1.val + limbRadix ^ 2 * r2.val +
    limbRadix ^ 3 * r3.val + limbRadix ^ 4 * r4.val + limbRadix ^ 5 * r5.val +
    limbRadix ^ 6 * r6.val + limbRadix ^ 7 * r7.val + limbRadix ^ 8 * c16.val
  have h_adjustment : asNat adjustment < montgomeryRadix := by
    apply asNat_bounded
    intro i hi
    interval_cases i <;>
      simp only [adjustment, Array.getElem!_Nat_eq, Array.make,
        List.getElem!_cons_zero, List.getElem!_cons_succ] <;> assumption
  have h_identity : wideAsNat limbs + asNat adjustment * order = quotient * montgomeryRadix := by
    clear * - row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13
      row14 row15 row16
    rw [← constants.L_spec]
    simp only [wideAsNat, asNat, adjustment, quotient, Array.uScalarToNatRadix,
      montgomeryRadix, limbRadix, UScalar.ofNatCore_val_eq, pow_mul,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      constants.L, Array.getElem!_Nat_eq, Array.make,
      List.getElem!_cons_zero, List.getElem!_cons_succ,
      pow_zero, pow_one, one_mul, mul_zero, add_zero]
      at *
    omega
  clear * - h_range h_adjustment h_identity hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  have h_quotient : quotient < 2 * order := by
    apply Nat.lt_of_mul_lt_mul_right (a := montgomeryRadix)
    rw [← h_identity, Nat.mul_assoc, Nat.mul_comm order, two_mul]
    exact Nat.add_lt_add h_range (Nat.mul_lt_mul_of_pos_right h_adjustment order_pos)
  have h_small : quotient < 2 ^ 254 := by
    have := order_lt_two_pow_253
    omega
  have h_top : c16.val < 2 ^ 22 := by
    simp only [quotient, limbRadix] at h_small
    omega
  refine spec_bind (UScalar.cast_inBounds_spec .U32 c16 ?_) ?_
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
    clear * - hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 h_r8 h_top
    intro i hi
    interval_cases i <;>
      simp only [pre, Array.getElem!_Nat_eq, Array.make,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
    all_goals first | assumption | (rw [h_r8]; exact h_top.trans (by decide))
  have h_sub_spec := sub_spec pre constants.L h_normalized constants.L_limbs_lt
    (by rw [constants.L_spec]; omega)
    (by rw [constants.L_spec, h_pre]; omega)
  conv at h_sub_spec => lhs; unfold constants.L
  refine spec_mono h_sub_spec ?_
  intro result ⟨h_result, h_sub, h_canonical⟩
  rw [constants.L_spec, h_pre, Nat.add_mod_right] at h_sub
  refine ⟨?_, h_result, h_canonical⟩
  rw [← Nat.mod_mul_mod, h_sub, Nat.mod_mul_mod, ← h_identity, Nat.add_mul_mod_self_right]

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

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

/-- The seventeen carry equations telescope to the Montgomery identity. -/
private theorem reduction_identity (B l0 l1 l2 l3 l4 l8 : Nat)
    (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 : Nat)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 : Nat)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 : Nat)
    (r0 r1 r2 r3 r4 r5 r6 r7 : Nat)
    (h0 : t0 + n0 * l0 = c0 * B)
    (h1 : c0 + t1 + n0 * l1 + n1 * l0 = c1 * B)
    (h2 : c1 + t2 + n0 * l2 + n1 * l1 + n2 * l0 = c2 * B)
    (h3 : c2 + t3 + n0 * l3 + n1 * l2 + n2 * l1 + n3 * l0 = c3 * B)
    (h4 : c3 + t4 + n0 * l4 + n1 * l3 + n2 * l2 + n3 * l1 + n4 * l0 = c4 * B)
    (h5 : c4 + t5 + n1 * l4 + n2 * l3 + n3 * l2 + n4 * l1 + n5 * l0 = c5 * B)
    (h6 : c5 + t6 + n2 * l4 + n3 * l3 + n4 * l2 + n5 * l1 + n6 * l0 = c6 * B)
    (h7 : c6 + t7 + n3 * l4 + n4 * l3 + n5 * l2 + n6 * l1 + n7 * l0 = c7 * B)
    (h8 : c7 + t8 + n0 * l8 + n4 * l4 + n5 * l3 + n6 * l2 + n7 * l1 + n8 * l0 = c8 * B)
    (h9 : c8 + t9 + n1 * l8 + n5 * l4 + n6 * l3 + n7 * l2 + n8 * l1 = c9 * B + r0)
    (h10 : c9 + t10 + n2 * l8 + n6 * l4 + n7 * l3 + n8 * l2 = c10 * B + r1)
    (h11 : c10 + t11 + n3 * l8 + n7 * l4 + n8 * l3 = c11 * B + r2)
    (h12 : c11 + t12 + n4 * l8 + n8 * l4 = c12 * B + r3)
    (h13 : c12 + t13 + n5 * l8 = c13 * B + r4)
    (h14 : c13 + t14 + n6 * l8 = c14 * B + r5)
    (h15 : c14 + t15 + n7 * l8 = c15 * B + r6)
    (h16 : c15 + t16 + n8 * l8 = c16 * B + r7) :
    (t0 + B * t1 + B ^ 2 * t2 + B ^ 3 * t3 + B ^ 4 * t4 + B ^ 5 * t5 + B ^ 6 * t6 + B ^ 7 * t7 +
      B ^ 8 * t8 + B ^ 9 * t9 + B ^ 10 * t10 + B ^ 11 * t11 + B ^ 12 * t12 + B ^ 13 * t13 +
      B ^ 14 * t14 + B ^ 15 * t15 + B ^ 16 * t16) +
      (n0 + B * n1 + B ^ 2 * n2 + B ^ 3 * n3 + B ^ 4 * n4 + B ^ 5 * n5 + B ^ 6 * n6 +
        B ^ 7 * n7 + B ^ 8 * n8) *
      (l0 + B * l1 + B ^ 2 * l2 + B ^ 3 * l3 + B ^ 4 * l4 + B ^ 8 * l8) =
      (r0 + B * r1 + B ^ 2 * r2 + B ^ 3 * r3 + B ^ 4 * r4 + B ^ 5 * r5 + B ^ 6 * r6 +
        B ^ 7 * r7 + B ^ 8 * c16) * B ^ 9 := by
  zify at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 ⊢
  linear_combination h0 + h1 * (B : Int) + h2 * (B : Int) ^ 2 + h3 * (B : Int) ^ 3 +
    h4 * (B : Int) ^ 4 + h5 * (B : Int) ^ 5 + h6 * (B : Int) ^ 6 + h7 * (B : Int) ^ 7 +
    h8 * (B : Int) ^ 8 + h9 * (B : Int) ^ 9 + h10 * (B : Int) ^ 10 + h11 * (B : Int) ^ 11 +
    h12 * (B : Int) ^ 12 + h13 * (B : Int) ^ 13 + h14 * (B : Int) ^ 14 + h15 * (B : Int) ^ 15 +
    h16 * (B : Int) ^ 16

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_reduce`**

Returns the normalized canonical Montgomery residue. -/
@[step]
theorem montgomery_reduce_spec (limbs : Array U64 17#usize)
    (h_bounds : ∀ i < 17, limbs[i]!.val < 2 ^ 63)
    (h_range : wideAsNat limbs < montgomeryRadix * order) :
    montgomery_reduce limbs ⦃ (result : Scalar29) =>
      (asNat result * montgomeryRadix) % order = wideAsNat limbs % order ∧
      (∀ i < 9, result[i]!.val < limbRadix) ∧
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
    have h_poly := reduction_identity limbRadix
      (constants.L[0]!.val) (constants.L[1]!.val) (constants.L[2]!.val) (constants.L[3]!.val)
      (constants.L[4]!.val) (constants.L[8]!.val)
      (limbs.val[0]!.val) (limbs.val[1]!.val) (limbs.val[2]!.val) (limbs.val[3]!.val)
      (limbs.val[4]!.val) (limbs.val[5]!.val) (limbs.val[6]!.val) (limbs.val[7]!.val)
      (limbs.val[8]!.val) (limbs.val[9]!.val) (limbs.val[10]!.val) (limbs.val[11]!.val)
      (limbs.val[12]!.val) (limbs.val[13]!.val) (limbs.val[14]!.val) (limbs.val[15]!.val)
      (limbs.val[16]!.val)
      n0.val n1.val n2.val n3.val n4.val n5.val n6.val n7.val n8.val
      c0.val c1.val c2.val c3.val c4.val c5.val c6.val c7.val c8.val c9.val c10.val c11.val
      c12.val c13.val c14.val c15.val c16.val
      r0.val r1.val r2.val r3.val r4.val r5.val r6.val r7.val
    simp only [constants.L, Array.getElem!_Nat_eq, Array.make,
      List.getElem!_cons_zero, List.getElem!_cons_succ, UScalar.ofNatCore_val_eq]
      at h_poly row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13
        row14 row15 row16
    specialize h_poly row0.symm row1.symm row2.symm row3.symm row4.symm row5.symm row6.symm
      row7.symm row8.symm row9.symm row10.symm row11.symm row12.symm row13.symm row14.symm
      row15.symm row16.symm
    have h_radix : montgomeryRadix = (2 ^ 29) ^ 9 := by
      rw [← pow_mul]
      exact congrArg (fun n => (2 : Nat) ^ n) (by decide : 261 = 29 * 9)
    rw [← constants.L_spec, h_radix]
    simpa only [wideAsNat, asNat, adjustment, quotient, Array.uScalarToNatRadix,
      UScalar.ofNatCore_val_eq, pow_mul, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, constants.L, Array.getElem!_Nat_eq,
      Array.make, List.getElem!_cons_zero, List.getElem!_cons_succ,
      limbRadix, pow_zero, pow_one, one_mul, mul_one, mul_zero, add_zero] using h_poly
  clear * - h_range h_adjustment h_identity hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  have h_radix_pos : 0 < montgomeryRadix := by
    exact pow_pos (by decide : 0 < (2 : Nat)) 261
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
  have h_top_weight : limbRadix ^ 8 * c16.val ≤ quotient := by
    exact Nat.le_add_left _ _
  have h_top : c16.val < 2 ^ 22 := by
    apply (Nat.mul_lt_mul_left (by decide : 0 < 2 ^ 232)).mp
    rw [← pow_add]
    have h_weight : 2 ^ 232 * c16.val ≤ quotient := by
      simpa only [limbRadix, ← pow_mul, show 29 * 8 = 232 from rfl] using h_top_weight
    exact lt_of_le_of_lt h_weight h_small
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
  have h_normalized : ∀ i < 9, pre[i]!.val < limbRadix := by
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
  simp only [Array.getElem!_Nat_eq] at h_result
  have h_residue : asNat result % order = quotient % order := by
    rw [constants.L_spec, h_pre] at h_sub
    have h := congrArg (fun n : Nat => n % order) h_sub
    split_ifs at h <;>
      simpa only [Nat.add_mod, Nat.mod_self, Nat.zero_mod, Nat.add_zero, Nat.mod_mod] using h
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

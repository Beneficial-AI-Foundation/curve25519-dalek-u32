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
private theorem part1_spec (sum : U64) (h_sum : sum.val < 2 ^ 63 + 2 ^ 61) :
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
private theorem part2_spec (sum : U64) :
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

attribute [local step] montgomery_reduce.part1_spec montgomery_reduce.part2_spec

-- Generate the block definitions and their equality with the extracted function.
set_option linter.hashCommand false in
#decompose montgomery_reduce montgomery_reduce_eq
  letRange 0 85 => montgomeryReduceAdjust
  letRange 1 60 => montgomeryReduceExtract

/-- Initial reduction block, through cancellation of the ninth low digit. -/
add_decl_doc montgomeryReduceAdjust

/-- Extraction block, returning eight reduced digits and the full top carry. -/
add_decl_doc montgomeryReduceExtract

/-- Value left after cancelling the low nine radix digits, before splitting the high digits. -/
private def highValue (limbs : Array U64 17#usize) (n1 n2 n3 n4 n5 n6 n7 n8 : U32)
    (carry : U64) : Nat :=
  carry.val + (∑ i ∈ Finset.range 8, limbRadix ^ i * limbs[i + 9]!.val) +
    (n1.val + limbRadix * n2.val + limbRadix ^ 2 * n3.val + limbRadix ^ 3 * n4.val +
      limbRadix ^ 4 * n5.val + limbRadix ^ 5 * n6.val + limbRadix ^ 6 * n7.val +
      limbRadix ^ 7 * n8.val) * constants.L[8]!.val +
    (n5.val + limbRadix * n6.val + limbRadix ^ 2 * n7.val + limbRadix ^ 3 * n8.val) *
      constants.L[4]!.val +
    (n6.val + limbRadix * n7.val + limbRadix ^ 2 * n8.val) * constants.L[3]!.val +
    (n7.val + limbRadix * n8.val) * constants.L[2]!.val + n8.val * constants.L[1]!.val

/-- Cancels the low nine digits and records the bounded multiple of the order added. -/
@[local step]
private theorem montgomery_reduce_adjust_spec (limbs : Array U64 17#usize)
    (h_bounds : ∀ i < 17, limbs[i]!.val < 2 ^ 63) :
    montgomeryReduceAdjust limbs
      ⦃ (l1 : U32) (n1 : U32) (l2 : U32) (n2 : U32) (l3 : U32) (n3 : U32)
        (l4 : U32) (n4 : U32) (n5 : U32) (n6 : U32) (n7 : U32) (l8 : U32)
        (carry8 : U64) (n8 : U32) =>
      l1 = constants.L[1]! ∧ l2 = constants.L[2]! ∧ l3 = constants.L[3]! ∧
      l4 = constants.L[4]! ∧ l8 = constants.L[8]! ∧
      IsNormalized (Array.make 9#usize [0#u32, n1, n2, n3, n4, n5, n6, n7, n8]) ∧
      carry8.val < 2 ^ 35 ∧
      ∃ adjustment : Nat, adjustment < montgomeryRadix ∧
        wideAsNat limbs + adjustment * order =
          highValue limbs n1 n2 n3 n4 n5 n6 n7 n8 carry8 * montgomeryRadix ⦄ := by
  simp only [Array.getElem!_Nat_eq] at h_bounds
  unfold montgomeryReduceAdjust Insts.CoreOpsIndexIndexUsizeU32.index
  simp only [index_eq, UScalar.ofNatCore_val_eq, Nat.reduceLT, constants.L,
    Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
    List.getElem!_cons_succ, bind_tc_ok]
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c0, n0, hn0, hc0, row0⟩ by
      grind only [limbRadix]
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 1
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c1, n1, hn1, hc1, row1⟩ by
      grind only [limbRadix]
  simp only [*, -row1] at row1
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 2
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c2, n2, hn2, hc2, row2⟩ by
      grind only [limbRadix]
  simp only [*, -row2] at row2
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 3
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c3, n3, hn3, hc3, row3⟩ by
      grind only [limbRadix]
  simp only [*, -row3] at row3
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 4
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c4, n4, hn4, hc4, row4⟩ by
      grind only [limbRadix]
  simp only [*, -row4] at row4
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 4
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c5, n5, hn5, hc5, row5⟩ by
      grind only [limbRadix]
  simp only [*, -row5] at row5
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 4
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c6, n6, hn6, hc6, row6⟩ by
      grind only [limbRadix]
  simp only [*, -row6] at row6
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 4
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c7, n7, hn7, hc7, row7⟩ by
      grind only [limbRadix]
  simp only [*, -row7] at row7
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 5
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part1_spec
    as ⟨c8, n8, hn8, hc8, row8⟩ by
      grind only [limbRadix]
  simp only [*, -row8] at row8
  let adjustment : Scalar29 := Array.make 9#usize [n0, n1, n2, n3, n4, n5, n6, n7, n8]
  refine ⟨?_, hc8, asNat adjustment, ?_, ?_⟩
  · intro i hi
    interval_cases i <;>
      simp only [Array.getElem!_Nat_eq,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
    all_goals first | assumption | decide
  · apply asNat_bounded
    intro i hi
    interval_cases i <;>
      simp only [adjustment, Array.getElem!_Nat_eq, Array.make,
        List.getElem!_cons_zero, List.getElem!_cons_succ] <;> assumption
  · rw [← constants.L_spec]
    simp only [wideAsNat, asNat, adjustment, highValue, Array.uScalarToNatRadix,
      montgomeryRadix, limbRadix, UScalar.ofNatCore_val_eq, pow_mul,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd,
      constants.L, Array.getElem!_Nat_eq, Array.make,
      List.getElem!_cons_zero, List.getElem!_cons_succ,
      pow_zero, pow_one, one_mul, mul_zero, add_zero]
      at row0 row1 row2 row3 row4 row5 row6 row7 row8 ⊢
    omega

/-- Splits the remaining value into eight normalized digits and the full top carry. -/
@[local step]
private theorem montgomery_reduce_extract_spec (limbs : Array U64 17#usize)
    (n1 n2 n3 n4 n5 n6 n7 n8 : U32) (carry8 : U64)
    (h_bounds : ∀ i < 17, limbs[i]!.val < 2 ^ 63)
    (h_n : IsNormalized (Array.make 9#usize [0#u32, n1, n2, n3, n4, n5, n6, n7, n8]))
    (h_carry : carry8.val < 2 ^ 35) :
    montgomeryReduceExtract limbs constants.L[1]! n1 constants.L[2]! n2
      constants.L[3]! n3 constants.L[4]! n4 n5 n6 n7 constants.L[8]! carry8 n8
      ⦃ (r0 : U32) (r1 : U32) (r2 : U32) (r3 : U32) (r4 : U32) (r5 : U32)
        (r6 : U32) (carry16 : U64) (r7 : U32) =>
      IsNormalized (Array.make 9#usize [r0, r1, r2, r3, r4, r5, r6, r7, 0#u32]) ∧
      asNat (Array.make 9#usize [r0, r1, r2, r3, r4, r5, r6, r7, 0#u32]) +
        limbRadix ^ 8 * carry16.val = highValue limbs n1 n2 n3 n4 n5 n6 n7 n8 carry8 ⦄ := by
  have hn1 := h_n 1 (by decide)
  have hn2 := h_n 2 (by decide)
  have hn3 := h_n 3 (by decide)
  have hn4 := h_n 4 (by decide)
  have hn5 := h_n 5 (by decide)
  have hn6 := h_n 6 (by decide)
  have hn7 := h_n 7 (by decide)
  have hn8 := h_n 8 (by decide)
  simp only [Array.getElem!_Nat_eq, Array.make,
    List.getElem!_cons_zero, List.getElem!_cons_succ] at hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8
  simp only [Array.getElem!_Nat_eq] at h_bounds
  unfold montgomeryReduceExtract
  simp only [index_eq, UScalar.ofNatCore_val_eq, Nat.reduceLT, constants.L,
    Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
    List.getElem!_cons_succ, bind_tc_ok]
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 5
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c9, r0, hr0, hc9, row9⟩
  simp only [*, -row9] at row9
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 4
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c10, r1, hr1, hc10, row10⟩
  simp only [*, -row10] at row10
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 3
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c11, r2, hr2, hc11, row11⟩
  simp only [*, -row11] at row11
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 2
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c12, r3, hr3, hc12, row12⟩
  simp only [*, -row12] at row12
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 1
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c13, r4, hr4, hc13, row13⟩
  simp only [*, -row13] at row13
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 1
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c14, r5, hr5, hc14, row14⟩
  simp only [*, -row14] at row14
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 1
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c15, r6, hr6, hc15, row15⟩
  simp only [*, -row15] at row15
  refine spec_bind (U64.add_spec ?_) ?_
  · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
  intro sum h_sum
  iterate 1
    refine spec_bind (m_spec _ _) ?_
    intro product h_product
    try simp only [UScalar.ofNatCore_val_eq] at h_product
    refine spec_bind (U64.add_spec ?_) ?_
    · grind only [U64.max_eq, limbRadix, UScalar.ofNatCore_val_eq]
    intro sum h_sum
  step -threadGrindState -grind -assumTac with montgomery_reduce.part2_spec
    as ⟨c16, r7, hr7, hc16, row16⟩
  simp only [*, -row16] at row16
  refine ⟨?_, ?_⟩
  · intro i hi
    interval_cases i <;>
      simp only [Array.getElem!_Nat_eq,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
    all_goals first | assumption | decide
  · simp only [asNat, highValue, Array.uScalarToNatRadix, limbRadix,
      UScalar.ofNatCore_val_eq, pow_mul, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.reduceAdd, constants.L, Array.getElem!_Nat_eq,
      Array.make, List.getElem!_cons_zero, List.getElem!_cons_succ,
      pow_zero, pow_one, one_mul, mul_zero, add_zero]
      at row9 row10 row11 row12 row13 row14 row15 row16 ⊢
    omega

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
  step -threadGrindState -grind -assumTac with montgomery_reduce_adjust_spec limbs h_bounds
    as ⟨l1, n1, l2, n2, l3, n3, l4, n4, n5, n6, n7, l8, c8, n8,
      hl1, hl2, hl3, hl4, hl8, h_n, h_carry, adjustment, h_adjustment, h_identity⟩
  simp only [hl1, hl2, hl3, hl4, hl8]
  step -threadGrindState -grind -assumTac with
    montgomery_reduce_extract_spec limbs n1 n2 n3 n4 n5 n6 n7 n8 c8 h_bounds h_n h_carry
    as ⟨r0, r1, r2, r3, r4, r5, r6, c16, r7, h_digits, h_extract⟩
  let low : Scalar29 := Array.make 9#usize [r0, r1, r2, r3, r4, r5, r6, r7, 0#u32]
  let quotient : Nat := asNat low + limbRadix ^ 8 * c16.val
  change quotient = highValue limbs n1 n2 n3 n4 n5 n6 n7 n8 c8 at h_extract
  rw [← h_extract] at h_identity
  have h_quotient : quotient < 2 * order := by
    apply Nat.lt_of_mul_lt_mul_right (a := montgomeryRadix)
    rw [← h_identity, Nat.mul_assoc, Nat.mul_comm order, two_mul]
    exact Nat.add_lt_add h_range (Nat.mul_lt_mul_of_pos_right h_adjustment order_pos)
  have h_small : quotient < 2 ^ 254 := by
    have := order_lt_two_pow_253
    omega
  have h_top : c16.val < 2 ^ 22 := by
    have h_weight : limbRadix ^ 8 * c16.val ≤ quotient := Nat.le_add_left _ _
    simp only [limbRadix] at h_weight
    omega
  refine spec_bind (UScalar.cast_inBounds_spec .U32 c16 ?_) ?_
  · rw [UScalar.max_UScalarTy_U32_eq, U32.max_eq]
    exact h_top.le.trans (by decide)
  intro r8 h_r8
  let pre : Scalar29 := Array.make 9#usize [r0, r1, r2, r3, r4, r5, r6, r7, r8]
  have h_pre : asNat pre = quotient := by
    simp only [pre, low, asNat, quotient, Array.uScalarToNatRadix,
      UScalar.ofNatCore_val_eq, pow_mul, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Array.getElem!_Nat_eq, Array.make,
      List.getElem!_cons_zero, List.getElem!_cons_succ, limbRadix,
      h_r8, pow_zero, pow_one, one_mul, mul_zero, add_zero]
  change IsNormalized low at h_digits
  have h_normalized : IsNormalized pre := by
    intro i hi
    have h_digit := h_digits i hi
    interval_cases i <;>
      simp only [pre, low, Array.getElem!_Nat_eq, Array.make,
        List.getElem!_cons_zero, List.getElem!_cons_succ] at h_digit ⊢
    all_goals first | exact h_digit | (rw [h_r8]; exact h_top.trans (by decide))
  have h_sub_spec := sub_spec pre constants.L h_normalized constants.L_limbs_lt
    (by rw [constants.L_spec]; omega)
    (by rw [constants.L_spec, h_pre]; omega)
  refine spec_mono h_sub_spec ?_
  intro result ⟨h_result, h_sub, h_canonical⟩
  rw [constants.L_spec, h_pre, Nat.add_mod_right] at h_sub
  refine ⟨?_, h_result, h_canonical⟩
  rw [← Nat.mod_mul_mod, h_sub, Nat.mod_mul_mod, ← h_identity, Nat.add_mul_mod_self_right]

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

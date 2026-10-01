/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Definitions
import Dalek32.Lint.Basic
import Dalek32.Scalar.Index
import Dalek32.Scalar.M
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Spec theorem for `square_internal`

Squares nine radix-`2^29` limbs into seventeen coefficients.
Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 292-323.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

private theorem index_eq (a : Scalar29) (j : Usize) (h_j : j.val < 9) :
    Insts.CoreOpsIndexIndexUsizeU32.index a j = ok a.val[j.val]! := by
  obtain ⟨result, h_eq, h_result⟩ := spec_imp_exists
    (Insts.CoreOpsIndexIndexUsizeU32.index_spec a j h_j)
  exact h_result ▸ h_eq

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::square_internal`**

Returns the exact square with coefficients below `5 * 2^59`. -/
@[step]
theorem square_internal_spec (a : Scalar29)
    (h_a : ∀ i < 9, a[i]!.val < limbRadix) :
    square_internal a ⦃ (result : Array U64 17#usize) =>
      wideAsNat result = asNat a ^ 2 ∧
      (∀ i < 17, result[i]!.val < 5 * 2 ^ 59) ⦄ := by
  simp only [limbRadix, Array.getElem!_Nat_eq] at h_a
  unfold square_internal
  -- Normalize the fixed array lookups before symbolic execution.
  simp only [index_eq, Nat.reduceLT, Array.index_usize, Array.getElem?_Usize_eq, Array.make,
    UScalar.ofNatCore_val_eq, List.getElem?_cons_zero, List.getElem?_cons_succ,
    bind_tc_ok]
  -- Each coefficient contains at most five products bounded by `2^30 * 2^29`.
  repeat' first
    | (step -threadGrindState -grind -assumTac with m_spec as ⟨product, h_product⟩
       have h_product_bound : product.val ≤ 2 ^ 30 * (2 ^ 29 - 1) := by
         rw [h_product]
         apply Nat.mul_le_mul
         · first | assumption | exact (h_a _ (by decide)).le.trans (by decide)
         · exact Nat.le_pred_of_lt (h_a _ (by decide)))
    | (step -threadGrindState -grind -assumTac with U64.add_spec
         as ⟨sum, h_sum⟩ by
         clear! a
         grind only [U64.max_eq])
    | (step -threadGrindState -assumTac with U32.mul_spec as ⟨doubled, h_doubled⟩
       have h_doubled_bound : doubled.val ≤ 2 ^ 30 := by grind only)
  constructor
  · simp only [wideAsNat, asNat, Array.uScalarToNatRadix,
      UScalar.ofNatCore_val_eq, pow_mul]
    generalize (2 ^ 29 : Nat) = B
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Array.getElem!_Nat_eq, List.getElem!_cons_zero,
      List.getElem!_cons_succ]
    simp only [*]
    ring
  · intro j hj
    interval_cases j <;>
      simp only [Array.getElem!_Nat_eq, List.getElem!_cons_zero,
        List.getElem!_cons_succ] <;> omega

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

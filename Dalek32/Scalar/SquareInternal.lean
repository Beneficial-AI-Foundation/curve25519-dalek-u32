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

private theorem double_spec_bounded (x : U32) (h_x : x.val ≤ 2 ^ 29) :
    x * 2#u32 ⦃ (result : U32) =>
      result.val = x.val * 2 ∧ result.val ≤ 2 ^ 30 ⦄ := by
  apply spec_mono (U32.mul_spec (x := x) (y := 2#u32)
    ((Nat.mul_le_mul_right 2 h_x).trans (by rw [U32.max_eq]; decide)))
  intro result h_result
  change result.val = x.val * 2 at h_result
  exact ⟨h_result, by omega⟩

private theorem u64_add_spec_bounded (x y : U64) {x_bound y_bound : Nat}
    (h_x : x.val ≤ x_bound) (h_y : y.val ≤ y_bound)
    (h_max : x_bound + y_bound ≤ U64.max) :
    x + y ⦃ (result : U64) =>
      result.val = x.val + y.val ∧ result.val ≤ x_bound + y_bound ⦄ := by
  apply spec_mono (U64.add_spec (x := x) (y := y) ((Nat.add_le_add h_x h_y).trans h_max))
  intro result h_result
  refine ⟨h_result, ?_⟩
  rw [h_result]
  exact Nat.add_le_add h_x h_y

attribute [local step] double_spec_bounded u64_add_spec_bounded

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::square_internal`**

Returns the exact square with coefficients below `2^62`. -/
@[step]
theorem square_internal_spec (a : Scalar29)
    (h_a : ∀ i < 9, a[i]!.val < limbRadix) :
    square_internal a ⦃ (result : Array U64 17#usize) =>
      wideAsNat result = asNat a ^ 2 ∧
      (∀ i < 17, result[i]!.val < 2 ^ 62) ⦄ := by
  simp only [limbRadix, Array.getElem!_Nat_eq] at h_a
  unfold square_internal
  -- Normalize the fixed array lookups before symbolic execution.
  simp only [index_eq, Nat.reduceLT, Array.index_usize, Array.getElem?_Usize_eq, Array.make,
    UScalar.ofNatCore_val_eq, List.getElem?_cons_zero, List.getElem?_cons_succ,
    bind_tc_ok]
  have h_mul := @m_spec_bounded
  -- Propagate limb bounds and discharge the remaining closed overflow checks.
  step* -threadGrindState -grind by
    first
    | exact (h_a _ (by decide)).le
    | rw [U64.max_eq]; decide
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

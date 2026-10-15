/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Dalek32.Field.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! # Wide-input field squaring

Verifies the extracted straight-line implementation on its overflow-maximal input
domain (`19 * limb < 2^32`), which includes the slack needed by point doubling.
All intermediate machine operations are checked for overflow.
The value identity accounts explicitly for the terms folded by `2^255 = 19 mod p`.

The overflow bounds are not written by hand: a single `repeat'` loop steps through
the extracted code and, for each operation, derives the result's bound from the
operands' bounds (`Nat.mul_le_mul`, `Nat.add_le_add`). Only the uniform input bound
`226050910 = ⌊(2^32 - 1) / 19⌋` and the final targets are stated explicitly, so the proof
survives renumbering of the extracted intermediates.
-/
open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[local step]
private theorem square_inner_m_spec (x y : U32) :
    square_inner.m x y ⦃ (result : U64) => result.val = x.val * y.val ⦄ := by
  unfold square_inner.m
  step*

/-- Reduction modulo `p` ignores an explicit multiple of `p`. -/
private theorem mod_eq_of_eq_add_mul {a b k : Nat} (h : b = a + p * k) :
    a % p = b % p := by
  rw [h, Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]

-- The long extracted bind chain exceeds the default simplifier recursion depth.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Symbolic execution and the ten-limb polynomial identity need a larger tactic budget.
/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::square_inner`

Under `SquareInputBounds`, returns the unreduced square modulo `p`, with every
coefficient small enough for `reduce`. -/
@[step]
theorem square_inner_spec (self : FieldElement2625) (h_bounds : SquareInputBounds self) :
    square_inner self ⦃ (z : Array U64 10#usize) =>
      Array.uScalarToNatField2625 z % p = toNat self ^ 2 % p ∧
      (∀ i < 10, z[i]!.val ≤ 2 ^ 64 - 2 ^ 39) ⦄ := by
  -- `19 * limb < 2^32` is exactly `limb ≤ 226050910`.
  have h_limb : ∀ i < 10, self[i]!.val ≤ 226050910 := fun i hi => by
    have h := h_bounds i hi
    omega
  unfold square_inner
  -- Symbolic execution. Every intermediate value gets an exact equation `h_*` and an
  -- upper bound `h_*_bound` built from its operands' bounds, so no numeric constant is
  -- written by hand; overflow side conditions are closed by evaluating those bounds.
  repeat' first
    | (step -threadGrindState -grind -assumTac with square_inner_m_spec
         as ⟨product, h_product⟩
       have h_product_bound :=
         h_product.trans_le (Nat.mul_le_mul (by assumption) (by assumption)))
    | (step -threadGrindState -grind -assumTac with U64.add_spec
         as ⟨sum, h_sum⟩ by
         exact Nat.le_trans (Nat.add_le_add (by assumption) (by assumption))
           (by norm_num [U64.max_eq])
       have h_sum_bound :=
         h_sum.trans_le (Nat.add_le_add (by assumption) (by assumption)))
    | (step -threadGrindState -grind -assumTac with U64.mul_spec
         as ⟨doubled, h_doubled⟩ by
         exact Nat.le_trans (Nat.mul_le_mul (by assumption) (le_refl _))
           (by norm_num [U64.max_eq, UScalar.ofNatCore_val_eq])
       have h_doubled_bound :=
         h_doubled.trans_le (Nat.mul_le_mul (by assumption) (le_refl _)))
    | (step -threadGrindState -grind -assumTac with U32.mul_spec
         as ⟨scaled, h_scaled⟩ by
         exact Nat.le_trans (Nat.mul_le_mul (le_refl _) (by assumption))
           (by norm_num [U32.max_eq, UScalar.ofNatCore_val_eq])
       have h_scaled_bound :=
         h_scaled.trans_le (Nat.mul_le_mul (le_refl _) (by assumption)))
    | (step -threadGrindState -grind -assumTac with Array.index_usize_spec
         as ⟨limb, h_limb_eq⟩ by simp
       have h_limb_bound : limb.val ≤ 226050910 := by
         rw [h_limb_eq, ← getElem!_pos, ← Array.getElem!_Nat_eq]
         exact h_limb _ (by decide))
    | (step -threadGrindState -grind -assumTac with Array.update_spec
         as ⟨z, h_z⟩ by simp)
  -- Substitute limb reads and array updates so the result is one explicit array.
  subst_vars
  constructor
  · -- The high-degree terms differ from the folded result by this explicit multiple of `p`.
    refine mod_eq_of_eq_add_mul (k :=
      2 ^ 2 * self[1]!.val * self[9]!.val +
        2 ^ 1 * self[2]!.val * self[8]!.val +
        2 ^ 27 * self[2]!.val * self[9]!.val +
        2 ^ 2 * self[3]!.val * self[7]!.val +
        2 ^ 27 * self[3]!.val * self[8]!.val +
        2 ^ 53 * self[3]!.val * self[9]!.val +
        2 ^ 1 * self[4]!.val * self[6]!.val +
        2 ^ 27 * self[4]!.val * self[7]!.val +
        2 ^ 52 * self[4]!.val * self[8]!.val +
        2 ^ 78 * self[4]!.val * self[9]!.val +
        2 ^ 1 * self[5]!.val * self[5]!.val +
        2 ^ 27 * self[5]!.val * self[6]!.val +
        2 ^ 53 * self[5]!.val * self[7]!.val +
        2 ^ 78 * self[5]!.val * self[8]!.val +
        2 ^ 104 * self[5]!.val * self[9]!.val +
        2 ^ 51 * self[6]!.val * self[6]!.val +
        2 ^ 78 * self[6]!.val * self[7]!.val +
        2 ^ 103 * self[6]!.val * self[8]!.val +
        2 ^ 129 * self[6]!.val * self[9]!.val +
        2 ^ 103 * self[7]!.val * self[7]!.val +
        2 ^ 129 * self[7]!.val * self[8]!.val +
        2 ^ 155 * self[7]!.val * self[9]!.val +
        2 ^ 153 * self[8]!.val * self[8]!.val +
        2 ^ 180 * self[8]!.val * self[9]!.val +
        2 ^ 205 * self[9]!.val * self[9]!.val) ?_
    simp only [toNat, Array.uScalarToNatField2625,
      Finset.sum_range_succ, Finset.sum_range_zero, Array.getElem!_Nat_eq,
      Array.set_val_eq, Array.repeat, UScalar.ofNatCore_val_eq]
    norm_num [p]
    simp only [*]
    ring
  · -- Each coefficient's tracked bound evaluates below `2^64 - 2^39`.
    intro j hj
    interval_cases j <;>
      simp only [Array.getElem!_Nat_eq, Array.set_val_eq, Array.repeat,
        UScalar.ofNatCore_val_eq] <;>
      norm_num <;>
      exact Nat.le_trans (by assumption) (by norm_num)
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Aeneas.Command.Decompose
import Dalek32.Definitions
import Dalek32.Lint.Basic
import Dalek32.Scalar.Index
import Dalek32.Scalar.M
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Spec theorem for `mul_internal`

Multiplies nine radix-`2^29` limbs into seventeen coefficients.
`asNat` and `wideAsNat` correspond to `Scalar52_as_Nat` and
`Scalar52_wide_as_Nat` in the u64 proof; here inputs have nine 29-bit limbs.
Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 234-287.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

private theorem index_eq (a : Scalar29) (j : Usize) (h_j : j.val < 9) :
    Insts.CoreOpsIndexIndexUsizeU32.index a j = ok a.val[j.val]! := by
  obtain ⟨result, h_eq, h_result⟩ := spec_imp_exists
    (Insts.CoreOpsIndexIndexUsizeU32.index_spec a j h_j)
  exact h_result ▸ h_eq

private theorem array_index_eq {α : Type} [Inhabited α] {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = ok a[i.val]! := by
  grind [Array.index_usize, Array.getElem!_Nat_eq]

private theorem array_update_eq {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (x : α) (hi : i.val < n.val) :
    Array.update a i x = ok (a.set i x) := by
  obtain ⟨result, h_eq, h_result⟩ := spec_imp_exists
    (Array.update_spec a i x (by simpa only [Array.length_eq] using hi))
  exact h_result ▸ h_eq

/-- The product coefficients used to identify the Karatsuba output. -/
private def productCoefficients (a b : Scalar29) : List Nat :=
  [
    a[0]!.val * b[0]!.val,
    a[0]!.val * b[1]!.val + a[1]!.val * b[0]!.val,
    a[0]!.val * b[2]!.val + a[1]!.val * b[1]!.val + a[2]!.val * b[0]!.val,
    a[0]!.val * b[3]!.val + a[1]!.val * b[2]!.val + a[2]!.val * b[1]!.val +
      a[3]!.val * b[0]!.val,
    a[0]!.val * b[4]!.val + a[1]!.val * b[3]!.val + a[2]!.val * b[2]!.val +
      a[3]!.val * b[1]!.val + a[4]!.val * b[0]!.val,
    a[0]!.val * b[5]!.val + a[1]!.val * b[4]!.val + a[2]!.val * b[3]!.val +
      a[3]!.val * b[2]!.val + a[4]!.val * b[1]!.val + a[5]!.val * b[0]!.val,
    a[0]!.val * b[6]!.val + a[1]!.val * b[5]!.val + a[2]!.val * b[4]!.val +
      a[3]!.val * b[3]!.val + a[4]!.val * b[2]!.val + a[5]!.val * b[1]!.val +
      a[6]!.val * b[0]!.val,
    a[0]!.val * b[7]!.val + a[1]!.val * b[6]!.val + a[2]!.val * b[5]!.val +
      a[3]!.val * b[4]!.val + a[4]!.val * b[3]!.val + a[5]!.val * b[2]!.val +
      a[6]!.val * b[1]!.val + a[7]!.val * b[0]!.val,
    a[0]!.val * b[8]!.val + a[1]!.val * b[7]!.val + a[2]!.val * b[6]!.val +
      a[3]!.val * b[5]!.val + a[4]!.val * b[4]!.val + a[5]!.val * b[3]!.val +
      a[6]!.val * b[2]!.val + a[7]!.val * b[1]!.val + a[8]!.val * b[0]!.val,
    a[1]!.val * b[8]!.val + a[2]!.val * b[7]!.val + a[3]!.val * b[6]!.val +
      a[4]!.val * b[5]!.val + a[5]!.val * b[4]!.val + a[6]!.val * b[3]!.val +
      a[7]!.val * b[2]!.val + a[8]!.val * b[1]!.val,
    a[2]!.val * b[8]!.val + a[3]!.val * b[7]!.val + a[4]!.val * b[6]!.val +
      a[5]!.val * b[5]!.val + a[6]!.val * b[4]!.val + a[7]!.val * b[3]!.val +
      a[8]!.val * b[2]!.val,
    a[3]!.val * b[8]!.val + a[4]!.val * b[7]!.val + a[5]!.val * b[6]!.val +
      a[6]!.val * b[5]!.val + a[7]!.val * b[4]!.val + a[8]!.val * b[3]!.val,
    a[4]!.val * b[8]!.val + a[5]!.val * b[7]!.val + a[6]!.val * b[6]!.val +
      a[7]!.val * b[5]!.val + a[8]!.val * b[4]!.val,
    a[5]!.val * b[8]!.val + a[6]!.val * b[7]!.val + a[7]!.val * b[6]!.val +
      a[8]!.val * b[5]!.val,
    a[6]!.val * b[8]!.val + a[7]!.val * b[7]!.val + a[8]!.val * b[6]!.val,
    a[7]!.val * b[8]!.val + a[8]!.val * b[7]!.val,
    a[8]!.val * b[8]!.val]

private theorem productCoefficients_lt (a b : Scalar29)
    (h_a : IsNormalized a) (h_b : IsNormalized b) :
    ∀ i < 17, (productCoefficients a b)[i]! < 2 ^ 62 := by
  have h_products (i : Nat) (hi : i < 9) (j : Nat) (hj : j < 9) :
      a[i]!.val * b[j]!.val ≤ 2 ^ 58 := by
    calc
      a[i]!.val * b[j]!.val ≤ limbRadix * limbRadix :=
        Nat.mul_le_mul (h_a i hi).le (h_b j hj).le
      _ = 2 ^ 58 := by decide
  simp only [Nat.forall_lt_succ_right] at h_products
  intro i hi
  interval_cases i <;>
    simp only [productCoefficients, List.getElem!_cons_zero, List.getElem!_cons_succ] <;>
    omega

private theorem productCoefficients_value (a b : Scalar29) :
    (∑ i ∈ Finset.range 17, 2 ^ (29 * i) * (productCoefficients a b)[i]!) =
      asNat a * asNat b := by
  simp only [asNat, Array.uScalarToNatRadix, UScalar.ofNatCore_val_eq, pow_mul]
  generalize (2 ^ 29 : Nat) = B
  simp only [productCoefficients, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Array.getElem!_Nat_eq, List.getElem!_cons_zero, List.getElem!_cons_succ]
  ring

/-- Interpret the pure wrapping operations in their machine-word ring. -/
private theorem wrapping_add_cast (x y : U64) :
    ((core.num.U64.wrapping_add x y).val : ZMod (2 ^ 64)) =
      (x.val : ZMod (2 ^ 64)) + (y.val : ZMod (2 ^ 64)) := by
  rw [← Nat.cast_add]
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  simp only [core.num.U64.wrapping_add_val_eq, UScalar.size, UScalarTy.numBits, Nat.mod_mod]

private theorem wrapping_sub_cast (x y : U64) :
    ((core.num.U64.wrapping_sub x y).val : ZMod (2 ^ 64)) =
      (x.val : ZMod (2 ^ 64)) - (y.val : ZMod (2 ^ 64)) := by
  have hy : y.val ≤ 2 ^ 64 := y.hBounds.le
  have h_cast : ((x.val + (2 ^ 64 - y.val) : Nat) : ZMod (2 ^ 64)) =
      (x.val : ZMod (2 ^ 64)) - (y.val : ZMod (2 ^ 64)) := by
    rw [Nat.cast_add, Nat.cast_sub hy, ZMod.natCast_self]
    ring
  rw [← h_cast]
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  simp only [core.num.U64.wrapping_sub_val_eq, UScalar.size, UScalarTy.numBits, Nat.mod_mod]

private theorem val_eq_of_cast_eq (x : U64) (n : Nat) (hn : n < 2 ^ 64)
    (h : (x.val : ZMod (2 ^ 64)) = (n : ZMod (2 ^ 64))) : x.val = n := by
  have hx : x.val < 2 ^ 64 := x.hBounds
  have h_mod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  simpa only [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hn] using h_mod

/-- The remaining Karatsuba updates in the machine-word ring. -/
private def combinedCoefficients (z : Array U64 17#usize) (a b : List U32) :
    List (ZMod (2 ^ 64)) :=
  let x (i : Nat) : ZMod (2 ^ 64) := a[i]!.val
  let y (i : Nat) : ZMod (2 ^ 64) := b[i]!.val
  let c (i : Nat) : ZMod (2 ^ 64) := z[i]!.val
  [c 0, c 1, c 2, c 3, c 4,
    x 0 * y 0 + c 5,
    x 0 * y 1 + x 1 * y 0 + c 6,
    x 0 * y 2 + x 1 * y 1 + x 2 * y 0 + c 7,
    x 0 * y 3 + x 1 * y 2 + x 2 * y 1 + x 3 * y 0 + c 8,
    x 0 * y 4 + x 1 * y 3 + x 2 * y 2 + x 3 * y 1 + x 4 * y 0 - c 9,
    x 1 * y 4 + x 2 * y 3 + x 3 * y 2 + x 4 * y 1 - c 10,
    x 2 * y 4 + x 3 * y 3 + x 4 * y 2 - c 11,
    x 3 * y 4 + x 4 * y 3 - c 12,
    c 13, c 14, c 15, c 16]

-- Generate the blocks and their equality with the extracted function.
set_option linter.hashCommand false in
#decompose mul_internal mul_internal_eq
  letRange 0 145 => mulInternalPrepare
  letRange 1 72 => mulInternalFinish

/-- Computes the partial coefficients and the four low-plus-high sums for each input. -/
add_decl_doc mulInternalPrepare

/-- Recombines the eight middle coefficients, retaining the other coefficients. -/
add_decl_doc mulInternalFinish

/-- The prepared state recombines to the product in the machine-word ring. -/
@[local step]
private theorem mulInternalPrepare_spec (a b : Scalar29)
    (h_a : IsNormalized a) (h_b : IsNormalized b) :
    mulInternalPrepare a b
      ⦃ (b4 : U32) (a4 : U32) (z : Array U64 17#usize)
        (a0 : U32) (a1 : U32) (a2 : U32) (a3 : U32)
        (b0 : U32) (b1 : U32) (b2 : U32) (b3 : U32) =>
      (∀ x ∈ [a0, a1, a2, a3, a4, b0, b1, b2, b3, b4], x.val ≤ 2 ^ 30) ∧
      (∀ i < 17,
        (combinedCoefficients z [a0, a1, a2, a3, a4] [b0, b1, b2, b3, b4])[i]! =
          (((productCoefficients a b)[i]! : Nat) : ZMod (2 ^ 64))) ⦄ := by
  simp only [IsNormalized, limbRadix, Array.getElem!_Nat_eq] at h_a h_b
  unfold mulInternalPrepare
  -- Resolve fixed array operations before stepping through the arithmetic.
  simp only [index_eq, Nat.reduceLT, Array.update, Array.index_usize, Array.repeat,
    Array.getElem?_Usize_eq, UScalar.ofNatCore_val_eq, List.replicate, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, lift, bind_tc_ok]
  repeat' (
    apply spec_bind
    first
    | (focus with_reducible exact m_spec _ _
       intro product h_product
       have h_product_bound : product.val ≤ 2 ^ 30 * 2 ^ 30 := by
         rw [h_product]
         apply Nat.mul_le_mul <;>
           first
           | assumption
           | exact (h_a _ (by decide)).le.trans (by decide)
           | exact (h_b _ (by decide)).le.trans (by decide))
    | (focus with_reducible exact U64.add_spec (by rw [U64.max_eq]; omega)
       intro sum h_sum)
    | (focus with_reducible exact U32.add_spec (by grind only [U32.max_eq])
       intro sum h_sum
       have h_sum_bound : sum.val ≤ 2 ^ 30 := by grind only))
  simp only [pure, spec_ok]
  constructor
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | assumption
      | exact (h_a _ (by decide)).le.trans (by decide)
      | exact (h_b _ (by decide)).le.trans (by decide)
  · intro i hi
    unfold combinedCoefficients productCoefficients
    interval_cases i <;>
      simp only [↓ List.getElem!_cons_zero, ↓ List.getElem!_cons_succ,
        ↓ Array.getElem!_Nat_eq, wrapping_add_cast, wrapping_sub_cast, *,
        Nat.cast_add, Nat.cast_mul] <;> ring

/-- Recombines a prepared array without losing any machine-word residue. -/
@[local step]
private theorem mulInternalFinish_spec (b4 a4 : U32) (z : Array U64 17#usize)
    (a0 a1 a2 a3 b0 b1 b2 b3 : U32)
    (h_bounds : ∀ x ∈ [a0, a1, a2, a3, a4, b0, b1, b2, b3, b4], x.val ≤ 2 ^ 30) :
    mulInternalFinish b4 a4 z a0 a1 a2 a3 b0 b1 b2 b3 ⦃ (result : Array U64 17#usize) =>
      ∀ i < 17, (result[i]!.val : ZMod (2 ^ 64)) =
        (combinedCoefficients z [a0, a1, a2, a3, a4] [b0, b1, b2, b3, b4])[i]! ⦄ := by
  unfold mulInternalFinish
  simp (disch := (simp only [Array.length_eq, UScalar.ofNatCore_val_eq]; decide)) only
    [array_index_eq, array_update_eq, ↓ Array.getElem!_Nat_set_ne,
      UScalar.ofNatCore_val_eq, lift, bind_tc_ok]
  simp only [Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
    List.getElem!_cons_succ]
  repeat' (
    apply spec_bind
    first
    | (focus with_reducible exact m_spec _ _
       intro product h_product
       have h_product_bound : product.val ≤ 2 ^ 30 * 2 ^ 30 := by
         rw [h_product]
         apply Nat.mul_le_mul <;> exact h_bounds _ (by simp))
    | (focus with_reducible exact U64.add_spec (by rw [U64.max_eq]; omega)
       intro sum h_sum))
  simp only [spec_ok]
  intro i hi
  interval_cases i <;>
    simp (disch := first | decide |
      (simp only [List.length_set, Array.length_eq, UScalar.ofNatCore_val_eq]; decide)) only
      [combinedCoefficients, List.getElem!_cons_zero, List.getElem!_cons_succ,
        Array.getElem!_Nat_eq, Array.set_val_eq, UScalar.ofNatCore_val_eq,
        ↓ List.set_getElem!_eq, ↓ List.set_getElem!_ne,
        wrapping_add_cast, wrapping_sub_cast, *, Nat.cast_add, Nat.cast_mul]

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::mul_internal`**

Returns the exact product with coefficients below `2^62`. -/
@[step]
theorem mul_internal_spec (a b : Scalar29)
    (h_a : IsNormalized a) (h_b : IsNormalized b) :
    mul_internal a b ⦃ (result : Array U64 17#usize) =>
      wideAsNat result = asNat a * asNat b ∧
      (∀ i < 17, result[i]!.val < 2 ^ 62) ⦄ := by
  rw [mul_internal_eq]
  step with mulInternalPrepare_spec a b h_a h_b
    as ⟨b4, a4, z, a0, a1, a2, a3, b0, b1, b2, b3, h_bounds, h_prepared⟩
  apply spec_mono (mulInternalFinish_spec b4 a4 z a0 a1 a2 a3 b0 b1 b2 b3 h_bounds)
  intro result h_result
  have h_coefficients (i : Nat) (hi : i < 17) :
      result[i]!.val = (productCoefficients a b)[i]! := by
    apply val_eq_of_cast_eq _ _ ((productCoefficients_lt a b h_a h_b i hi).trans (by decide))
    exact (h_result i hi).trans (h_prepared i hi)
  constructor
  · unfold wideAsNat Array.uScalarToNatRadix
    simp only [UScalar.ofNatCore_val_eq]
    calc
      (∑ i ∈ Finset.range 17, 2 ^ (29 * i) * result[i]!.val) =
          ∑ i ∈ Finset.range 17, 2 ^ (29 * i) * (productCoefficients a b)[i]! := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [h_coefficients i (Finset.mem_range.mp hi)]
      _ = asNat a * asNat b := productCoefficients_value a b
  · intro i hi
    rw [h_coefficients i hi]
    exact productCoefficients_lt a b h_a h_b i hi

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

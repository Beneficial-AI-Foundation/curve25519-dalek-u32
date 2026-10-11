/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
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

/-- The schoolbook coefficients used to identify the Karatsuba output. -/
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

/-- Separate fixed array normalization from arithmetic verification. -/
private theorem mul_internal_eq (a b : Scalar29) :
    mul_internal a b = (do
    let i2 ← m (a.val[0]!) (b.val[0]!)
    let i4 ← m (a.val[0]!) (b.val[1]!)
    let i6 ← m (a.val[1]!) (b.val[0]!)
    let i7 ← i4 + i6
    let i9 ← m (a.val[0]!) (b.val[2]!)
    let i10 ← m (a.val[1]!) (b.val[1]!)
    let i11 ← i9 + i10
    let i13 ← m (a.val[2]!) (b.val[0]!)
    let i14 ← i11 + i13
    let i16 ← m (a.val[0]!) (b.val[3]!)
    let i17 ← m (a.val[1]!) (b.val[2]!)
    let i18 ← i16 + i17
    let i19 ← m (a.val[2]!) (b.val[1]!)
    let i20 ← i18 + i19
    let i22 ← m (a.val[3]!) (b.val[0]!)
    let i23 ← i20 + i22
    let i25 ← m (a.val[0]!) (b.val[4]!)
    let i26 ← m (a.val[1]!) (b.val[3]!)
    let i27 ← i25 + i26
    let i28 ← m (a.val[2]!) (b.val[2]!)
    let i29 ← i27 + i28
    let i30 ← m (a.val[3]!) (b.val[1]!)
    let i31 ← i29 + i30
    let i33 ← m (a.val[4]!) (b.val[0]!)
    let i34 ← i31 + i33
    let i35 ← m (a.val[1]!) (b.val[4]!)
    let i36 ← m (a.val[2]!) (b.val[3]!)
    let i37 ← i35 + i36
    let i38 ← m (a.val[3]!) (b.val[2]!)
    let i39 ← i37 + i38
    let i40 ← m (a.val[4]!) (b.val[1]!)
    let i41 ← i39 + i40
    let i42 ← m (a.val[2]!) (b.val[4]!)
    let i43 ← m (a.val[3]!) (b.val[3]!)
    let i44 ← i42 + i43
    let i45 ← m (a.val[4]!) (b.val[2]!)
    let i46 ← i44 + i45
    let i47 ← m (a.val[3]!) (b.val[4]!)
    let i48 ← m (a.val[4]!) (b.val[3]!)
    let i49 ← i47 + i48
    let i50 ← m (a.val[4]!) (b.val[4]!)
    let i56 ← m (a.val[5]!) (b.val[5]!)
    let i60 ← m (a.val[5]!) (b.val[6]!)
    let i62 ← m (a.val[6]!) (b.val[5]!)
    let i63 ← i60 + i62
    let i67 ← m (a.val[5]!) (b.val[7]!)
    let i68 ← m (a.val[6]!) (b.val[6]!)
    let i69 ← i67 + i68
    let i71 ← m (a.val[7]!) (b.val[5]!)
    let i72 ← i69 + i71
    let i75 ← m (a.val[5]!) (b.val[8]!)
    let i76 ← m (a.val[6]!) (b.val[7]!)
    let i77 ← i75 + i76
    let i78 ← m (a.val[7]!) (b.val[6]!)
    let i79 ← i77 + i78
    let i81 ← m (a.val[8]!) (b.val[5]!)
    let i82 ← i79 + i81
    let i83 ← m (a.val[6]!) (b.val[8]!)
    let i84 ← m (a.val[7]!) (b.val[7]!)
    let i85 ← i83 + i84
    let i86 ← m (a.val[8]!) (b.val[6]!)
    let i87 ← i85 + i86
    let i88 ← m (a.val[7]!) (b.val[8]!)
    let i89 ← m (a.val[8]!) (b.val[7]!)
    let i90 ← i88 + i89
    let i91 ← m (a.val[8]!) (b.val[8]!)
    let i113 ← a.val[0]! + a.val[5]!
    let i114 ← a.val[1]! + a.val[6]!
    let i115 ← a.val[2]! + a.val[7]!
    let i116 ← a.val[3]! + a.val[8]!
    let i117 ← b.val[0]! + b.val[5]!
    let i118 ← b.val[1]! + b.val[6]!
    let i119 ← b.val[2]! + b.val[7]!
    let i120 ← b.val[3]! + b.val[8]!
    let i123 ← m (i113) (i117)
    let i127 ← m (i113) (i118)
    let i129 ← m (i114) (i117)
    let i130 ← i127 + i129
    let i134 ← m (i113) (i119)
    let i135 ← m (i114) (i118)
    let i136 ← i134 + i135
    let i138 ← m (i115) (i117)
    let i139 ← i136 + i138
    let i143 ← m (i113) (i120)
    let i144 ← m (i114) (i119)
    let i145 ← i143 + i144
    let i146 ← m (i115) (i118)
    let i147 ← i145 + i146
    let i149 ← m (i116) (i117)
    let i150 ← i147 + i149
    let i153 ← m (i113) (b.val[4]!)
    let i154 ← m (i114) (i120)
    let i155 ← i153 + i154
    let i156 ← m (i115) (i119)
    let i157 ← i155 + i156
    let i158 ← m (i116) (i118)
    let i159 ← i157 + i158
    let i160 ← m (a.val[4]!) (i117)
    let i161 ← i159 + i160
    let i164 ← m (i114) (b.val[4]!)
    let i165 ← m (i115) (i120)
    let i166 ← i164 + i165
    let i167 ← m (i116) (i119)
    let i168 ← i166 + i167
    let i169 ← m (a.val[4]!) (i118)
    let i170 ← i168 + i169
    let i173 ← m (i115) (b.val[4]!)
    let i174 ← m (i116) (i120)
    let i175 ← i173 + i174
    let i176 ← m (a.val[4]!) (i119)
    let i177 ← i175 + i176
    let i180 ← m (i116) (b.val[4]!)
    let i181 ← m (a.val[4]!) (i120)
    let i182 ← i180 + i181
    ok (Array.make 17#usize [
      i2,
      i7,
      i14,
      i23,
      i34,
      core.num.U64.wrapping_add (i123) (core.num.U64.wrapping_sub (core.num.U64.wrapping_sub (i41)
        (i56)) (i2)),
      core.num.U64.wrapping_add (i130) (core.num.U64.wrapping_sub (core.num.U64.wrapping_sub (i46)
        (i63)) (i7)),
      core.num.U64.wrapping_add (i139) (core.num.U64.wrapping_sub (core.num.U64.wrapping_sub (i49)
        (i72)) (i14)),
      core.num.U64.wrapping_add (i150) (core.num.U64.wrapping_sub (core.num.U64.wrapping_sub (i50)
        (i23)) (i82)),
      core.num.U64.wrapping_sub (i161) (core.num.U64.wrapping_add (i87) (i34)),
      core.num.U64.wrapping_sub (i170) (core.num.U64.wrapping_add (i90) (core.num.U64.wrapping_sub
        (i41) (i56))),
      core.num.U64.wrapping_sub (i177) (core.num.U64.wrapping_add (i91) (core.num.U64.wrapping_sub
        (i46) (i63))),
      core.num.U64.wrapping_sub (i182) (core.num.U64.wrapping_sub (i49) (i72)),
      i82,
      i87,
      i90,
      i91])) := by
  unfold mul_internal
  simp only [index_eq, Nat.reduceLT, Array.update, Array.index_usize, Array.repeat, Array.make,
    Array.getElem?_Usize_eq, UScalar.ofNatCore_val_eq, List.replicate, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, lift, bind_tc_ok]

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::mul_internal`**

Returns the exact product with coefficients below `2^62`. -/
@[step]
theorem mul_internal_spec (a b : Scalar29)
    (h_a : IsNormalized a) (h_b : IsNormalized b) :
    mul_internal a b ⦃ (result : Array U64 17#usize) =>
      wideAsNat result = asNat a * asNat b ∧
      (∀ i < 17, result[i]!.val < 2 ^ 62) ⦄ := by
  suffices h_coefficients : mul_internal a b ⦃ (result : Array U64 17#usize) =>
      ∀ i < 17, result[i]!.val = (productCoefficients a b)[i]! ⦄ by
    apply spec_mono h_coefficients
    intro result h_result
    constructor
    · unfold wideAsNat Array.uScalarToNatRadix
      simp only [UScalar.ofNatCore_val_eq]
      calc
        (∑ i ∈ Finset.range 17, 2 ^ (29 * i) * result[i]!.val) =
            ∑ i ∈ Finset.range 17, 2 ^ (29 * i) * (productCoefficients a b)[i]! := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [h_result i (Finset.mem_range.mp hi)]
        _ = asNat a * asNat b := productCoefficients_value a b
    · intro i hi
      rw [h_result i hi]
      exact productCoefficients_lt a b h_a h_b i hi
  have h_coeff_bounds := productCoefficients_lt a b h_a h_b
  simp only [IsNormalized, limbRadix, Array.getElem!_Nat_eq] at h_a h_b
  rw [mul_internal_eq]
  -- Match each operation separately from the long continuation.
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
    | (focus with_reducible exact U64.add_spec (by clear! a b; rw [U64.max_eq]; omega)
       intro sum h_sum)
    | (focus with_reducible exact U32.add_spec (by grind only [U32.max_eq])
       intro sum h_sum
       have h_sum_bound : sum.val ≤ 2 ^ 30 := by grind only))
  simp only [spec_ok, Array.make]
  intro i hi
  apply val_eq_of_cast_eq _ _ ((h_coeff_bounds i hi).trans (by decide))
  -- Expand the recorded operation equations only inside each coefficient's ring identity.
  interval_cases i <;>
    simp only [productCoefficients, Array.getElem!_Nat_eq, List.getElem!_cons_zero,
      List.getElem!_cons_succ, wrapping_add_cast, wrapping_sub_cast, *, Nat.cast_add,
      Nat.cast_mul] <;> ring

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

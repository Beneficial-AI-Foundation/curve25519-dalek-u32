/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.Field.Reduce

/-!
# Spec theorem for `negate`

`negate self` computes `-self` as `16 * p - self` limbwise in `u32`, to avoid underflow. The limbs
of `16 * p` in the alternating `2^26/2^25` radix are `0x3ffffed << 4` for limb `0`,
`0x1ffffff << 4` for odd limbs and `0x3ffffff << 4` for the other even limbs. The ten differences
are widened to `u64` and passed to `reduce`, so the result represents `-self` modulo `p`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 302:4-317:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

-- Note: a looser bound (self[i] < 8 * 2^26, roughly) would also hold; 3 * 2^26 matches mul.
/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::negate`
If every limb of `self` is below `3 * 2 ^ 26`, `negate` succeeds and returns a reduced element
(every limb below `2 ^ 26`) `r` with `r + self ≡ 0 [MOD p]`.
The proof unfolds `negate`, resolves the limb reads with `index_usize_eq` and runs `step*`, which
discharges the `u32` side conditions. The shifts by `4` give the constants `c_0 = 2 ^ 30 - 304`,
`c_i = 2 ^ 29 - 16` for odd `i` and `c_i = 2 ^ 30 - 16` for even `i ≥ 2`, so the subtraction does
not underflow since `self[i] < 3 * 2 ^ 26 < 2 ^ 29 - 16 ≤ c_i`. The three constants are then
evaluated by `simp` with `Nat.shiftLeft_eq`, and each widened limb is rewritten to
`z_i = c_i - self[i]`. As `z_i < 2 ^ 30`, `getElem!_make_le` with one `omega` per limb discharges
the precondition of `reduce`, and the limb bound is the first postcondition of `reduce_spec`. For
the value, its congruence and `uScalarToNatField2625_make` reduce the goal, via
`Nat.mod_eq_zero_of_dvd` with witness `16`, to the exact identity
`z.toNat + self.toNat = p * 16`. After `toNat_expand` and the per-limb rewrites, `omega` with
`p_add_19` closes it, as the constants `c_i` at their limb weights sum to `16 * p`. -/
@[step]
theorem negate_spec (self : FieldElement2625)
    (h_self : ∀ i < 10, self[i]!.val < 3 * 2 ^ 26) :
    negate self ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val < 2 ^ 26) ∧
      (result.toNat + self.toNat) % p = 0 ⦄ := by
  have hs0 : self[0]!.val < 3 * 2 ^ 26 := h_self 0 (by decide)
  have hs1 : self[1]!.val < 3 * 2 ^ 26 := h_self 1 (by decide)
  have hs2 : self[2]!.val < 3 * 2 ^ 26 := h_self 2 (by decide)
  have hs3 : self[3]!.val < 3 * 2 ^ 26 := h_self 3 (by decide)
  have hs4 : self[4]!.val < 3 * 2 ^ 26 := h_self 4 (by decide)
  have hs5 : self[5]!.val < 3 * 2 ^ 26 := h_self 5 (by decide)
  have hs6 : self[6]!.val < 3 * 2 ^ 26 := h_self 6 (by decide)
  have hs7 : self[7]!.val < 3 * 2 ^ 26 := h_self 7 (by decide)
  have hs8 : self[8]!.val < 3 * 2 ^ 26 := h_self 8 (by decide)
  have hs9 : self[9]!.val < 3 * 2 ^ 26 := h_self 9 (by decide)
  clear h_self
  unfold negate
  simp only [index_usize_eq, Nat.reduceLT, UScalar.ofNatCore_val_eq, bind_tc_ok]
  step*
  all_goals
    have hc0 : i.val = 2 ^ 30 - 304 := by
      simp [i_post1, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hc1 : i4.val = 2 ^ 29 - 16 := by
      simp [i4_post1, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hc2 : i8.val = 2 ^ 30 - 16 := by
      simp [i8_post1, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hz0 : i3.val = 2 ^ 30 - 304 - self[0]!.val := by
      rw [i3_post, U32.cast_U64_val_eq, i2_post1, hc0]
    have hz1 : i7.val = 2 ^ 29 - 16 - self[1]!.val := by
      rw [i7_post, U32.cast_U64_val_eq, i6_post1, hc1]
    have hz2 : i11.val = 2 ^ 30 - 16 - self[2]!.val := by
      rw [i11_post, U32.cast_U64_val_eq, i10_post1, hc2]
    have hz3 : i14.val = 2 ^ 29 - 16 - self[3]!.val := by
      rw [i14_post, U32.cast_U64_val_eq, i13_post1, hc1]
    have hz4 : i17.val = 2 ^ 30 - 16 - self[4]!.val := by
      rw [i17_post, U32.cast_U64_val_eq, i16_post1, hc2]
    have hz5 : i20.val = 2 ^ 29 - 16 - self[5]!.val := by
      rw [i20_post, U32.cast_U64_val_eq, i19_post1, hc1]
    have hz6 : i23.val = 2 ^ 30 - 16 - self[6]!.val := by
      rw [i23_post, U32.cast_U64_val_eq, i22_post1, hc2]
    have hz7 : i26.val = 2 ^ 29 - 16 - self[7]!.val := by
      rw [i26_post, U32.cast_U64_val_eq, i25_post1, hc1]
    have hz8 : i29.val = 2 ^ 30 - 16 - self[8]!.val := by
      rw [i29_post, U32.cast_U64_val_eq, i28_post1, hc2]
    have hz9 : i32.val = 2 ^ 29 - 16 - self[9]!.val := by
      rw [i32_post, U32.cast_U64_val_eq, i31_post1, hc1]
  · exact getElem!_make_le _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · refine ⟨neg_post1, ?_⟩
    rw [Nat.add_mod, neg_post2, ← Nat.add_mod, uScalarToNatField2625_make]
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨16, ?_⟩
    rw [toNat_expand, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9]
    have := p_add_19
    omega

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

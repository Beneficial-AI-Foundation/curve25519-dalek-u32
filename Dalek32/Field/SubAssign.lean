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
# Spec theorem for `sub_assign`

`sub_assign self _rhs` computes `self - _rhs` as `(self + 16 * p) - _rhs` limbwise in `u32`, to
avoid underflow. The limbs of `16 * p` in the alternating `2^26/2^25` radix are
`0x3ffffed << 4` for limb `0`, `0x1ffffff << 4` for odd limbs and `0x3ffffff << 4` for the other
even limbs. The ten differences are widened to `u64` and passed to `reduce`, so the result
represents `self - _rhs` modulo `p`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 87:4-105:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts
namespace CoreOpsArithSubAssignSharedBFieldElement2625

-- Note: the arithmetic also admits a looser bound (_rhs[i] < 8 * 2^26, roughly);
-- 3 * 2^26 is kept to match mul, since every caller in the crate meets it.
/-- **Spec theorem for**
`<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
core::ops::SubAssign<&FieldElement2625>>::sub_assign`
If every limb of both operands is below `3 * 2 ^ 26`, `sub_assign` succeeds and returns a reduced
element (every limb below `2 ^ 26`) `r` with `r + _rhs ≡ self [MOD p]`.
The proof unfolds `sub_assign`, resolves the limb reads with `index_usize_eq` and runs `step*`,
which discharges the `u32` side conditions. The shifts by `4` give the constants
`c_0 = 2 ^ 30 - 304`, `c_i = 2 ^ 29 - 16` for odd `i` and `c_i = 2 ^ 30 - 16` for even `i ≥ 2`, so
`self[i] + c_i < 3 * 2 ^ 26 + 2 ^ 30 < 2 ^ 32` does not overflow, and the subtraction does not
underflow since `_rhs[i] < 3 * 2 ^ 26 < 2 ^ 29 - 16 ≤ c_i`. The three constants are then evaluated
by `simp` with `Nat.shiftLeft_eq`, and each widened limb is rewritten to
`z_i = self[i] + c_i - _rhs[i]`. As `z_i < 2 ^ 31`, `getElem!_make_le` with one `omega` per limb
discharges the precondition of `reduce`, and the limb bound is the first postcondition of
`reduce_spec`. For the value, its congruence, `uScalarToNatField2625_make` and
`Nat.add_mul_mod_self_right`, which replaces `self.toNat` by `self.toNat + 16 * p` modulo `p`,
reduce the goal to the exact identity `z.toNat + _rhs.toNat = self.toNat + 16 * p`. After
`toNat_expand` and the per-limb rewrites, `omega` with `p_add_19` closes it, as the constants
`c_i` at their limb weights sum to `16 * p`. -/
@[step]
theorem sub_assign_spec (self _rhs : FieldElement2625)
    (h_self : ∀ i < 10, self[i]!.val < 3 * 2 ^ 26)
    (h_rhs : ∀ i < 10, _rhs[i]!.val < 3 * 2 ^ 26) :
    sub_assign self _rhs ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val < 2 ^ 26) ∧
      (result.toNat + _rhs.toNat) % p = self.toNat % p ⦄ := by
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
  have hr0 : _rhs[0]!.val < 3 * 2 ^ 26 := h_rhs 0 (by decide)
  have hr1 : _rhs[1]!.val < 3 * 2 ^ 26 := h_rhs 1 (by decide)
  have hr2 : _rhs[2]!.val < 3 * 2 ^ 26 := h_rhs 2 (by decide)
  have hr3 : _rhs[3]!.val < 3 * 2 ^ 26 := h_rhs 3 (by decide)
  have hr4 : _rhs[4]!.val < 3 * 2 ^ 26 := h_rhs 4 (by decide)
  have hr5 : _rhs[5]!.val < 3 * 2 ^ 26 := h_rhs 5 (by decide)
  have hr6 : _rhs[6]!.val < 3 * 2 ^ 26 := h_rhs 6 (by decide)
  have hr7 : _rhs[7]!.val < 3 * 2 ^ 26 := h_rhs 7 (by decide)
  have hr8 : _rhs[8]!.val < 3 * 2 ^ 26 := h_rhs 8 (by decide)
  have hr9 : _rhs[9]!.val < 3 * 2 ^ 26 := h_rhs 9 (by decide)
  clear h_self h_rhs
  unfold sub_assign
  simp only [index_usize_eq, Nat.reduceLT, UScalar.ofNatCore_val_eq, bind_tc_ok]
  step*
  all_goals
    have hc0 : i1.val = 2 ^ 30 - 304 := by
      simp [i1_post1, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hc1 : i7.val = 2 ^ 29 - 16 := by
      simp [i7_post1, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hc2 : i13.val = 2 ^ 30 - 16 := by
      simp [i13_post1, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hz0 : i5.val = self[0]!.val + (2 ^ 30 - 304) - _rhs[0]!.val := by
      rw [i5_post, U32.cast_U64_val_eq, i4_post1, i2_post, hc0]
    have hz1 : i11.val = self[1]!.val + (2 ^ 29 - 16) - _rhs[1]!.val := by
      rw [i11_post, U32.cast_U64_val_eq, i10_post1, i8_post, hc1]
    have hz2 : i17.val = self[2]!.val + (2 ^ 30 - 16) - _rhs[2]!.val := by
      rw [i17_post, U32.cast_U64_val_eq, i16_post1, i14_post, hc2]
    have hz3 : i22.val = self[3]!.val + (2 ^ 29 - 16) - _rhs[3]!.val := by
      rw [i22_post, U32.cast_U64_val_eq, i21_post1, i19_post, hc1]
    have hz4 : i27.val = self[4]!.val + (2 ^ 30 - 16) - _rhs[4]!.val := by
      rw [i27_post, U32.cast_U64_val_eq, i26_post1, i24_post, hc2]
    have hz5 : i32.val = self[5]!.val + (2 ^ 29 - 16) - _rhs[5]!.val := by
      rw [i32_post, U32.cast_U64_val_eq, i31_post1, i29_post, hc1]
    have hz6 : i37.val = self[6]!.val + (2 ^ 30 - 16) - _rhs[6]!.val := by
      rw [i37_post, U32.cast_U64_val_eq, i36_post1, i34_post, hc2]
    have hz7 : i42.val = self[7]!.val + (2 ^ 29 - 16) - _rhs[7]!.val := by
      rw [i42_post, U32.cast_U64_val_eq, i41_post1, i39_post, hc1]
    have hz8 : i47.val = self[8]!.val + (2 ^ 30 - 16) - _rhs[8]!.val := by
      rw [i47_post, U32.cast_U64_val_eq, i46_post1, i44_post, hc2]
    have hz9 : i52.val = self[9]!.val + (2 ^ 29 - 16) - _rhs[9]!.val := by
      rw [i52_post, U32.cast_U64_val_eq, i51_post1, i49_post, hc1]
  · exact getElem!_make_le _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · refine ⟨fe_post1, ?_⟩
    rw [Nat.add_mod, fe_post2, ← Nat.add_mod, uScalarToNatField2625_make,
      ← Nat.add_mul_mod_self_right self.toNat 16 p]
    apply congrArg (· % p)
    rw [toNat_expand, toNat_expand, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9]
    have := p_add_19
    omega

end CoreOpsArithSubAssignSharedBFieldElement2625
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts

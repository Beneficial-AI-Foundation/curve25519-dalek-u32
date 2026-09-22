/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Auxiliary
import Dalek32.Lint.Basic
import Dalek32.Scalar.ConditionalAddL
import Dalek32.Scalar.Zero
import Dalek32.Subtle.ChoiceFromU8

/-!
# `sub`

Subtraction with conditional correction by the scalar order.
Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 188-202.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

namespace Sub

/-- Normalized difference prefix and borrow conservation. -/
def Invariant (a b : Scalar29) (iter : core.ops.range.Range Usize)
    (difference : Scalar29) (borrow : U32) : Prop :=
  iter.end = 9#usize ∧
  iter.start.val ≤ 9 ∧
  (∀ j < 9, difference[j]!.val < limbRadix) ∧
  (∀ j, iter.start.val ≤ j → j < 9 → difference[j]!.val = 0) ∧
  asNat difference + (∑ j ∈ Finset.range iter.start.val, 2 ^ (29 * j) * b[j]!.val) =
    (∑ j ∈ Finset.range iter.start.val, 2 ^ (29 * j) * a[j]!.val) +
      2 ^ (29 * iter.start.val) * (borrow.val / 2 ^ 31)

end Sub

namespace sub_loop

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::sub` (loop body)**

Preserves the difference prefix and advances the iterator. -/
@[step]
theorem body_spec (a b : Scalar29) (mask : U32) (iter : core.ops.range.Range Usize)
    (difference : Scalar29) (borrow : U32)
    (h_a : ∀ j < 9, a[j]!.val < limbRadix)
    (h_b : ∀ j < 9, b[j]!.val < limbRadix)
    (h_mask : mask.val = limbRadix - 1)
    (h_inv : Sub.Invariant a b iter difference borrow) :
    body a b mask iter difference borrow ⦃
      (result : ControlFlow (core.ops.range.Range Usize × Scalar29 × U32) (Scalar29 × U32)) =>
      match result with
      | .done (difference', borrow') =>
        iter.start.val = 9 ∧ difference' = difference ∧ borrow' = borrow
      | .cont (iter', difference', borrow') =>
        Sub.Invariant a b iter' difference' borrow' ∧
        iter'.start.val = iter.start.val + 1 ⦄ := by
  rcases h_inv with ⟨h_end, h_start, h_difference, h_suffix, h_value⟩
  unfold body
  step -threadGrindState -grind as ⟨next, iter', h_next, h_end'⟩
  simp only [h_end, UScalar.ofNatCore_val_eq] at h_next
  by_cases hi : iter.start.val < 9
  · simp only [hi, ↓reduceIte] at h_next
    rcases h_next with ⟨h_next, h_advance⟩
    simp only [h_next]
    step with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨x, h_x⟩
    step with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨y, h_y⟩
    have h_x_bound : x.val < limbRadix := by
      simpa only [h_x, Array.getElem!_Nat_eq] using h_a iter.start.val hi
    have h_y_bound : y.val < limbRadix := by
      simpa only [h_y, Array.getElem!_Nat_eq] using h_b iter.start.val hi
    step as ⟨incoming, h_incoming⟩
    simp only [Nat.shiftRight_eq_div_pow] at h_incoming
    have h_incoming_bound : incoming.val < 2 := by scalar_tac
    step with U32.add_spec as ⟨subtrahend, h_subtrahend⟩ by
      simp only [limbRadix] at h_y_bound
      scalar_tac
    step as ⟨borrow', h_borrow'⟩
    have h_wrapped : borrow'.val =
        (x.val + (2 ^ 32 - subtrahend.val)) % 2 ^ 32 := by
      simp only [h_borrow', core.num.U32.wrapping_sub_val_eq,
        UScalar.size, UScalarTy.numBits]
    have h_row : borrow'.val % limbRadix + y.val + incoming.val =
        x.val + limbRadix * (borrow'.val / 2 ^ 31) := by
      simp only [limbRadix] at h_x_bound h_y_bound ⊢
      omega
    step with Insts.CoreOpsIndexIndexMutUsizeU32.index_mut_spec
      as ⟨_limb, back, _h_limb, h_back⟩
    step as ⟨digit, h_digit⟩
    have h_digit_value : digit.val = borrow'.val % limbRadix := by
      simp only [h_digit, UScalar.val_and, h_mask, limbRadix,
        Nat.and_two_pow_sub_one_eq_mod]
    have h_digit_bound : digit.val < limbRadix := by grind only [limbRadix]
    have h_normalized : ∀ j < 9, (difference.set iter.start digit)[j]!.val < limbRadix := by
      clear * - h_difference h_digit_bound
      simp only [Array.getElem!_Nat_eq, Array.set_val_eq] at *
      grind
    have h_suffix' : ∀ j, iter'.start.val ≤ j → j < 9 →
        (difference.set iter.start digit)[j]!.val = 0 := by
      intro j hj hj9
      simpa only [Array.getElem!_Nat_set_ne difference iter.start j digit (by omega)]
        using h_suffix j (by omega) hj9
    have h_update := Array.uScalarToNatRadix_set difference 29 iter.start digit hi
    change asNat (difference.set iter.start digit) +
        2 ^ (29 * iter.start.val) * difference[iter.start.val]!.val =
      asNat difference + 2 ^ (29 * iter.start.val) * digit.val at h_update
    rw [h_suffix iter.start.val (Nat.le_refl _) hi, Nat.mul_zero, Nat.add_zero] at h_update
    simp only [← h_digit_value, h_y, h_x, h_incoming, ← Array.getElem!_Nat_eq] at h_row
    simp only [h_back]
    change Sub.Invariant a b iter' (difference.set iter.start digit) borrow' ∧
      iter'.start.val = iter.start.val + 1
    refine ⟨⟨h_end'.trans h_end, by omega, h_normalized, h_suffix', ?_⟩, h_advance⟩
    rw [h_advance, h_update]
    simp only [Finset.sum_range_succ, Nat.mul_add, Nat.mul_one, Nat.pow_add,
      Nat.mul_assoc]
    clear * - h_value h_row
    grind only [limbRadix]
  · simp only [hi, ↓reduceIte] at h_next
    simp only [h_next.1, spec_ok]
    exact ⟨by omega, trivial, trivial⟩

end sub_loop

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::sub` (loop)**

Returns the normalized radix difference with borrow conservation. -/
@[step]
theorem sub_loop_spec (iter : core.ops.range.Range Usize) (a b difference : Scalar29)
    (mask borrow : U32) (h_a : ∀ j < 9, a[j]!.val < limbRadix)
    (h_b : ∀ j < 9, b[j]!.val < limbRadix) (h_mask : mask.val = limbRadix - 1)
    (h_inv : Sub.Invariant a b iter difference borrow) :
    sub_loop iter a b difference mask borrow ⦃ (result : Scalar29) (borrow' : U32) =>
      (∀ j < 9, result[j]!.val < limbRadix) ∧
      asNat result + asNat b = asNat a + montgomeryRadix * (borrow'.val / 2 ^ 31) ⦄ := by
  unfold sub_loop
  refine loop.spec_decr_nat
    (fun state : core.ops.range.Range Usize × Scalar29 × U32 => 9 - state.1.start.val)
    (fun (iter, difference, borrow) => Sub.Invariant a b iter difference borrow)
    _ _ _ ?_ h_inv
  rintro ⟨iter, difference, borrow⟩ h_state
  apply spec_mono (sub_loop.body_spec a b mask iter difference borrow h_a h_b h_mask h_state)
  intro flow h_flow
  rcases h_state with ⟨_h_end, h_start, h_difference, _h_suffix, h_value⟩
  cases flow with
  | done result =>
    rcases result with ⟨difference', borrow'⟩
    rcases h_flow with ⟨h_done, rfl, rfl⟩
    refine ⟨h_difference, ?_⟩
    rw [h_done] at h_value
    change asNat difference' + asNat b =
      asNat a + 2 ^ (29 * 9) * (borrow'.val / 2 ^ 31) at h_value
    simpa only [montgomeryRadix, show 29 * 9 = 261 from rfl] using h_value
  | cont state => grind only [Sub.Invariant]

/-- **Spec theorem for `curve25519_dalek::backend::serial::u32::scalar::Scalar29::sub`**

Returns the normalized canonical difference after at most one order correction. -/
@[step]
theorem sub_spec (a b : Scalar29) (h_a : ∀ j < 9, a[j]!.val < limbRadix)
    (h_b : ∀ j < 9, b[j]!.val < limbRadix)
    (h_lower : asNat b ≤ asNat a + order) (h_upper : asNat a < asNat b + order) :
    sub a b ⦃ (result : Scalar29) =>
      (∀ j < 9, result[j]!.val < limbRadix) ∧
      asNat result + asNat b = asNat a + (if asNat a < asNat b then order else 0) ∧
      asNat result < order ⦄ := by
  unfold sub
  step as ⟨shifted, h_shifted⟩
  step as ⟨mask, h_mask⟩
  have h_mask_value : mask.val = limbRadix - 1 := by
    rw [h_mask, h_shifted, U32.size, U32.numBits]
    rfl
  have h_initial : Sub.Invariant a b { start := 0#usize, «end» := 9#usize } ZERO 0#u32 := by
    refine ⟨rfl, by decide, ?_, fun j _ hj => ZERO_limbs j hj, by simp⟩
    grind only [ZERO_limbs, limbRadix]
  step with sub_loop_spec _ _ _ _ _ _ h_a h_b h_mask_value h_initial
    as ⟨difference, borrow, h_difference, h_value⟩
  have h_difference_bound := asNat_bounded difference h_difference
  step as ⟨flag, h_flag⟩
  simp only [Nat.shiftRight_eq_div_pow] at h_flag
  have h_flag_bound : flag.val < 2 := by scalar_tac
  step with UScalar.cast_inBounds_spec as ⟨byte, h_byte⟩
  rw [h_flag] at h_byte
  have h_byte_cases : byte = 0#u8 ∨ byte = 1#u8 := by scalar_tac
  step with subtle.Choice.Insts.CoreConvertFromU8.from_spec byte h_byte_cases
    as ⟨condition, h_condition⟩
  simp only [h_condition]
  step with conditional_add_l_spec difference byte h_difference h_byte_cases
    as ⟨carry, result, h_result, h_carry, _h_last, h_sum⟩
  have h_result_bound := asNat_bounded result h_result
  refine ⟨h_result, ?_⟩
  grind only [montgomeryRadix, limbRadix, UScalar.ofNatCore_val_eq]

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

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
    have h_x_value : x.val = a[iter.start.val]!.val := by
      simp only [h_x, Array.getElem!_Nat_eq]
    have h_y_value : y.val = b[iter.start.val]!.val := by
      simp only [h_y, Array.getElem!_Nat_eq]
    have h_x_bound : x.val < limbRadix := by
      rw [h_x_value]
      exact h_a iter.start.val hi
    have h_y_bound : y.val < limbRadix := by
      rw [h_y_value]
      exact h_b iter.start.val hi
    step as ⟨incoming, h_incoming⟩
    have h_incoming_value : incoming.val = borrow.val / 2 ^ 31 := by
      simpa only [Nat.shiftRight_eq_div_pow] using h_incoming
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
    have h_digit_bound : digit.val < limbRadix := by
      rw [h_digit_value]
      exact Nat.mod_lt _ (by decide)
    have h_normalized : ∀ j < 9, (difference.set iter.start digit)[j]!.val < limbRadix := by
      intro j hj
      by_cases heq : iter.start.val = j
      · rw [Array.getElem!_Nat_set_eq difference iter.start j digit
          ⟨heq, by simpa only [Array.length_eq, UScalar.ofNatCore_val_eq] using hj⟩]
        exact h_digit_bound
      · rw [Array.getElem!_Nat_set_ne difference iter.start j digit heq]
        exact h_difference j hj
    have h_suffix' : ∀ j, iter'.start.val ≤ j → j < 9 →
        (difference.set iter.start digit)[j]!.val = 0 := by
      intro j hj hj9
      have h_ne : iter.start.val ≠ j := by omega
      rw [Array.getElem!_Nat_set_ne difference iter.start j digit h_ne]
      exact h_suffix j (by omega) hj9
    have h_update := Array.uScalarToNatRadix_set difference 29 iter.start digit hi
    change asNat (difference.set iter.start digit) +
        2 ^ (29 * iter.start.val) * difference[iter.start.val]!.val =
      asNat difference + 2 ^ (29 * iter.start.val) * digit.val at h_update
    rw [h_suffix iter.start.val (Nat.le_refl _) hi, Nat.mul_zero, Nat.add_zero] at h_update
    rw [← h_digit_value, h_y_value, h_x_value, h_incoming_value] at h_row
    have h_scaled := congrArg (fun n : Nat => 2 ^ (29 * iter.start.val) * n) h_row
    simp only [Nat.mul_add] at h_scaled
    simp only [h_back]
    change Sub.Invariant a b iter' (difference.set iter.start digit) borrow' ∧
      iter'.start.val = iter.start.val + 1
    refine ⟨⟨h_end'.trans h_end, by omega, h_normalized, h_suffix', ?_⟩, h_advance⟩
    rw [h_advance]
    simp only [Finset.sum_range_succ]
    have h_power : 2 ^ (29 * (iter.start.val + 1)) =
        2 ^ (29 * iter.start.val) * limbRadix := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.pow_add, limbRadix]
    rw [h_update, h_power]
    simp only [Nat.mul_assoc]
    omega
  · simp only [hi, ↓reduceIte] at h_next
    rcases h_next with ⟨h_next, _h_same⟩
    simp only [h_next, spec_ok]
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
    rcases h_flow with ⟨h_done, h_difference_eq, h_borrow_eq⟩
    subst difference' borrow'
    refine ⟨h_difference, ?_⟩
    rw [h_done] at h_value
    change asNat difference + asNat b =
      asNat a + 2 ^ (29 * 9) * (borrow.val / 2 ^ 31) at h_value
    simpa only [montgomeryRadix, show 29 * 9 = 261 from rfl] using h_value
  | cont state =>
    rcases state with ⟨iter', difference', borrow'⟩
    rcases h_flow with ⟨h_state', h_advance⟩
    have ⟨_, h_next_start, _, _, _⟩ := h_state'
    exact ⟨h_state', by dsimp only; omega⟩

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
    refine ⟨rfl, by decide, ?_, ?_, ?_⟩
    · intro j hj
      rw [ZERO_limbs j hj]
      decide
    · intro j _hj hj9
      exact ZERO_limbs j hj9
    · simp only [ZERO_spec, UScalar.ofNatCore_val_eq, Nat.zero_div, Nat.mul_zero,
        Finset.range_zero, Finset.sum_empty, Nat.add_zero]
  step with sub_loop_spec _ _ _ _ _ _ h_a h_b h_mask_value h_initial
    as ⟨difference, borrow, h_difference, h_value⟩
  have h_difference_bound := asNat_bounded difference h_difference
  step as ⟨flag, h_flag⟩
  have h_flag_value : flag.val = borrow.val / 2 ^ 31 := by
    simpa only [Nat.shiftRight_eq_div_pow] using h_flag
  have h_flag_bound : flag.val < 2 := by scalar_tac
  step with UScalar.cast_inBounds_spec as ⟨byte, h_byte⟩ by scalar_tac
  have h_byte_cases : byte = 0#u8 ∨ byte = 1#u8 := by scalar_tac
  step with subtle.Choice.Insts.CoreConvertFromU8.from_spec byte h_byte_cases
    as ⟨condition, h_condition⟩
  have h_condition_cases : condition = 0#u8 ∨ condition = 1#u8 := by
    simpa only [h_condition] using h_byte_cases
  have h_condition_value : condition.val = borrow.val / 2 ^ 31 := by
    rw [h_condition, h_byte, h_flag_value]
  step with conditional_add_l_spec difference condition h_difference h_condition_cases
    as ⟨carry, result, h_result, h_carry, _h_last, h_sum⟩
  have h_result_bound := asNat_bounded result h_result
  have h_carry_cases : carry.val / limbRadix = 0 ∨ carry.val / limbRadix = 1 := by
    simp only [limbRadix] at h_carry ⊢
    omega
  refine ⟨h_result, ?_⟩
  rcases h_condition_cases with h_zero | h_one
  · have h_borrow_zero : borrow.val / 2 ^ 31 = 0 := by
      simpa only [h_zero, UScalar.ofNatCore_val_eq] using h_condition_value.symm
    simp only [h_borrow_zero, Nat.mul_zero, Nat.add_zero] at h_value
    have h_nonnegative : ¬ asNat a < asNat b := by omega
    simp only [h_nonnegative, ↓reduceIte, Nat.add_zero]
    simp only [h_zero, show (0#u8) ≠ 1#u8 by decide, ↓reduceIte, Nat.add_zero] at h_sum
    rcases h_carry_cases with hc | hc
    · simp only [hc, Nat.mul_zero, Nat.add_zero] at h_sum
      omega
    · simp only [hc, Nat.mul_one] at h_sum
      omega
  · have h_borrow_one : borrow.val / 2 ^ 31 = 1 := by
      simpa only [h_one, UScalar.ofNatCore_val_eq] using h_condition_value.symm
    simp only [h_borrow_one, Nat.mul_one] at h_value
    have h_negative : asNat a < asNat b := by omega
    simp only [h_negative, ↓reduceIte]
    simp only [h_one, ↓reduceIte] at h_sum
    rcases h_carry_cases with hc | hc
    · simp only [hc, Nat.mul_zero, Nat.add_zero] at h_sum
      omega
    · simp only [hc, Nat.mul_one] at h_sum
      omega

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

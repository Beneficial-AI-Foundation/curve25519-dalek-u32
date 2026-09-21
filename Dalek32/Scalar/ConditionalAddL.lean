/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Auxiliary
import Dalek32.Constants.L
import Dalek32.Lint.Basic
import Dalek32.Scalar.Index
import Dalek32.Scalar.IndexMut
import Dalek32.Subtle.ConditionalSelectU32

/-!
# `conditional_add_l`

Conditional addition with the final accumulator.
Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 204-214.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

namespace ConditionalAddL

/-- Normalization and carry conservation after the processed prefix. -/
def Invariant (initial : Scalar29) (condition : subtle.Choice)
    (iter : core.ops.range.Range Usize) (self : Scalar29) (carry : U32) : Prop :=
  iter.end = 9#usize ∧
  iter.start.val ≤ 9 ∧
  (∀ j < 9, self[j]!.val < limbRadix) ∧
  carry.val < 2 * limbRadix ∧
  (iter.start.val = 9 → self[8]!.val = carry.val % limbRadix) ∧
  asNat self + 2 ^ (29 * iter.start.val) * (carry.val / limbRadix) =
    asNat initial + ∑ j ∈ Finset.range iter.start.val,
      2 ^ (29 * j) * (if condition = 1#u8 then constants.L[j]!.val else 0)

end ConditionalAddL

namespace conditional_add_l_loop

export ConditionalAddL (Invariant)

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::conditional_add_l` (loop body)**

Preserves the carry invariant and advances the iterator. -/
@[step]
theorem body_spec (condition : subtle.Choice) (mask : U32)
    (iter : core.ops.range.Range Usize) (self : Scalar29) (carry : U32)
    (initial : Scalar29) (h_condition : condition = 0#u8 ∨ condition = 1#u8)
    (h_mask : mask.val = limbRadix - 1) (h_inv : Invariant initial condition iter self carry) :
    body condition mask iter self carry ⦃
      (result : ControlFlow (core.ops.range.Range Usize × Scalar29 × U32) (U32 × Scalar29)) =>
      match result with
      | .done (carry', self') => iter.start.val = 9 ∧ carry' = carry ∧ self' = self
      | .cont (iter', self', carry') =>
        Invariant initial condition iter' self' carry' ∧
        iter'.start.val = iter.start.val + 1 ⦄ := by
  rcases h_inv with ⟨h_end, h_start, h_self, h_carry, _h_last, h_value⟩
  unfold body
  step -threadGrindState -grind as ⟨next, iter', h_next, h_end'⟩
  simp only [h_end, UScalar.ofNatCore_val_eq] at h_next
  by_cases hi : iter.start.val < 9
  · simp only [hi, ↓reduceIte] at h_next
    rcases h_next with ⟨h_next, h_advance⟩
    simp only [h_next]
    step with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨l, h_l⟩
    step with U32.Insts.SubtleConditionallySelectable.conditional_select_spec
      as ⟨addend, h_addend⟩
    have h_addend_value : addend.val =
        if condition = 1#u8 then constants.L[iter.start.val]!.val else 0 := by
      by_cases hc : condition = 1#u8 <;>
        simp only [h_addend, hc, ↓reduceIte, h_l, Array.getElem!_Nat_eq,
          UScalar.ofNatCore_val_eq]
    have h_addend_bound : addend.val < limbRadix := by
      rw [h_addend_value]
      split
      · exact constants.L_limbs_lt iter.start.val hi
      · decide
    step as ⟨shifted, h_shifted⟩
    have h_shifted_value : shifted.val = carry.val / limbRadix := by
      simpa only [Nat.shiftRight_eq_div_pow, limbRadix] using h_shifted
    have h_shifted_bound : shifted.val < 2 := by
      simp only [limbRadix] at h_carry h_shifted_value
      omega
    step with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨limb, h_limb⟩
    have h_limb_value : limb.val = self[iter.start.val]!.val := by
      simp only [h_limb, Array.getElem!_Nat_eq]
    have h_limb_bound : limb.val < limbRadix := by
      rw [h_limb_value]
      exact h_self iter.start.val hi
    step with U32.add_spec as ⟨sum, h_sum⟩ by
      simp only [limbRadix] at h_limb_bound
      scalar_tac
    step with U32.add_spec as ⟨carry', h_carry'⟩ by
      simp only [limbRadix] at h_limb_bound h_addend_bound
      scalar_tac
    have h_carry_bound : carry'.val < 2 * limbRadix := by
      simp only [limbRadix] at h_limb_bound h_addend_bound ⊢
      omega
    have h_carry_value : carry'.val = carry.val / limbRadix +
        self[iter.start.val]!.val +
        (if condition = 1#u8 then constants.L[iter.start.val]!.val else 0) := by
      rw [h_carry', h_sum, h_shifted_value, h_limb_value, h_addend_value]
    step with Insts.CoreOpsIndexIndexMutUsizeU32.index_mut_spec
      as ⟨_limb, back, _h_limb, h_back⟩
    step as ⟨digit, h_digit⟩
    have h_digit_value : digit.val = carry'.val % limbRadix := by
      simp only [h_digit, UScalar.val_and, h_mask, limbRadix,
        Nat.and_two_pow_sub_one_eq_mod]
    have h_digit_bound : digit.val < limbRadix := by
      rw [h_digit_value]
      exact Nat.mod_lt _ (by decide)
    have h_self' : ∀ j < 9, (self.set iter.start digit)[j]!.val < limbRadix := by
      intro j hj
      by_cases heq : iter.start.val = j
      · rw [Array.getElem!_Nat_set_eq self iter.start j digit
          ⟨heq, by simpa only [Array.length_eq, UScalar.ofNatCore_val_eq] using hj⟩]
        exact h_digit_bound
      · rw [Array.getElem!_Nat_set_ne self iter.start j digit heq]
        exact h_self j hj
    have h_update := Array.uScalarToNatRadix_set self 29 iter.start digit hi
    change asNat (self.set iter.start digit) +
        2 ^ (29 * iter.start.val) * self[iter.start.val]!.val =
      asNat self + 2 ^ (29 * iter.start.val) * digit.val at h_update
    have h_split := Nat.mod_add_div carry'.val limbRadix
    rw [← h_digit_value] at h_split
    have h_scaled_split := congrArg (fun n : Nat => 2 ^ (29 * iter.start.val) * n) h_split
    have h_scaled_carry :=
      congrArg (fun n : Nat => 2 ^ (29 * iter.start.val) * n) h_carry_value
    simp only [Nat.mul_add] at h_scaled_split h_scaled_carry
    simp only [h_back]
    change Invariant initial condition iter' (self.set iter.start digit) carry' ∧
      iter'.start.val = iter.start.val + 1
    refine ⟨⟨h_end'.trans h_end, by omega, h_self', h_carry_bound, ?_, ?_⟩, h_advance⟩
    · intro h_final
      have hi8 : iter.start.val = 8 := by omega
      rw [Array.getElem!_Nat_set_eq self iter.start 8 digit
        ⟨hi8, by simpa only [Array.length_eq, UScalar.ofNatCore_val_eq] using (by decide : 8 < 9)⟩]
      exact h_digit_value
    · rw [h_advance, Finset.sum_range_succ]
      have h_power : 2 ^ (29 * (iter.start.val + 1)) =
          2 ^ (29 * iter.start.val) * limbRadix := by
        simp only [Nat.mul_add, Nat.mul_one, Nat.pow_add, limbRadix]
      rw [h_power]
      simp only [Nat.mul_assoc]
      omega
  · simp only [hi, ↓reduceIte] at h_next
    rcases h_next with ⟨h_next, _h_same⟩
    simp only [h_next, spec_ok]
    exact ⟨by omega, trivial, trivial⟩

end conditional_add_l_loop

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::conditional_add_l` (loop)**

Completes conditional addition from a valid loop state. -/
@[step]
theorem conditional_add_l_loop_spec (iter : core.ops.range.Range Usize)
    (self : Scalar29) (condition : subtle.Choice) (carry : U32) (mask : U32)
    (initial : Scalar29) (h_condition : condition = 0#u8 ∨ condition = 1#u8)
    (h_mask : mask.val = limbRadix - 1)
    (h_inv : conditional_add_l_loop.Invariant initial condition iter self carry) :
    conditional_add_l_loop iter self condition carry mask ⦃ (carry' : U32) (result : Scalar29) =>
      (∀ j < 9, result[j]!.val < limbRadix) ∧
      carry'.val < 2 * limbRadix ∧
      result[8]!.val = carry'.val % limbRadix ∧
      asNat result + montgomeryRadix * (carry'.val / limbRadix) =
        asNat initial + (if condition = 1#u8 then order else 0) ⦄ := by
  have h_total : (∑ j ∈ Finset.range 9,
      2 ^ (29 * j) * (if condition = 1#u8 then constants.L[j]!.val else 0)) =
      if condition = 1#u8 then order else 0 := by
    by_cases hc : condition = 1#u8
    · simp only [hc, ↓reduceIte]
      exact constants.L_spec
    · simp only [hc, ↓reduceIte, Nat.mul_zero, Finset.sum_const_zero]
  unfold conditional_add_l_loop
  refine loop.spec_decr_nat
    (fun state : core.ops.range.Range Usize × Scalar29 × U32 => 9 - state.1.start.val)
    (fun (iter, self, carry) => conditional_add_l_loop.Invariant initial condition iter self carry)
    _ _ _ ?_ h_inv
  rintro ⟨iter, self, carry⟩ h_state
  apply spec_mono (conditional_add_l_loop.body_spec condition mask iter self carry initial
    h_condition h_mask h_state)
  intro flow h_flow
  rcases h_state with ⟨_h_end, h_start, h_self, h_carry, h_last, h_value⟩
  cases flow with
  | done result =>
    rcases result with ⟨carry', result⟩
    rcases h_flow with ⟨h_done, h_carry_eq, h_self_eq⟩
    subst carry' result
    change (∀ j < 9, self[j]!.val < limbRadix) ∧
      carry.val < 2 * limbRadix ∧ self[8]!.val = carry.val % limbRadix ∧ _
    refine ⟨h_self, h_carry, h_last h_done, ?_⟩
    rw [h_done, h_total] at h_value
    simpa only [montgomeryRadix, show 29 * 9 = 261 from rfl] using h_value
  | cont state =>
    rcases state with ⟨iter', self', carry'⟩
    rcases h_flow with ⟨h_state', h_advance⟩
    have ⟨_, h_next_start, _, _, _, _⟩ := h_state'
    exact ⟨h_state', by dsimp only; omega⟩

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::conditional_add_l`**

Returns the normalized conditional sum and final accumulator. -/
@[step]
theorem conditional_add_l_spec (self : Scalar29) (condition : subtle.Choice)
    (h_self : ∀ j < 9, self[j]!.val < limbRadix)
    (h_condition : condition = 0#u8 ∨ condition = 1#u8) :
    conditional_add_l self condition ⦃ (carry : U32) (result : Scalar29) =>
      (∀ j < 9, result[j]!.val < limbRadix) ∧
      carry.val < 2 * limbRadix ∧
      result[8]!.val = carry.val % limbRadix ∧
      asNat result + montgomeryRadix * (carry.val / limbRadix) =
        asNat self + (if condition = 1#u8 then order else 0) ⦄ := by
  unfold conditional_add_l
  step as ⟨shifted, h_shifted⟩
  step as ⟨mask, h_mask⟩
  have h_mask_value : mask.val = limbRadix - 1 := by
    rw [h_mask, h_shifted, U32.size, U32.numBits]
    rfl
  apply conditional_add_l_loop_spec _ _ _ _ _ self h_condition h_mask_value
  refine ⟨rfl, by decide, h_self, by decide, ?_, ?_⟩
  · intro h_impossible
    change 0 = 9 at h_impossible
    omega
  · simp only [UScalar.ofNatCore_val_eq, Nat.zero_div, Nat.mul_zero, Nat.add_zero,
      Finset.range_zero, Finset.sum_empty]

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dana Mukusheva
-/
import Dalek32.Auxiliary
import Dalek32.Constants.L
import Dalek32.Lint.Basic
import Dalek32.Scalar.Sub
import Dalek32.Scalar.Zero

/-!
# `add`

Addition with a single conditional subtraction of the scalar order.
Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 172-185.

## Correspondence with the `u64` backend spec

`add_spec` mirrors `Scalar52.add_spec` in curve25519-dalek-lean-verify
("Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Add.lean"):

| `u32` (this file)          | `u64` (`Scalar52`)                       |
|----------------------------|------------------------------------------|
| `order`                    | `L`                                      |
| `asNat`                    | `Scalar52_as_Nat`                        |
| `IsNormalized` (9 limbs, each `< 2^29`) | `∀ i < 5, limb i < 2^52`    |
| `asNat a < order`          | `Scalar52_as_Nat a < L`                  |
| `asNat b < order`          | `Scalar52_as_Nat b ≤ L` (weaker there)   |
| `x % order = y % order`    | `x ≡ y [MOD L]`                          |

The postconditions say the same thing: the result is normalized, congruent to `a + b`
modulo the order, and canonical (`< order`).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

namespace Add

/-- Normalized sum prefix, bounded carry, and carry conservation. -/
def Invariant (a b : Scalar29) (iter : core.ops.range.Range Usize)
    (sum : Scalar29) (carry : U32) : Prop :=
  iter.end = 9#usize ∧
  iter.start.val ≤ 9 ∧
  IsNormalized sum ∧
  (∀ j, iter.start.val ≤ j → j < 9 → sum[j]!.val = 0) ∧
  carry.val < 2 ^ 30 ∧
  asNat sum + 2 ^ (29 * iter.start.val) * (carry.val / 2 ^ 29) =
    ∑ j ∈ Finset.range iter.start.val, 2 ^ (29 * j) * (a[j]!.val + b[j]!.val)

end Add

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::add` (loop body)**

Preserves the sum invariant on continuation and completion. -/
@[step]
theorem add_loop.body_spec (a b : Scalar29) (iter : core.ops.range.Range Usize)
    (sum : Scalar29) (carry : U32)
    (h_a : IsNormalized a) (h_b : IsNormalized b)
    (h_inv : Add.Invariant a b iter sum carry) :
    add_loop.body a b 0x1fffffff#u32 iter sum carry ⦃
      (result : ControlFlow (core.ops.range.Range Usize × Scalar29 × U32) Scalar29) =>
      match result with
      | .done sum' =>
        iter.start.val = 9 ∧ sum' = sum ∧ Add.Invariant a b iter sum' carry
      | .cont (iter', sum', carry') =>
        Add.Invariant a b iter' sum' carry' ∧
        iter'.start.val = iter.start.val + 1 ⦄ := by
  rcases h_inv with ⟨h_end, h_start, h_sum, h_suffix, h_carry, h_value⟩
  unfold add_loop.body
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
    step with U32.add_spec as ⟨pair, h_pair⟩ by
      simp only [limbRadix] at h_x_bound h_y_bound
      scalar_tac
    step as ⟨incoming, h_incoming⟩
    simp only [Nat.shiftRight_eq_div_pow] at h_incoming
    have h_incoming_bound : incoming.val < 2 := by scalar_tac
    step with U32.add_spec as ⟨carry', h_carry'⟩ by
      simp only [limbRadix] at h_x_bound h_y_bound
      scalar_tac
    have h_carry'_bound : carry'.val < 2 ^ 30 := by
      simp only [limbRadix] at h_x_bound h_y_bound
      omega
    step with Insts.CoreOpsIndexIndexMutUsizeU32.index_mut_spec
      as ⟨_limb, back, _h_limb, h_back⟩
    step as ⟨digit, h_digit⟩
    have h_digit_value : digit.val = carry'.val % limbRadix := by
      rw [h_digit, UScalar.val_and]
      change carry'.val &&& (2 ^ 29 - 1) = carry'.val % 2 ^ 29
      simp only [Nat.and_two_pow_sub_one_eq_mod]
    have h_digit_bound : digit.val < limbRadix := by grind only [limbRadix]
    have h_row : digit.val + limbRadix * (carry'.val / 2 ^ 29) =
        x.val + y.val + carry.val / 2 ^ 29 := by
      simp only [limbRadix] at h_digit_value ⊢
      omega
    have h_normalized : IsNormalized (sum.set iter.start digit) := by
      clear * - h_sum h_digit_bound
      simp only [IsNormalized, Array.getElem!_Nat_eq, Array.set_val_eq] at *
      grind
    have h_suffix' : ∀ j, iter'.start.val ≤ j → j < 9 →
        (sum.set iter.start digit)[j]!.val = 0 := by
      intro j hj hj9
      simpa only [Array.getElem!_Nat_set_ne sum iter.start j digit (by omega)]
        using h_suffix j (by omega) hj9
    have h_update := Array.uScalarToNatRadix_set sum 29 iter.start digit hi
    change asNat (sum.set iter.start digit) +
        2 ^ (29 * iter.start.val) * sum[iter.start.val]!.val =
      asNat sum + 2 ^ (29 * iter.start.val) * digit.val at h_update
    rw [h_suffix iter.start.val (Nat.le_refl _) hi, Nat.mul_zero, Nat.add_zero] at h_update
    simp only [h_y, h_x, ← Array.getElem!_Nat_eq] at h_row
    simp only [h_back]
    change Add.Invariant a b iter' (sum.set iter.start digit) carry' ∧
      iter'.start.val = iter.start.val + 1
    refine ⟨⟨h_end'.trans h_end, by omega, h_normalized, h_suffix', h_carry'_bound, ?_⟩,
      h_advance⟩
    rw [h_advance, h_update, Finset.sum_range_succ, ← h_value]
    unfold limbRadix at h_row
    calc asNat sum + 2 ^ (29 * iter.start.val) * digit.val +
          2 ^ (29 * (iter.start.val + 1)) * (carry'.val / 2 ^ 29)
        _ = asNat sum + 2 ^ (29 * iter.start.val) *
            (digit.val + 2 ^ 29 * (carry'.val / 2 ^ 29)) := by ring
        _ = asNat sum + 2 ^ (29 * iter.start.val) * (carry.val / 2 ^ 29) +
            2 ^ (29 * iter.start.val) * (a[iter.start.val]!.val + b[iter.start.val]!.val) := by
          rw [h_row]
          ring
  · simp only [hi, ↓reduceIte] at h_next
    simp only [h_next.1, spec_ok]
    exact ⟨by omega, trivial, h_end, h_start, h_sum, h_suffix, h_carry, h_value⟩

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::add` (loop)**

Returns the normalized radix sum, truncated to nine limbs. -/
@[step]
theorem add_loop_spec (iter : core.ops.range.Range Usize) (a b sum : Scalar29)
    (carry : U32) (h_a : IsNormalized a) (h_b : IsNormalized b)
    (h_inv : Add.Invariant a b iter sum carry) :
    add_loop iter a b sum 0x1fffffff#u32 carry ⦃ (result : Scalar29) =>
      IsNormalized result ∧
      asNat result = (asNat a + asNat b) % montgomeryRadix ⦄ := by
  unfold add_loop
  refine loop.spec_decr_nat
    (fun state : core.ops.range.Range Usize × Scalar29 × U32 => 9 - state.1.start.val)
    (fun (iter, sum, carry) => Add.Invariant a b iter sum carry)
    _ _ _ ?_ h_inv
  rintro ⟨iter, sum, carry⟩ h_state
  apply spec_mono (add_loop.body_spec a b iter sum carry h_a h_b h_state)
  intro flow h_flow
  cases flow with
  | done result =>
    rcases h_flow with ⟨h_done, _h_sum_eq, h_final⟩
    rcases h_final with ⟨_h_end, _h_start, h_result, _h_suffix, _h_carry, h_value⟩
    refine ⟨h_result, ?_⟩
    rw [h_done] at h_value
    have h_ab : (∑ j ∈ Finset.range 9, 2 ^ (29 * j) * (a[j]!.val + b[j]!.val)) =
        asNat a + asNat b := by
      simp only [mul_add, Finset.sum_add_distrib]
      rfl
    have h_bound := asNat_bounded result h_result
    rw [← h_ab, ← h_value]
    unfold montgomeryRadix at h_bound ⊢
    rw [show 29 * 9 = 261 from rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_bound]
  | cont state => grind only [Add.Invariant]

/-- **Spec theorem for `curve25519_dalek::backend::serial::u32::scalar::Scalar29::add`**

Returns the normalized canonical sum after at most one order correction. -/
@[step]
theorem add_spec (a b : Scalar29) (h_a : IsNormalized a) (h_b : IsNormalized b)
    (h_a_lt : asNat a < order) (h_b_lt : asNat b < order) :
    add a b ⦃ (result : Scalar29) =>
      IsNormalized result ∧
      asNat result % order = (asNat a + asNat b) % order ∧
      asNat result < order ⦄ := by
  unfold add
  step as ⟨shifted, h_shifted⟩
  step as ⟨mask, h_mask⟩
  have h_mask_eq : mask = 0x1fffffff#u32 := by
    apply UScalar.eq_of_val_eq
    rw [h_mask, h_shifted, U32.size, U32.numBits]
    rfl
  simp only [h_mask_eq]
  have h_initial : Add.Invariant a b { start := 0#usize, «end» := 9#usize } ZERO 0#u32 := by
    refine ⟨rfl, by decide, ?_, fun j _ hj => ZERO_limbs j hj, by simp, by simp⟩
    grind only [ZERO_limbs, IsNormalized, limbRadix]
  step with add_loop_spec _ _ _ _ _ h_a h_b h_initial as ⟨sum, h_sum, h_sum_value⟩
  have h_sum_eq : asNat sum = asNat a + asNat b := by
    rw [h_sum_value]
    apply Nat.mod_eq_of_lt
    have := order_lt_two_pow_253
    unfold montgomeryRadix
    omega
  step with sub_spec sum constants.L h_sum constants.L_limbs_lt
    (by rw [constants.L_spec]; omega) (by rw [constants.L_spec]; omega)
    as ⟨result, h_result, h_mod, h_lt⟩
  refine ⟨h_result, ?_, h_lt⟩
  rw [constants.L_spec, h_sum_eq] at h_mod
  rw [← h_mod]
  simp only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

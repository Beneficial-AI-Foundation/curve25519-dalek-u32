/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.Field.Square

/-!
# Spec theorem for `pow2k`

`pow2k self k` computes `self ^ (2 ^ k)` for `k > 0` by repeated squaring: it squares `self` once
and then squares the result `k - 1` more times in a loop over the range `1..k`. Every squaring
returns a reduced field element, so every iteration meets the precondition of `square`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 320:4-327:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace Pow2k

/-- Loop invariant of `pow2k`, relative to the original input `x` and exponent `k`: the range ends
at `k`, its start `s` satisfies `1 ≤ s ≤ k`, the accumulator `z` is reduced (every limb below
`2 ^ 26`) and represents `x ^ (2 ^ s)` modulo `p`. -/
private def Invariant (x : FieldElement2625) (k : U32) (iter : core.ops.range.Range U32)
    (z : FieldElement2625) : Prop :=
  iter.end = k ∧
  1 ≤ iter.start.val ∧
  iter.start.val ≤ k.val ∧
  (∀ i < 10, z[i]!.val < 2 ^ 26) ∧
  z.toNat % p = x.toNat ^ (2 ^ iter.start.val) % p

end Pow2k


/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::pow2k` (loop body)
Preserves `Pow2k.Invariant` and advances the range start by one on continuation; on completion the
range is exhausted (`start = k`) and the accumulator is returned unchanged.
A first `step` applies `IteratorRange.next_U32_spec`, whose postcondition is an `if` on
`start < end`, and `by_cases` on that condition resolves it. If `start < end = k`, the range
yields `some start` with `start' = start + 1 ≤ k` and `end' = k`, and `step with square_spec`
applies to `z` since `z[i] < 2 ^ 26 < 2 ^ 27 + 2 ^ 25`. It returns a reduced `z'` with
`z' ≡ z ^ 2 ≡ (x ^ (2 ^ start)) ^ 2 = x ^ (2 ^ (start + 1))` modulo `p`, by rewriting with
`Nat.pow_mod`, `← pow_mul` and `pow_succ`. Otherwise the range yields `none`, the body returns
`z`, and `k ≤ start ≤ k` gives `start = k`. -/
@[step]
private theorem pow2k_loop.body_spec (iter : core.ops.range.Range U32) (z : FieldElement2625)
    (x : FieldElement2625) (k : U32)
    (h_inv : Pow2k.Invariant x k iter z) :
    pow2k_loop.body iter z ⦃
      (result : ControlFlow (core.ops.range.Range U32 × FieldElement2625) FieldElement2625) =>
      match result with
      | .done z' =>
        iter.start.val = k.val ∧ z' = z ∧ Pow2k.Invariant x k iter z'
      | .cont (iter', z') =>
        Pow2k.Invariant x k iter' z' ∧ iter'.start.val = iter.start.val + 1 ⦄ := by
  rcases h_inv with ⟨h_end, h_start, h_le, h_red, h_val⟩
  unfold pow2k_loop.body
  step as ⟨o, iter', h_next, h_end'⟩
  by_cases hi : iter.start.val < iter.end.val
  · simp only [hi, ↓reduceIte] at h_next
    rcases h_next with ⟨h_o, h_adv⟩
    simp only [h_o]
    step with square_spec as ⟨z', h_red', h_val'⟩
    refine ⟨⟨h_end'.trans h_end, by omega, ?_, h_red', ?_⟩, h_adv⟩
    · rw [h_end] at hi
      omega
    · rw [h_val', Nat.pow_mod, h_val, ← Nat.pow_mod, ← pow_mul, h_adv, pow_succ]
  · simp only [hi, ↓reduceIte] at h_next
    rcases h_next with ⟨h_o, _⟩
    simp only [h_o, spec_ok]
    rw [h_end] at hi
    exact ⟨by omega, trivial, h_end, h_start, h_le, h_red, h_val⟩


/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::pow2k` (loop)
From a state satisfying `Pow2k.Invariant`, the loop returns a reduced element representing
`x ^ (2 ^ k)` modulo `p`.
The proof applies `loop.spec_decr_nat` with measure `k - iter.start` and invariant
`Pow2k.Invariant x k`, and reduces each iteration to `pow2k_loop.body_spec` via `spec_mono`. On
continuation `omega` shows that the measure drops, from `start' = start + 1` and the invariant's
`start' ≤ k`. On completion `start = k`, which rewrites the invariant's congruence into the
postcondition. -/
@[step]
private theorem pow2k_loop_spec (iter : core.ops.range.Range U32) (z : FieldElement2625)
    (x : FieldElement2625) (k : U32)
    (h_inv : Pow2k.Invariant x k iter z) :
    pow2k_loop iter z ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val < 2 ^ 26) ∧
      result.toNat % p = x.toNat ^ (2 ^ k.val) % p ⦄ := by
  unfold pow2k_loop
  refine loop.spec_decr_nat
    (fun state : core.ops.range.Range U32 × FieldElement2625 => k.val - state.1.start.val)
    (fun (iter, z) => Pow2k.Invariant x k iter z)
    _ _ _ ?_ h_inv
  rintro ⟨iter, z⟩ h_state
  apply spec_mono (pow2k_loop.body_spec iter z x k h_state)
  intro flow h_flow
  cases flow with
  | done result =>
    rcases h_flow with ⟨h_done, _, _, _, _, h_red, h_val⟩
    rw [h_done] at h_val
    exact ⟨h_red, h_val⟩
  | cont state =>
    rcases state with ⟨iter', z'⟩
    rcases h_flow with ⟨h_state', h_adv⟩
    have h_le := h_state'.2.2.1
    exact ⟨h_state', by dsimp only; omega⟩


/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::pow2k`
If `0 < k` and every limb of `self` is below `2 ^ 27 + 2 ^ 25`, the result is reduced (every limb
below `2 ^ 26`) and represents `self ^ (2 ^ k)` modulo `p`.
After unfolding `pow2k`, `step with massert_spec` passes `massert (k > 0)` by `h_k`, and a second
`step` applies `square_spec` to `self`, giving a reduced `z` with `z ≡ self ^ 2` modulo `p`.
`pow2k_loop_spec` then concludes once `Pow2k.Invariant self k {start := 1, end := k} z` holds:
`1 ≤ 1 ≤ k` by `h_k`, and `z ≡ self ^ (2 ^ 1)` by `simpa` with `UScalar.ofNatCore_val_eq` and
`pow_one`. -/
@[step]
theorem pow2k_spec (self : FieldElement2625) (k : U32)
    (h_k : 0 < k.val)
    (h_self : ∀ i < 10, self[i]!.val < 2 ^ 27 + 2 ^ 25) :
    pow2k self k ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val < 2 ^ 26) ∧
      result.toNat % p = self.toNat ^ (2 ^ k.val) % p ⦄ := by
  unfold pow2k
  step with massert_spec
  step as ⟨z, h_red, h_val⟩
  apply pow2k_loop_spec _ _ self k
  refine ⟨rfl, Nat.le_refl 1, h_k, h_red, ?_⟩
  simpa only [UScalar.ofNatCore_val_eq, pow_one] using h_val


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

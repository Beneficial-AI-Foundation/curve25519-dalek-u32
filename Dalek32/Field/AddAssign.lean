/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary

/-!
# Spec theorem for `add_assign`

`self += rhs` adds the ten `u32` limbs of `rhs` to those of `self`, limb by limb, in a `for` loop
over `0..10`, without any carrying or reduction. If every limb sum fits in a `u32`, no addition
overflows, every limb of the result is the exact sum of the corresponding limbs, and so the
represented value is the exact sum of the represented values.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 70:4-74:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625
namespace Insts.CoreOpsArithAddAssignSharedBFieldElement2625

namespace AddAssign

/-- Loop invariant of `add_assign`: the range ends at `10` and has not overshot it, every limb sum
of the original operands fits in a `u32`, the limbs before `iter.start` hold the limb sums and the
limbs from `iter.start` on still hold the original limbs of `initial`. -/
private def Invariant (initial rhs : FieldElement2625) (iter : core.ops.range.Range Usize)
    (self : FieldElement2625) : Prop :=
  iter.end = 10#usize ∧
  iter.start.val ≤ 10 ∧
  (∀ i < 10, initial[i]!.val + rhs[i]!.val ≤ U32.max) ∧
  (∀ i < iter.start.val, self[i]!.val = initial[i]!.val + rhs[i]!.val) ∧
  (∀ i < 10, iter.start.val ≤ i → self[i]! = initial[i]!)

end AddAssign

/-- **Spec theorem for**
`<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
core::ops::AddAssign<&FieldElement2625>>::add_assign` (loop body)

Starting from a state satisfying the invariant, one iteration either stops with `iter.start = 10`
and the state unchanged, or adds limb `iter.start` and continues with `iter.start + 1`, preserving
the invariant and leaving `rhs` unchanged. The proof steps through `next` on the range and splits
on `iter.start < 10`. If it fails, `next` returns `none`, the body returns `done self`, and
`iter.start = 10` follows from `iter.start ≤ 10` by `omega`. Otherwise the two limb reads are
stepped, the invariant gives `self[i] = initial[i]` at `i = iter.start`, and
`step with U32.add_spec` adds the limbs, the overflow precondition following from the sum bound.
After stepping the update, the new invariant is checked with `Array.getElem!_Nat_set_eq` at limb
`i` and `Array.getElem!_Nat_set_ne` at the other limbs, which keep their earlier sums or original
values. -/
@[step]
private theorem add_assign_loop.body_spec (iter : core.ops.range.Range Usize)
    (self rhs initial : FieldElement2625)
    (h_inv : AddAssign.Invariant initial rhs iter self) :
    add_assign_loop.body iter self rhs ⦃
      (result : ControlFlow (core.ops.range.Range Usize × FieldElement2625 × FieldElement2625)
        FieldElement2625) =>
      match result with
      | .done self' =>
        iter.start.val = 10 ∧ self' = self ∧ AddAssign.Invariant initial rhs iter self'
      | .cont (iter', self', rhs') =>
        rhs' = rhs ∧ AddAssign.Invariant initial rhs iter' self' ∧
        iter'.start.val = iter.start.val + 1 ⦄ := by
  obtain ⟨h_end, h_start, h_bound, h_done, h_rest⟩ := h_inv
  unfold add_assign_loop.body
  step as ⟨next, iter', h_next, h_end'⟩
  simp only [h_end, UScalar.ofNatCore_val_eq] at h_next
  by_cases hi : iter.start.val < 10
  · simp only [hi, ↓reduceIte] at h_next
    obtain ⟨h_next, h_advance⟩ := h_next
    simp only [h_next]
    step as ⟨r_i, h_r_i⟩
    step as ⟨s_i, h_s_i⟩
    have h_rest_i := h_rest _ hi le_rfl
    rw [Array.getElem_val_eq_getElem!] at h_r_i h_s_i
    step with U32.add_spec as ⟨sum, h_sum⟩
    step as ⟨self', h_self'⟩
    refine ⟨⟨h_end'.trans h_end, by omega, h_bound, ?_, ?_⟩, h_advance⟩
    · intro j hj
      rw [h_self']
      by_cases hj' : iter.start.val = j
      · subst hj'
        rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by scalar_tac⟩, h_sum, h_s_i, h_r_i,
          h_rest_i]
      · rw [Array.getElem!_Nat_set_ne _ _ _ _ hj']
        exact h_done j (by omega)
    · intro j hj hj'
      rw [h_self', Array.getElem!_Nat_set_ne _ _ _ _ (by omega)]
      exact h_rest j hj (by omega)
  · simp only [hi, ↓reduceIte] at h_next
    obtain ⟨h_next, -⟩ := h_next
    simp only [h_next, spec_ok]
    exact ⟨by omega, trivial, h_end, h_start, h_bound, h_done, h_rest⟩

/-- **Spec theorem for**
`<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
core::ops::AddAssign<&FieldElement2625>>::add_assign` (loop)

From any state satisfying the invariant the loop terminates with every limb equal to the sum of the
corresponding limbs of `initial` and `rhs`, so the represented value is `initial.toNat + rhs.toNat`.
The proof applies `loop.spec_decr_nat` with measure `10 - iter.start` and invariant
`rhs' = rhs ∧ AddAssign.Invariant initial rhs iter self` on the loop state `(iter, self, rhs')`,
and weakens `add_assign_loop.body_spec` with `spec_mono`. On `cont` the invariant is preserved and
the measure drops by `omega`. On `done`, `iter.start = 10`, so the invariant gives the limb sums
at every `i < 10`. The value then follows by unfolding `toNat` to the weighted limb sum and
splitting it with `Finset.sum_add_distrib`, `Finset.sum_congr` and `Nat.mul_add`. -/
@[step]
private theorem add_assign_loop_spec (iter : core.ops.range.Range Usize)
    (self rhs initial : FieldElement2625)
    (h_inv : AddAssign.Invariant initial rhs iter self) :
    add_assign_loop iter self rhs ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val = initial[i]!.val + rhs[i]!.val) ∧
      result.toNat = initial.toNat + rhs.toNat ⦄ := by
  unfold add_assign_loop
  refine loop.spec_decr_nat
    (fun state : core.ops.range.Range Usize × FieldElement2625 × FieldElement2625 =>
      10 - state.1.start.val)
    (fun (iter', self', rhs') => rhs' = rhs ∧ AddAssign.Invariant initial rhs iter' self')
    _ _ _ ?_ ⟨rfl, h_inv⟩
  rintro ⟨iter', self', rhs'⟩ ⟨h_rhs, h_state⟩
  subst h_rhs
  apply spec_mono (add_assign_loop.body_spec iter' self' rhs' initial h_state)
  intro flow h_flow
  cases flow with
  | done result =>
    obtain ⟨h_done, -, -, -, -, h_sums, -⟩ := h_flow
    have h_limbs : ∀ i < 10, result[i]!.val = initial[i]!.val + rhs'[i]!.val :=
      fun i hi => h_sums i (by omega)
    refine ⟨h_limbs, ?_⟩
    simp only [toNat_eq, Array.uScalarToNatField2625]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => by
      rw [h_limbs i (Finset.mem_range.mp hi), Nat.mul_add]
  | cont state =>
    obtain ⟨iter'', self'', rhs''⟩ := state
    obtain ⟨h_rhs', h_state', h_advance⟩ := h_flow
    have h_start := h_state.2.1
    have h_next_start := h_state'.2.1
    exact ⟨⟨h_rhs', h_state'⟩, by dsimp only; omega⟩

/-- **Spec theorem for**
`<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
core::ops::AddAssign<&FieldElement2625>>::add_assign`

If every limb sum `self[i] + _rhs[i]` fits in a `u32`, the result has as limbs the exact limb sums
and represents `self.toNat + _rhs.toNat` (no reduction modulo `p` takes place). After unfolding,
`add_assign self _rhs` is the loop over `0..10`, and `add_assign_loop_spec` with `initial := self`
gives exactly the claim. Its initial invariant is supplied directly: the end is `10` by `rfl`,
`0 ≤ 10` by `simp`, the sum bound is `h_sum`, the summed prefix `i < 0` is empty (`simp at hi`),
and every limb equals itself by `rfl`. -/
@[step]
theorem add_assign_spec (self _rhs : FieldElement2625)
    (h_sum : ∀ i < 10, self[i]!.val + _rhs[i]!.val ≤ U32.max) :
    add_assign self _rhs ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val = self[i]!.val + _rhs[i]!.val) ∧
      result.toNat = self.toNat + _rhs.toNat ⦄ := by
  unfold add_assign
  apply add_assign_loop_spec _ _ _ self
  refine ⟨rfl, by simp, h_sum, fun i hi => ?_, fun _ _ _ => rfl⟩
  simp at hi

end Insts.CoreOpsArithAddAssignSharedBFieldElement2625
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.External.Axioms
import Dalek32.Field.SquareInner
import Dalek32.Field.Reduce

/-!
# Spec theorem for `square2`

`square2 self` computes `2 * self ^ 2` as a `FieldElement2625`. It runs the squaring kernel
`square_inner`, doubles each of the ten unreduced `u64` coefficients in place through a mutable
iterator (`for coeff in &mut coeffs { *coeff += *coeff; }`), and then `reduce`s the doubled
coefficients. In the extracted code the loop threads the `IterMut` together with a backward
function: every step composes a write of the doubled coefficient at the current index onto the
backward function, and when the iterator is exhausted the backward function is applied to it,
yielding an iterator whose slice holds all doubled coefficients.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 600:4-606:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace Square2

/-- Loop invariant of `square2`, relative to the original coefficients `coeffs`: the iterator still
holds the original coefficients (`iter.slice.val = coeffs.val`, as the forward iterator is never
written to), its position `iter.i` is at most `10`, and on any length-`10` iterator `im` the
accumulated backward function `back` keeps the length `10`, sets every entry `j < iter.i` to
`2 * coeffs[j]` and leaves every other entry as in `im`. -/
private def Invariant (coeffs : Array U64 10#usize) (iter : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64) : Prop :=
  iter.slice.val = coeffs.val ∧
  iter.i ≤ 10 ∧
  ∀ im : core.slice.iter.IterMut U64, im.slice.val.length = 10 →
    (back im).slice.val.length = 10 ∧
    ∀ j < 10, (back im).slice.val[j]!.val =
      if j < iter.i then 2 * coeffs[j]!.val else im.slice.val[j]!.val

end Square2


/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::square2` (loop body)
If no original coefficient reaches `2 ^ 63`, the body preserves `Square2.Invariant` and advances
the position by one on continuation; on completion it returns an iterator whose slice has length
`10` and holds the doubled original coefficients.
The proof unfolds `square2_loop.body` and `IteratorIterMut.next` and splits with `by_cases` on
`iter.i < iter.slice.len`. In the positive case the current entry is `coeffs[iter.i]` (by
`Slice.Inhabited_getElem_eq_getElem!` and `iter.slice.val = coeffs.val`), so `step` discharges
the checked `coeff + coeff` from `coeffs[iter.i] < 2 ^ 63`. The new backward function writes the
doubled entry at `iter.i` with `setAtNat` before calling `back`: `Slice.setAtNat_length` keeps
the length `10`, and a case split on `j < iter.i`, `j = iter.i` or neither, using
`Slice.getElem!_Nat_setAtNat_eq` and `Slice.getElem!_Nat_setAtNat_ne`, moves the invariant's
`if` from `j < iter.i` to `j < iter.i + 1`. In the negative case `iter.i = 10`, the body returns
`back iter`, and the invariant at `im := iter` is the postcondition, as every `j < 10` is below
`iter.i`. -/
@[step]
private theorem square2_loop.body_spec (iter : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64)
    (coeffs : Array U64 10#usize)
    (h_coeffs : ∀ i < 10, coeffs[i]!.val < 2 ^ 63)
    (h_inv : Square2.Invariant coeffs iter back) :
    square2_loop.body iter back ⦃
      (result : ControlFlow (core.slice.iter.IterMut U64 ×
        (core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64))
        (core.slice.iter.IterMut U64)) =>
      match result with
      | .done r =>
        r.slice.val.length = 10 ∧
        ∀ i < 10, r.slice.val[i]!.val = 2 * coeffs[i]!.val
      | .cont (iter', back') =>
        Square2.Invariant coeffs iter' back' ∧ iter'.i = iter.i + 1 ⦄ := by
  obtain ⟨h_slice, h_le, h_back⟩ := h_inv
  have h_len : iter.slice.val.length = 10 := by
    rw [h_slice]; simp
  unfold square2_loop.body core.slice.iter.IteratorIterMut.next
  by_cases hi : iter.i < iter.slice.len
  · simp only [hi, ↓reduceDIte]
    have hi' : iter.i < iter.slice.val.length := by scalar_tac
    have hi10 : iter.i < 10 := by omega
    have h_x : (iter.slice[iter.i]'hi').val = coeffs[iter.i]!.val := by
      rw [Slice.Inhabited_getElem_eq_getElem! _ _ hi', Slice.getElem!_Nat_eq, h_slice,
        Array.getElem!_Nat_eq]
    have h_bound := h_coeffs iter.i hi10
    step as ⟨coeff1, h_coeff1⟩
    refine ⟨h_slice, show iter.i + 1 ≤ 10 by omega, ?_⟩
    intro im him
    have h_set_len : (im.slice.setAtNat iter.i coeff1).val.length = 10 := by
      simpa only [Slice.setAtNat_length] using him
    obtain ⟨h_len', h_entries⟩ :=
      h_back { slice := im.slice.setAtNat iter.i coeff1, i := im.i } h_set_len
    refine ⟨h_len', fun j hj => ?_⟩
    rw [h_entries j hj]
    by_cases hj1 : j < iter.i
    · simp only [hj1, ↓reduceIte, show j < iter.i + 1 by omega]
    · by_cases hj2 : j = iter.i
      · subst hj2
        simp only [hj1, ↓reduceIte, Nat.lt_add_one]
        rw [Slice.getElem!_Nat_setAtNat_eq _ _ _ (by rw [Slice.length, him]; exact hi10)]
        omega
      · simp only [hj1, ↓reduceIte, show ¬ j < iter.i + 1 by omega]
        rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm hj2)]
  · simp only [hi, ↓reduceDIte, bind_tc_ok]
    have hi10 : iter.i = 10 := by scalar_tac
    obtain ⟨h_len', h_entries⟩ := h_back iter h_len
    refine ⟨h_len', fun j hj => ?_⟩
    rw [h_entries j hj, if_pos (by omega)]


/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::square2` (loop)
If no original coefficient reaches `2 ^ 63`, the loop started from a state satisfying
`Square2.Invariant` returns an iterator whose slice has length `10` and holds the doubled original
coefficients.
The proof applies `loop.spec_decr_nat` with measure `10 - iter.i` and invariant
`Square2.Invariant coeffs`, and reduces each iteration to `square2_loop.body_spec` via
`spec_mono`. The completion case is the body's postcondition as is; on continuation `omega` shows
that the measure drops, from `iter'.i = iter.i + 1` and the invariant's `iter'.i ≤ 10`. -/
@[step]
private theorem square2_loop_spec (iter : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64)
    (coeffs : Array U64 10#usize)
    (h_coeffs : ∀ i < 10, coeffs[i]!.val < 2 ^ 63)
    (h_inv : Square2.Invariant coeffs iter back) :
    square2_loop iter back ⦃ (r : core.slice.iter.IterMut U64) =>
      r.slice.val.length = 10 ∧
      ∀ i < 10, r.slice.val[i]!.val = 2 * coeffs[i]!.val ⦄ := by
  unfold square2_loop
  refine loop.spec_decr_nat
    (fun state : core.slice.iter.IterMut U64 ×
      (core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64) => 10 - state.1.i)
    (fun (iter, back) => Square2.Invariant coeffs iter back)
    _ _ _ ?_ h_inv
  rintro ⟨iter, back⟩ h_state
  apply spec_mono (square2_loop.body_spec iter back coeffs h_coeffs h_state)
  intro flow h_flow
  cases flow with
  | done r => exact h_flow
  | cont state =>
    rcases state with ⟨iter', back'⟩
    rcases h_flow with ⟨h_state', h_advance⟩
    have h_le := h_state'.2.1
    exact ⟨h_state', by dsimp only; omega⟩


/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::square2`
If every limb of `self` is below `2 ^ 27 + 2 ^ 25`, the result is reduced (every limb below
`2 ^ 26`) and represents `2 * self ^ 2` modulo `p`.
The first `step` applies `square_inner_spec`, giving `coeffs ≡ self ^ 2` modulo `p` with
`coeffs[i] < 6675 * 2 ^ 50`, which `omega` weakens to `coeffs[i] < 2 ^ 63`. The second applies
the `into_iter_spec` axiom: `iter.slice.val = coeffs.val` and `iter.i = 0`, so
`Square2.Invariant coeffs iter (fun im => im)` holds, as no index is below `0`.
`square2_loop_spec` returns `r` of length `10` with doubled entries, and the axiom's backward
clause turns them into `(into_iter_back r)[i] = 2 * coeffs[i]`. These are below
`2 * 6675 * 2 ^ 50 ≤ 2 ^ 64 - 2 ^ 39`, so `step with reduce_spec` applies and gives the limb
bound. For the value, `Finset.mul_sum`, `Finset.sum_congr` and `ring` give
`(into_iter_back r).uScalarToNatField2625 = 2 * coeffs.uScalarToNatField2625`, and rewriting with
`Nat.mul_mod` chains this with the congruence of `square_inner_spec`. -/
@[step]
theorem square2_spec (self : FieldElement2625)
    (h_self : ∀ i < 10, self[i]!.val < 2 ^ 27 + 2 ^ 25) :
    square2 self ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val < 2 ^ 26) ∧
      result.toNat % p = 2 * self.toNat ^ 2 % p ⦄ := by
  unfold square2
  step as ⟨coeffs, h_mod, h_bound⟩
  step as ⟨iter, into_iter_back, h_iter_slice, h_iter_i, h_into_back⟩
  have h_coeffs : ∀ i < 10, coeffs[i]!.val < 2 ^ 63 := fun i hi => by
    have := h_bound i hi
    omega
  have h_inv : Square2.Invariant coeffs iter (fun im => im) :=
    ⟨h_iter_slice, by omega, fun im him => ⟨him, fun j _ => by simp [h_iter_i]⟩⟩
  step with square2_loop_spec iter (fun im => im) coeffs h_coeffs h_inv as ⟨r, h_r_len, h_r⟩
  have h_doubled : ∀ i < 10, (into_iter_back r)[i]!.val = 2 * coeffs[i]!.val := by
    intro i hi
    rw [Array.getElem!_Nat_eq, h_into_back r h_r_len, h_r i hi]
  step with reduce_spec as ⟨result, h_res, h_res_mod, _⟩
  refine ⟨h_res, ?_⟩
  have h_sum : (into_iter_back r).uScalarToNatField2625 = 2 * coeffs.uScalarToNatField2625 := by
    unfold Array.uScalarToNatField2625
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [h_doubled i (Finset.mem_range.mp hi)]
    ring
  rw [h_res_mod, h_sum, Nat.mul_mod, h_mod, ← Nat.mul_mod]


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

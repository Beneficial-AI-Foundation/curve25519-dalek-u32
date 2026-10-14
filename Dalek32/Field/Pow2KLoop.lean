/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Dalek32.Field.Square

/-!
# Repeated squaring loop

Both proofs use the verified square specification.
The loop counts the remaining iterations, including the empty-range case.
-/
open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- One iteration either returns the unchanged accumulator or squares it and
advances the range by exactly one. -/
theorem pow2k_loop.body_spec
    (iter : core.ops.range.Range U32) (z : FieldElement2625)
    (h_bounds : ReducedBounds z) :
    pow2k_loop.body iter z ⦃ result =>
      match result with
      | .done result => iter.end.val ≤ iter.start.val ∧ result = z
      | .cont (iter', z') =>
        iter.start.val < iter.end.val ∧
        iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end ∧
        toNat z' % p = toNat z ^ 2 % p ∧ ReducedBounds z' ⦄ := by
  unfold pow2k_loop.body
  step -threadGrindState -grind as ⟨next, iter', h_next, h_end⟩
  by_cases hi : iter.start.val < iter.end.val
  · simp only [hi, ↓reduceIte] at h_next
    rcases h_next with ⟨h_next, h_advance⟩
    simp only [h_next]
    apply spec_bind (square_spec z (reducedBounds_squareInputBounds h_bounds))
    intro z' hz'
    simp only [spec_ok]
    exact ⟨hi, h_advance, h_end, hz'⟩
  · simp only [hi, ↓reduceIte] at h_next
    simp only [h_next.1, spec_ok]
    exact ⟨by omega, trivial⟩

/-- Squaring once and then `n` more times gives `n+1` squarings. -/
theorem square_pow_mod (a b n : Nat) (h : b % p = a ^ 2 % p) :
    b ^ (2 ^ n) % p = a ^ (2 ^ (n + 1)) % p := by
  have hp := Nat.ModEq.pow (2 ^ n) h
  change b ^ (2 ^ n) % p = (a ^ 2) ^ (2 ^ n) % p at hp
  rw [← pow_mul, ← Nat.pow_succ'] at hp
  exact hp

/-- Arbitrary range: the accumulator is squared `end - start` times. -/
theorem pow2k_loop_spec
    (iter : core.ops.range.Range U32) (z : FieldElement2625)
    (h_bounds : ReducedBounds z) :
    pow2k_loop iter z ⦃ result =>
      toNat result % p = toNat z ^ (2 ^ (iter.end.val - iter.start.val)) % p ∧
      ReducedBounds result ⦄ := by
  unfold pow2k_loop
  refine loop.spec_decr_nat
    (fun state : core.ops.range.Range U32 × FieldElement2625 =>
      state.1.end.val - state.1.start.val)
    (fun (it, acc) => ReducedBounds acc ∧
      toNat acc ^ (2 ^ (it.end.val - it.start.val)) % p =
        toNat z ^ (2 ^ (iter.end.val - iter.start.val)) % p)
    _ _ _ ?_ ⟨h_bounds, rfl⟩
  rintro ⟨it, acc⟩ ⟨hb, hv⟩
  apply spec_mono (pow2k_loop.body_spec it acc hb)
  intro flow hf
  cases flow with
  | done result =>
    rcases hf with ⟨h_done, rfl⟩
    have hd : it.end.val - it.start.val = 0 := by omega
    simp only [hd, pow_zero, pow_one] at hv
    exact ⟨hv, hb⟩
  | cont state =>
    rcases state with ⟨it', acc'⟩
    rcases hf with ⟨hi, hs, he, hv', hb'⟩
    have hd : it.end.val - it.start.val =
        (it'.end.val - it'.start.val) + 1 := by rw [he, hs]; omega
    refine ⟨⟨hb', ?_⟩, ?_⟩
    · calc
        _ = toNat acc ^ (2 ^ ((it'.end.val - it'.start.val) + 1)) % p :=
          square_pow_mod _ _ _ hv'
        _ = _ := by rw [← hd]; exact hv
    · dsimp only
      omega

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

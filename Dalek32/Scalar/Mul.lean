/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Dalek32.Auxiliary
import Dalek32.Constants.RR
import Dalek32.Lint.Basic
import Dalek32.Scalar.MontgomeryReduce
import Dalek32.Scalar.MulInternal

/-!
# Spec theorem for `curve25519_dalek::backend::serial::u32::scalar::Scalar29::mul`

Computes `a * b (mod l)`: a Montgomery reduction of the schoolbook product gives
`a * b / R`, and a second Montgomery multiplication by `RR = R^2` removes the radix.

Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 372-376.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

/-- A reduced scalar times any normalized scalar stays below `R * l`, the input range
of `montgomery_reduce`. -/
theorem mul_lt_montgomeryRadix_mul_order (a b : Scalar29)
    (h_a : asNat a < order) (h_b : IsNormalized b) :
    asNat a * asNat b < montgomeryRadix * order := by
  rw [Nat.mul_comm montgomeryRadix]
  exact Nat.mul_lt_mul'' h_a (asNat_bounded b h_b)

/-- **Spec theorem for `curve25519_dalek::backend::serial::u32::scalar::Scalar29::mul`**

Given normalized inputs whose product fits the Montgomery reduction range, the result is
the canonical representative of `a * b` modulo the scalar order. -/
@[step]
theorem mul_spec (a b : Scalar29) (h_a : IsNormalized a) (h_b : IsNormalized b)
    (h_range : asNat a * asNat b < montgomeryRadix * order) :
    mul a b ⦃ (result : Scalar29) =>
      IsNormalized result ∧
      asNat result < order ∧
      asNat result % order = (asNat a * asNat b) % order ⦄ := by
  unfold mul
  step -threadGrindState -grind -assumTac with mul_internal_spec a b h_a h_b
    as ⟨w, h_w, h_w_bounds⟩
  step -threadGrindState -grind -assumTac with montgomery_reduce_spec w
    (fun i hi => (h_w_bounds i hi).trans (by decide)) (by rw [h_w]; exact h_range)
    as ⟨ab, h_ab, h_ab_norm, h_ab_lt⟩
  step -threadGrindState -grind -assumTac with mul_internal_spec ab constants.RR h_ab_norm
    constants.RR_limbs_lt as ⟨w', h_w', h_w'_bounds⟩
  have h_range' : asNat ab * asNat constants.RR < montgomeryRadix * order := by
    rw [Nat.mul_comm montgomeryRadix]
    exact Nat.mul_lt_mul'' h_ab_lt (asNat_bounded _ constants.RR_limbs_lt)
  step -threadGrindState -grind -assumTac with montgomery_reduce_spec w'
    (fun i hi => (h_w'_bounds i hi).trans (by decide)) (by rw [h_w']; exact h_range')
    as ⟨r, h_r, h_r_norm, h_r_lt⟩
  refine ⟨h_r_norm, h_r_lt, ?_⟩
  have h_ab' : asNat ab * montgomeryRadix ≡ asNat a * asNat b [MOD order] := by
    rw [h_w] at h_ab; exact h_ab
  have h_r' : asNat r * montgomeryRadix ≡ asNat ab * asNat constants.RR [MOD order] := by
    rw [h_w'] at h_r; exact h_r
  have h_rr : asNat constants.RR ≡ montgomeryRadix ^ 2 [MOD order] := constants.RR_spec
  apply cancel_montgomeryRadix
  calc asNat r * montgomeryRadix
      ≡ asNat ab * asNat constants.RR [MOD order] := h_r'
    _ ≡ asNat ab * montgomeryRadix ^ 2 [MOD order] := h_rr.mul_left _
    _ = (asNat ab * montgomeryRadix) * montgomeryRadix := by ring
    _ ≡ (asNat a * asNat b) * montgomeryRadix [MOD order] := h_ab'.mul_right _

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

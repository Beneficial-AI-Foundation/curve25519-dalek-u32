/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Dalek32.Scalar.MulInternal
import Dalek32.Scalar.MontgomeryReduce

/-!
# Fixed top-level specification for `Scalar29.montgomery_mul`

For normalized inputs whose product is below `R * order`, returns the canonical
Montgomery product, where `R = 2^261`. The fixed top-level specification is proved
by composing the multiplication and Montgomery reduction specifications.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_mul`**

Returns a normalized canonical scalar congruent to `a * b / R` modulo the scalar
order. The product bound is the input range required by Montgomery reduction. -/
@[step]
theorem montgomery_mul_spec (a b : Scalar29)
    (h_a : IsNormalized a) (h_b : IsNormalized b)
    (h_range : asNat a * asNat b < montgomeryRadix * order) :
    montgomery_mul a b ⦃ (r : Scalar29) =>
      (asNat r * montgomeryRadix) % order = (asNat a * asNat b) % order ∧
      IsNormalized r ∧
      asNat r < order ⦄ := by
  unfold montgomery_mul
  step with mul_internal_spec as ⟨limbs, h_exact, h_bounds⟩
  step with montgomery_reduce_spec as ⟨r, h_mod, h_norm, h_lt⟩
  exact ⟨by simpa only [h_exact] using h_mod, h_norm, h_lt⟩

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

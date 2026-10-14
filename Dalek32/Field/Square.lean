/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Dalek32.Field.SquareInner
import Dalek32.Field.Reduce

/-!
# Squaring contract and composition

The input domain `SquareInputBounds` (`19 * limb < 2^32`) comfortably contains the
sum of two reduced limbs, including their carry slack. The composition uses the
proved square_inner and reduce specifications.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- Field squaring, including success and output bounds for further squaring. -/
@[step]
theorem square_spec (self : FieldElement2625) (h_bounds : SquareInputBounds self) :
    square self ⦃ (result : FieldElement2625) =>
      toNat result % p = toNat self ^ 2 % p ∧ ReducedBounds result ⦄ := by
  unfold square
  apply spec_bind (square_inner_spec self h_bounds)
  intro z hz
  apply spec_mono (reduce_spec z hz.2)
  intro result hr
  exact ⟨hr.2.1.trans hz.1, hr.2.2⟩

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

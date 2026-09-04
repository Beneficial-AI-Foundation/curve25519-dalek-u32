/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions

/-!
# Spec theorem for `ZERO`

`ZERO` returns a `Result FieldElement2625` that is the field element `0` represented using ten
limbs in the alternating `2^26/2^25` radix.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 292:4-292:100
-/

open Aeneas Aeneas.Std
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::ZERO`
The Nat value of a 10 limb array of all zeroes is 0. -/
@[step]
theorem ZERO_spec :
    ZERO ⦃ (result : FieldElement2625) =>
      result.toNat = 0 ⦄ := by
  unfold ZERO
  rfl


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

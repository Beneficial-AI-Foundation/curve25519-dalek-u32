/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions

/-!
# Spec theorem for `ONE`

`ONE` returns a `Result FieldElement2625` that is the field element `1` represented using ten
limbs in the alternating `2^26/2^25` radix.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 294:4-294:99
-/

open Aeneas Aeneas.Std
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::ONE`
The Nat value of a 10 limb array with the first limb being 1 and the rest being all zeroes is 1. -/
@[step]
theorem ONE_spec :
    ONE ⦃ (result : FieldElement2625) =>
      result.toNat = 1 ⦄ := by
  unfold ONE
  rfl


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

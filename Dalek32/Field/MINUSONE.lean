/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions

/-!
# Spec theorem for `MINUS_ONE`

`MINUS_ONE` returns a `Result FieldElement2625` that is the field element `-1` represented using
ten limbs in the alternating `2^26/2^25` radix.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 296:4-299:7
-/

open Aeneas Aeneas.Std
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::MINUS_ONE`
Each limb of the array is saturated, i.e. even limbs equal to 2 ^ 26 - 1, while odd limbs equal to
2 ^ 25 - 1, except for limbs[0] that is 2 ^ 26 - 20. Adding these up with alternating weights 2 ^ 26
and 2 ^ 25 gives 2 ^ 255 - 20, which equals to p - 1, the canonical representative of -1 (mod p). -/
@[step]
theorem MINUS_ONE_spec :
    MINUS_ONE ⦃ (result : FieldElement2625) =>
      result.toNat = p - 1 ⦄ := by
  unfold MINUS_ONE p
  rfl


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

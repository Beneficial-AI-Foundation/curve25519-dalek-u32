/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs

/-!
# Spec theorem for `reduce.LOW_25_BITS`

`reduce.LOW_25_BITS` returns a `Result Std.U64` that is calculated as the bit 1 shifted to the
left by 25 and then subtracting one.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 338:8-338:47
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::reduce::LOW_25_BITS`
Bit shift to the left by 25 in terms of natural numbers is multiplying by 2^25, hence the result
equals to 2^25-1. -/
@[step]
theorem reduce.LOW_25_BITS_spec :
    reduce.LOW_25_BITS ⦃ (result : U64) => result.bv.toNat = 2^25-1 ⦄ := by
  unfold reduce.LOW_25_BITS
  rfl


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

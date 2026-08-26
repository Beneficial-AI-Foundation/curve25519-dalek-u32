/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs

/-!
# Spec theorem for `from_bytes.LOW_23_BITS`

`from_bytes.LOW_23_BITS` returns a `Result Std.U64` that is calculated as the bit 1 shifted to the
left by 23 and then subtracting one.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 419:8-419:47
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::from_bytes::LOW_23_BITS`
Bit shift to the left by 23 in terms of natural numbers is multiplying by 2^23, hence the result
equals to 2^23-1. -/
@[step]
theorem from_bytes.LOW_23_BITS_spec :
    from_bytes.LOW_23_BITS ⦃ (result : U64) => result.bv.toNat = 2^23-1 ⦄ := by
  unfold from_bytes.LOW_23_BITS
  rfl


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

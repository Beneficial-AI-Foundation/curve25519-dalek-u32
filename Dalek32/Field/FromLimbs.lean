/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: András Némedy Varga
-/
import translated.Funs
open Aeneas Aeneas.Std
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-!
# Spec theorem for `from_limbs`

`from_limbs` converts an `Array Std.U32 10#usize` into a `Result Array Std.U32 10#usize` simply by
applying the `ok` constructor to the input array. It is essentially just a type conversion.

Source: "curve25519-dalek/src/backend/serial/u32/field.rs", lines 287:4-289:5
-/

/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::from_limbs`
Since the function just applies the `ok` constructor to the input, the result is definitionally
equal to the input. -/
@[step]
theorem from_limbs_spec (limbs : Array Std.U32 10#usize) :
    from_limbs limbs ⦃ (result : Array Std.U32 10#usize) =>
      result = limbs ⦄ := by
  unfold from_limbs
  rfl


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

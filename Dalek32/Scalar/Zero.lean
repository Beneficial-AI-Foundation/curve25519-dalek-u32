/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Definitions
import translated.Funs

/-!
# Spec theorem for `curve25519_dalek::backend::serial::u32::scalar::Scalar29::ZERO`

This constant represents the scalar value zero. The extracted constant is a value, so its
specification is a direct equality rather than a result-producing function specification.

Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 61:4-61:69
-/

open Aeneas Aeneas.Std

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

/-- **Spec theorem for `curve25519_dalek::backend::serial::u32::scalar::Scalar29::ZERO`**

The natural-number interpretation of `ZERO` is zero. -/
@[simp]
theorem ZERO_spec : asNat ZERO = 0 := by
  unfold ZERO
  decide

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

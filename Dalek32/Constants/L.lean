/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Scalar.Math
import translated.Funs

/-!
# Spec theorem for `curve25519_dalek::backend::serial::u32::constants::L`

This constant represents the order of the Curve25519 base point.

Source: "curve25519-dalek/src/backend/serial/u32/constants.rs", lines 98:0-101:3
-/

open Aeneas Aeneas.Std
open Curve25519Dalek.backend.serial.u32.scalar

namespace Curve25519Dalek.backend.serial.u32.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u32::constants::L`**
The natural-number interpretation of the nine-limb encoding `L` equals the scalar order. -/
@[simp]
theorem L_spec : Scalar29.asNat L = Scalar29.order := by
  unfold L
  decide

/-- Every limb of `L` fits in the radix-`2^29` representation. -/
theorem L_limbs_lt : ∀ i < 9, L[i]!.val < 2 ^ 29 := by
  unfold L
  decide

end Curve25519Dalek.backend.serial.u32.constants

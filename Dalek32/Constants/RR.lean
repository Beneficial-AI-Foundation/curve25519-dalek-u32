/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Definitions
import translated.Funs

/-!
# Spec theorem for `curve25519_dalek::backend::serial::u32::constants::RR`

This constant represents `(2^261)^2 mod L`, where `L` is the scalar order.

Source: "curve25519-dalek/src/backend/serial/u32/constants.rs", lines 113:0-116:3
-/

open Aeneas Aeneas.Std
open Curve25519Dalek.backend.serial.u32.scalar

namespace Curve25519Dalek.backend.serial.u32.constants

set_option exponentiation.threshold 261

/-- **Spec theorem for `curve25519_dalek::backend::serial::u32::constants::RR`**
The nine-limb encoding `RR` represents the square of the Montgomery radix modulo the
scalar order. -/
@[simp]
theorem RR_spec :
    Scalar29.asNat RR % Curve25519Dalek.order =
      Scalar29.montgomeryRadix ^ 2 % Curve25519Dalek.order := by
  unfold RR Curve25519Dalek.order
  decide

/-- Every limb of `RR` fits in the radix-`2^29` representation. -/
theorem RR_limbs_lt : ∀ i < 9, RR[i]!.val < Scalar29.limbRadix := by
  unfold RR Scalar29.limbRadix
  decide

/-- The represented value of `RR` is the canonical residue modulo the scalar order. -/
theorem RR_value_lt_order : Scalar29.asNat RR < Curve25519Dalek.order := by
  unfold RR Scalar29.asNat Curve25519Dalek.order Aeneas.Std.Array.uScalarToNatRadix
  decide

end Curve25519Dalek.backend.serial.u32.constants

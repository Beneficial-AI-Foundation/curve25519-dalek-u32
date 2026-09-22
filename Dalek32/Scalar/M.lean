/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import translated.Funs

/-!
# Spec theorem for `curve25519_dalek::backend::serial::u32::scalar::m`

This helper widens two `u32` operands to `u64` and returns their exact product.

Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 55:0-57:1
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar

/-- **Spec theorem for `curve25519_dalek::backend::serial::u32::scalar::m`**

The function always succeeds and returns the exact `u64` product of its inputs. -/
@[step]
theorem m_spec (x y : U32) :
    m x y ⦃ (result : U64) =>
      result.val = x.val * y.val ⦄ := by
  unfold m
  step*

end Curve25519Dalek.backend.serial.u32.scalar

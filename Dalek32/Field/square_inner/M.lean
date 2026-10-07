/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs

/-!
# Spec theorem for `square_inner.m`

This helper of `FieldElement2625::square_inner` widens two `u32` operands to `u64` and returns
their exact product.

Source: "curve25519-dalek/src/backend/serial/u32/field.rs", lines 572:8-574:9
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::square_inner::m`**

The function always succeeds and returns the exact `u64` product of its inputs. -/
@[step]
theorem square_inner.m_spec (x y : U32) :
    square_inner.m x y ⦃ (result : U64) =>
      result.val = x.val * y.val ⦄ := by
  unfold square_inner.m
  step*

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

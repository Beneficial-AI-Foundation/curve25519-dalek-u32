/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs

/-!
# Spec theorem for `mul.m`

This helper of `<&FieldElement2625 as Mul<&FieldElement2625>>::mul` widens two `u32` operands to
`u64` and returns their exact product.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 132:8-134:9
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field
namespace MulSharedAFieldElement2625SharedBFieldElement2625FieldElement2625

/-- **Spec theorem for**
`<&curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
core::ops::Mul<&FieldElement2625>>::mul::m`
The function always succeeds and returns the exact `u64` product of its inputs. The proof unfolds
`mul.m` and `step*` steps through the two lossless casts to `u64` and the checked multiplication,
whose no-overflow side condition holds since `x, y ≤ 2 ^ 32 - 1` gives a product of at most
`(2 ^ 32 - 1) ^ 2 < 2 ^ 64`. -/
@[step]
theorem mul.m_spec (x y : U32) :
    mul.m x y ⦃ (result : U64) =>
      result.val = x.val * y.val ⦄ := by
  unfold mul.m
  step*

end MulSharedAFieldElement2625SharedBFieldElement2625FieldElement2625
end Curve25519Dalek.backend.serial.u32.field

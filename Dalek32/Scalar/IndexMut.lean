/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import translated.Funs

/-!
# Spec theorem for `index_mut`

`<curve25519_dalek::backend::serial::u32::scalar::Scalar29 as
core::ops::IndexMut<usize>>::index_mut`

Mutably indexes a `Scalar29`, returning the selected limb and a write-back function.

Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 48:4-50:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29.Insts.CoreOpsIndexIndexMutUsizeU32

/-- **Spec theorem for**
`<curve25519_dalek::backend::serial::u32::scalar::Scalar29 as
core::ops::IndexMut<usize>>::index_mut`

The function succeeds for an index below nine, returns that limb, and provides the expected
array write-back function. -/
@[step]
theorem index_mut_spec (self : Scalar29) (_index : Usize)
    (h_bound : _index.val < 9) :
    index_mut self _index ⦃ (limb : U32) (back : U32 → Scalar29) =>
      limb = self.val[_index.val]! ∧
      back = Aeneas.Std.Array.set self _index ⦄ := by
  unfold index_mut
  step*
  grind

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29.Insts.CoreOpsIndexIndexMutUsizeU32

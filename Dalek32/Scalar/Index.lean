/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import translated.Funs

/-!
# Spec theorem for `index`

`<curve25519_dalek::backend::serial::u32::scalar::Scalar29 as
core::ops::Index<usize>>::index`

Indexes a `Scalar29` by `usize`, returning the `u32` limb at the requested position.

Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 42:4-44:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29.Insts.CoreOpsIndexIndexUsizeU32

/-- **Spec theorem for**
`<curve25519_dalek::backend::serial::u32::scalar::Scalar29 as
core::ops::Index<usize>>::index`

The function succeeds for an index below nine and returns the limb at that index. -/
@[step]
theorem index_spec (self : Scalar29) (_index : Usize)
    (h_bound : _index.val < 9) :
    index self _index ⦃ (result : U32) =>
      result = self.val[_index.val]! ⦄ := by
  have h_index : _index.val < self.val.length := by
    rw [Aeneas.Std.Array.length_eq]
    exact h_bound
  simpa only [index, getElem!_pos self.val _index.val h_index] using
    Aeneas.Std.Array.index_usize_spec self _index h_index

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29.Insts.CoreOpsIndexIndexUsizeU32

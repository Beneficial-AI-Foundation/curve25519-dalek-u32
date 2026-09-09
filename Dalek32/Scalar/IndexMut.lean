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
    index_mut self _index ⦃ (result : U32 × (U32 → Scalar29)) =>
      result.1 = self.val[_index.val]! ∧
      result.2 = Aeneas.Std.Array.set self _index ⦄ := by
  have h_index : _index.val < self.val.length := by
    rw [Aeneas.Std.Array.length_eq]
    exact h_bound
  unfold index_mut
  step*
  simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos, and_self]

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29.Insts.CoreOpsIndexIndexMutUsizeU32

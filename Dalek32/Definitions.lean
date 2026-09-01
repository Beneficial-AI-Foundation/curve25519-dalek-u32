/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import Aeneas
import translated.Types

/-! # Common definitions

Common definitions used across spec theorems: field constants, conversion functions, etc.
-/


/-! ## Aeneas related definitions-/

namespace Aeneas.Std

/-- Turns an `Array (UScalar ty) Usize` into a `Nat` using `2 ^ exp` as the radix.
Omitting `exp` the radix defaults to `2^ty.numBits`. -/
def Array.uScalarToNatRadix {ty : UScalarTy} {n : Usize}
  (limbs : Array (UScalar ty) n) (exp : Nat := ty.numBits) : Nat :=
  ∑ i ∈ Finset.range n.val, 2 ^ (exp * i) * (limbs[i]!).val

/-- Turns an `Array (UScalar ty) Usize` into a `Nat` using `2 ^ exp` as the radix.
Omitting `exp` the radix defaults to `2^ty.numBits`. -/
def Array.uScalarToNatField2625 {ty : UScalarTy} (limbs : Array (UScalar ty) 10#usize) : Nat :=
  ∑ i ∈ Finset.range 10, 2 ^ (26 * ((i + 1) / 2) + 25 * (i / 2)) * (limbs[i]!).val

end Aeneas.Std


/-! ## Curve25519-Dalek related definitions-/

open Aeneas Aeneas.Std

namespace curve25519_dalek

/-- The field prime `p = 2^255 - 19` -/
def p : Nat := 2 ^ 255 - 19

attribute [irreducible] p


/-! ## FieldELement2625 related definitions (nested into curve25519_dalek)-/

namespace backend.serial.u32.field.FieldElement2625

def toNat (x : FieldElement2625) := Array.uScalarToNatField2625 x

end backend.serial.u32.field.FieldElement2625

end curve25519_dalek

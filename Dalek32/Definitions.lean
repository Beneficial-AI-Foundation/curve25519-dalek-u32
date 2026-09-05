/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga, Wojciech Aleksander Wołoszyn
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

/-- Turns an `Array (UScalar ty) 10#usize` into a `Nat` using `2 ^ 26` and `2 ^ 25` alternatingly
as a radix. -/
def Array.uScalarToNatField2625 {ty : UScalarTy} (limbs : Array (UScalar ty) 10#usize) : Nat :=
  ∑ i ∈ Finset.range 10, 2 ^ (26 * ((i + 1) / 2) + 25 * (i / 2)) * (limbs[i]!).val

end Aeneas.Std


/-! ## Curve25519Dalek related definitions-/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

/-- The field prime `p = 2^255 - 19`. -/
def p : Nat := 2 ^ 255 - 19

attribute [irreducible] p

/-- The order of the Ed25519 base point, shared by all scalar backends. -/
def order : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

-- Keep the large numeral out of routine reduction; use the lemmas in `Auxiliary.lean`.
attribute [irreducible] order


/-! ## FieldELement2625 related definitions (nested into Curve25519Dalek)-/

namespace backend.serial.u32.field.FieldElement2625

/-- Interpret a `FieldElement2625` (ten u32 limbs used to represent 26/25 bits alternatingly) as a
natural number. -/
def toNat (x : FieldElement2625) : Nat := Array.uScalarToNatField2625 x

end backend.serial.u32.field.FieldElement2625


/-! ## Scalar29 related definitions (nested into Curve25519Dalek) -/

namespace backend.serial.u32.scalar.Scalar29

/-- The Montgomery radix for nine radix-`2^29` limbs. -/
def montgomeryRadix : Nat := 2 ^ 261

/-- Interpret a `Scalar29` as a natural number. -/
def asNat (limbs : Scalar29) : Nat :=
  limbs.uScalarToNatRadix 29

/-- Interpret a seventeen-coefficient wide scalar value as a natural number. -/
def wideAsNat (limbs : Array U64 17#usize) : Nat :=
  limbs.uScalarToNatRadix 29

/-- Interpret a 32-byte little-endian scalar input as a natural number. -/
def bytes32AsNat (bytes : Array U8 32#usize) : Nat :=
  bytes.uScalarToNatRadix 8

/-- Interpret a 64-byte little-endian scalar input as a natural number. -/
def bytes64AsNat (bytes : Array U8 64#usize) : Nat :=
  bytes.uScalarToNatRadix 8

end backend.serial.u32.scalar.Scalar29

end Curve25519Dalek

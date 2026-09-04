/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Parity

/-!
# Mathematical foundations for `Scalar29`

This file gives the serial-u32 scalar representation its mathematical meaning. A `Scalar29` is
interpreted as nine little-endian radix-`2^29` limbs, and a wide scalar value as seventeen
coefficients in the same radix. The byte interpretations reuse the shared little-endian radix
encoding from `Dalek32.Definitions`.
-/

open Aeneas.Std

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

/-- The order of the Ed25519 base point. -/
def order : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

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

attribute [-simp] Int.reducePow Nat.reducePow
set_option exponentiation.threshold 261

/-- The scalar order fits in 253 bits. -/
theorem order_lt_two_pow_253 : order < 2 ^ 253 := by
  unfold order
  omega

/-- The scalar order is below the Montgomery radix. -/
theorem order_lt_montgomeryRadix : order < montgomeryRadix := by
  unfold order montgomeryRadix
  omega

/-- The Montgomery radix is coprime to the scalar order. -/
theorem montgomeryRadix_coprime_order : Nat.Coprime montgomeryRadix order := by
  unfold montgomeryRadix order
  exact Nat.Coprime.pow_left 261 (by norm_num [Nat.Coprime])

/-- Cancel the Montgomery radix from both sides of a congruence modulo the scalar order. -/
theorem cancel_montgomeryRadix {a b : Nat}
    (h : a * montgomeryRadix ≡ b * montgomeryRadix [MOD order]) :
    a ≡ b [MOD order] := by
  exact Nat.ModEq.cancel_right_of_coprime montgomeryRadix_coprime_order.symm h

/-- Nine radix-`2^29` limbs represent a value below the Montgomery radix. -/
theorem asNat_bounded (s : Scalar29)
    (hs : ∀ i < 9, s[i]!.val < 2 ^ 29) :
    asNat s < montgomeryRadix := by
  change (∑ i ∈ Finset.range 9, 2 ^ (29 * i) * s[i]!.val) < 2 ^ 261
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  have h0 := hs 0 (by omega)
  have h1 := hs 1 (by omega)
  have h2 := hs 2 (by omega)
  have h3 := hs 3 (by omega)
  have h4 := hs 4 (by omega)
  have h5 := hs 5 (by omega)
  have h6 := hs 6 (by omega)
  have h7 := hs 7 (by omega)
  have h8 := hs 8 (by omega)
  omega

/-- One weighted scalar limb is bounded by the represented value. -/
theorem limb_le_asNat (s : Scalar29) (i : Nat) (hi : i < 9) :
    2 ^ (29 * i) * s[i]!.val ≤ asNat s := by
  unfold asNat Aeneas.Std.Array.uScalarToNatRadix
  exact Finset.single_le_sum
    (f := fun j => 2 ^ (29 * j) * s[j]!.val)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hi)

/-- One weighted wide coefficient is bounded by the represented wide value. -/
theorem wide_limb_le_wideAsNat
    (s : Array U64 17#usize) (i : Nat) (hi : i < 17) :
    2 ^ (29 * i) * s[i]!.val ≤ wideAsNat s := by
  unfold wideAsNat Aeneas.Std.Array.uScalarToNatRadix
  exact Finset.single_le_sum
    (f := fun j => 2 ^ (29 * j) * s[j]!.val)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hi)

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

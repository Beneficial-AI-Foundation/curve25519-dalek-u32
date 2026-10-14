/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Dalek32.Definitions
import Dalek32.Lint.Basic
import translated.Funs

/-! # Limb bounds for field squaring -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- Overflow-maximal input domain of `square_inner`: `19 * limb` must fit in a `u32`.
This is the exact integer form of the `b < 1.752` headroom in `field.rs`, applied
uniformly to all limbs. It covers repeated squaring and the unreduced sum in point
doubling, and is the widest domain under which `reduce` still accepts the result. -/
def SquareInputBounds (x : FieldElement2625) : Prop :=
  ∀ i < 10, 19 * x[i]!.val < 2 ^ 32

/-- Carry slack is needed on odd limbs; this does not imply canonicality. -/
def ReducedBounds (x : FieldElement2625) : Prop :=
  ∀ i < 10, x[i]!.val < 2 ^ (26 - i % 2) + i % 2 * 2 ^ 18

theorem reducedBounds_squareInputBounds {x : FieldElement2625}
    (h : ReducedBounds x) : SquareInputBounds x := by
  intro i hi
  have hx := h i hi
  have hm : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases hm with hm | hm <;> simp only [hm] at hx ⊢ <;> norm_num at hx ⊢ <;> omega

/-- The top-level pow2k domain is contained in the wider square domain. -/
theorem pow2kBounds_squareInputBounds {x : FieldElement2625}
    (h : ∀ i < 10, x[i]!.val < 2 ^ (27 - i % 2)) : SquareInputBounds x := by
  intro i hi
  have hx := h i hi
  have hm : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases hm with hm | hm <;> simp only [hm] at hx ⊢ <;> norm_num at hx ⊢ <;> omega

/-- Adding two reduced limb arrays satisfies the square input bound, without
requiring a reduction between addition and squaring. -/
theorem reducedBounds_add_squareInputBounds {x y z : FieldElement2625}
    (hx : ReducedBounds x) (hy : ReducedBounds y)
    (hz : ∀ i < 10, z[i]!.val = x[i]!.val + y[i]!.val) :
    SquareInputBounds z := by
  intro i hi
  have hxi := hx i hi
  have hyi := hy i hi
  rw [hz i hi]
  have hm : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases hm with hm | hm <;> simp only [hm] at hxi hyi ⊢ <;>
    norm_num at hxi hyi ⊢ <;> omega

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

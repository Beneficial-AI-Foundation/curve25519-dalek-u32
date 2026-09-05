/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga, Wojciech Aleksander Wołoszyn
-/
import Dalek32.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum

/-! # Auxiliary theorems

Theorems which are useful for proving spec theorems in this project, but aren't available upstream.
This file is for theorems which depend only on Definitions.lean, not on Funs.lean. -/

open Aeneas Aeneas.Std Finset

/-! ## Aeneas specific theorems-/

namespace Aeneas.Std

/-- Two `UScalar` arrays with pointwise-equal limb values have equal `Nat` representations
for any radix. -/
theorem Array.toNatRadix_congr {ty : UScalarTy} {n : Usize} {exp : Nat}
    (x y : Array (UScalar ty) n) (h : ∀ i, i < n.val → x[i]!.val = y[i]!.val) :
      x.uScalarToNatRadix exp = y.uScalarToNatRadix exp := by
  unfold uScalarToNatRadix
  rw [sum_congr (f := fun i => 2 ^ (exp * i) * x[i]!.val)
  (g := fun i => 2 ^ (exp * i) * y[i]!.val)
  (by rfl) (by intro i hi; rewrite [mem_range] at hi; rw[h i hi])]

/-- A weighted limb is bounded by the full nonnegative radix sum. -/
theorem Array.uScalarToNatRadix_limb_le {ty : UScalarTy} {n : Usize}
    (limbs : Array (UScalar ty) n) (exp i : Nat) (hi : i < n.val) :
    2 ^ (exp * i) * limbs[i]!.val ≤ limbs.uScalarToNatRadix exp := by
  unfold uScalarToNatRadix
  exact Finset.single_le_sum
    (f := fun j => 2 ^ (exp * j) * limbs[j]!.val)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hi)

/-- Two `UScalar` arrays of `length 10` with pointwise-equal limb values have equal `Nat`
representations in the alternating `2^26/2^25` radix. -/
theorem Array.toNatField2625_congr {ty : UScalarTy}
    (x y : Array (UScalar ty) 10#usize) (h : ∀ i, i < 10 → x[i]!.val = y[i]!.val) :
      x.uScalarToNatField2625 = y.uScalarToNatField2625 := by
  unfold uScalarToNatField2625
  rw [sum_congr (by rfl) (by intro i hi; rewrite [mem_range] at hi; rw[h i hi])]


end Aeneas.Std


/-! ## Curve25519Dalek specific theorems-/

namespace Curve25519Dalek

/-Characterization API for `p`: later proofs use only these lemmas below, never the literal value.
`p` is made irreducible in `Definitions.lean` to avoid accidental unfolding.-/

theorem p_add_19 : p + 19 = 2 ^ 255 := by norm_num [p]

theorem p_pos : 0 < p := by norm_num [p]

theorem two_pow_254_lt_p : 2 ^ 254 < p := by norm_num [p]

theorem p_lt_two_pow_255 : p < 2 ^ 255 := by norm_num [p]


/-! ## Shared scalar-order properties -/

-- Unfold `order` only while establishing its arithmetic interface.

/-- The scalar order is positive. -/
theorem order_pos : 0 < order := by
  unfold order
  decide

/-- The scalar order exceeds `2^252`. -/
theorem two_pow_252_lt_order : 2 ^ 252 < order := by
  unfold order
  decide

/-- The scalar order fits in 253 bits. -/
theorem order_lt_two_pow_253 : order < 2 ^ 253 := by
  unfold order
  decide

/-- The scalar order is coprime to two. -/
theorem two_coprime_order : Nat.Coprime 2 order := by
  unfold order
  decide


/-! ## FieldElement2625 specific theorems (nested into Curve25519Dalek)-/

namespace backend.serial.u32.field.FieldElement2625

@[simp, scalar_tac_simps, grind =, agrind =]
theorem toNat_eq (x : FieldElement2625) : x.toNat = Array.uScalarToNatField2625 x := rfl

/-- Two field eLements with pointwise-equal limb values have equal `Nat` representations. -/
theorem toNat_congr (x y : FieldElement2625) (h : ∀ i, i < 10 → x[i]!.val = y[i]!.val) :
    x.toNat = y.toNat := by
   rw [toNat_eq, toNat_eq]; rw [Array.toNatField2625_congr]; exact h


end backend.serial.u32.field.FieldElement2625


/-! ## Scalar29 specific theorems (nested into Curve25519Dalek) -/

namespace backend.serial.u32.scalar.Scalar29

set_option exponentiation.threshold 261 in
/-- The shared scalar order is below the serial-u32 Montgomery radix. -/
theorem order_lt_montgomeryRadix : order < montgomeryRadix := by
  apply lt_trans Curve25519Dalek.order_lt_two_pow_253
  unfold montgomeryRadix
  decide

set_option exponentiation.threshold 261 in
/-- The serial-u32 Montgomery radix is coprime to the shared scalar order. -/
theorem montgomeryRadix_coprime_order : Nat.Coprime montgomeryRadix order := by
  unfold montgomeryRadix
  exact Nat.Coprime.pow_left 261 Curve25519Dalek.two_coprime_order

/-- Cancel the Montgomery radix from both sides of a congruence modulo the scalar order. -/
theorem cancel_montgomeryRadix {a b : Nat}
    (h : a * montgomeryRadix ≡ b * montgomeryRadix [MOD order]) :
    a ≡ b [MOD order] := by
  exact Nat.ModEq.cancel_right_of_coprime montgomeryRadix_coprime_order.symm h

set_option exponentiation.threshold 261 in
/-- Nine radix-`2^29` limbs represent a value below the Montgomery radix. -/
theorem asNat_bounded (s : Scalar29)
    (hs : ∀ i < 9, s[i]!.val < 2 ^ 29) :
    asNat s < montgomeryRadix := by
  change (∑ i ∈ Finset.range 9, 2 ^ (29 * i) * s[i]!.val) < 2 ^ 261
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  grind

end backend.serial.u32.scalar.Scalar29

end Curve25519Dalek


/-! ## General theorems-/

/-- Disjoint `|||` is addition: the low operand fits under the shift.
Analogue of `Nat.two_pow_add_eq_or_of_lt` but with reversed order. -/
theorem Nat.or_two_pow_eq_add_of_lt {a b i : Nat} (h : a < 2 ^ i) :
    a ||| b * 2 ^ i = a + b * 2 ^ i := by
  rw [Nat.lor_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h, Nat.add_comm]

/-- Adding a low part `m < l` to a multiple of `l` commutes with reduction modulo `k * l` -/
theorem Nat.add_mul_mod_mul_right_of_lt {m n k l : Nat} (hm : m < l) :
    (m + n * l) % (k * l) = m + n * l % (k * l) := by
  by_cases hk : 0 < k
  · have hlt : m + n * l % (k * l) < k * l := by
      rw [Nat.mul_mod_mul_right]
      calc m + n % k * l
          < l + n % k * l := Nat.add_lt_add_right hm _
        _ = (n % k + 1) * l := by ring
        _ ≤ k * l := Nat.mul_le_mul_right _ (Nat.mod_lt n hk)
    have hmk : m < k * l := Nat.lt_of_lt_of_le hm (Nat.le_mul_of_pos_left l hk)
    rw [Nat.add_mod, Nat.mod_eq_of_lt hmk, Nat.mod_eq_of_lt hlt]
  · simp [Nat.eq_zero_of_not_pos hk]

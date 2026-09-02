/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import Dalek32.Definitions
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
      x.uScalarToNatRadix exp = y.uScalarToNatRadix exp ∧
      x.uScalarToNatRadix = y.uScalarToNatRadix := by
  unfold uScalarToNatRadix
  split_conjs
  · rw [sum_congr (f := fun i => 2 ^ (exp * i) * x[i]!.val)
    (g := fun i => 2 ^ (exp * i) * y[i]!.val)
    (by rfl) (by intro i hi; rewrite [mem_range] at hi; rw[h i hi])]
  · rw [sum_congr (f := fun i => 2 ^ (ty.numBits * i) * x[i]!.val)
    (g := fun i => 2 ^ (ty.numBits * i) * y[i]!.val)
    (by rfl) (by intro i hi; rewrite [mem_range] at hi; rw[h i hi])]

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


/-! ## FieldElement2625 specific theorems (nested into Curve25519Dalek)-/

namespace backend.serial.u32.field.FieldElement2625

@[simp, scalar_tac_simps, grind =, agrind =]
theorem toNat_eq (x : FieldElement2625) : x.toNat = Array.uScalarToNatField2625 x := rfl

/-- Two field eLements with pointwise-equal limb values have equal `Nat` representations. -/
theorem toNat_congr (x y : FieldElement2625) (h : ∀ i, i < 10 → x[i]!.val = y[i]!.val) :
    x.toNat = y.toNat := by
   rw [toNat_eq, toNat_eq]; rw [Array.toNatField2625_congr]; exact h


end backend.serial.u32.field.FieldElement2625

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

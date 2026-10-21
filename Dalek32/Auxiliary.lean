/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga, Wojciech Aleksander Wołoszyn
-/
import Dalek32.Definitions
import Dalek32.Lint.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum

/-! # Auxiliary theorems

Theorems which are useful for proving spec theorems in this project, but aren't available upstream.
This file is for theorems which depend only on Definitions.lean, not on Funs.lean. -/

open Aeneas Aeneas.Std Finset

/-! ## Aeneas specific theorems-/

namespace Aeneas.Std

-- Used in: (none)
/-- Two `UScalar` arrays with pointwise-equal limb values have equal `Nat` representations
for any radix. -/
theorem Array.toNatRadix_congr {ty : UScalarTy} {n : Usize} {exp : Nat}
    (x y : Array (UScalar ty) n) (h : ∀ i, i < n.val → x[i]!.val = y[i]!.val) :
      x.uScalarToNatRadix exp = y.uScalarToNatRadix exp := by
  unfold uScalarToNatRadix
  rw [sum_congr (f := fun i => 2 ^ (exp * i) * x[i]!.val)
  (g := fun i => 2 ^ (exp * i) * y[i]!.val)
  (by rfl) (by intro i hi; rewrite [mem_range] at hi; rw[h i hi])]

-- Used in: (none)
/-- A weighted limb is bounded by the full nonnegative radix sum. -/
theorem Array.uScalarToNatRadix_limb_le {ty : UScalarTy} {n : Usize}
    (limbs : Array (UScalar ty) n) (exp i : Nat) (hi : i < n.val) :
    2 ^ (exp * i) * limbs[i]!.val ≤ limbs.uScalarToNatRadix exp := by
  unfold uScalarToNatRadix
  exact Finset.single_le_sum
    (f := fun j => 2 ^ (exp * j) * limbs[j]!.val)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hi)

-- Used in: Dalek32/Scalar/Add.lean, Dalek32/Scalar/ConditionalAddL.lean, Dalek32/Scalar/Sub.lean
/-- Replacing one limb changes its weighted contribution. -/
theorem Array.uScalarToNatRadix_set {ty : UScalarTy} {n : Usize}
    (a : Array (UScalar ty) n) (exp : Nat) (i : Usize) (x : UScalar ty)
    (hi : i.val < n.val) :
    (a.set i x).uScalarToNatRadix exp + 2 ^ (exp * i.val) * a[i.val]!.val =
      a.uScalarToNatRadix exp + 2 ^ (exp * i.val) * x.val := by
  unfold uScalarToNatRadix
  simp only [← sum_sdiff (by rewrite [singleton_subset_iff, mem_range]; exact hi), sum_singleton]
  simp_lists
  simp only [Nat.add_assoc]
  nth_rewrite 2 [Nat.add_comm]; rewrite [Nat.add_right_cancel_iff]
  exact sum_congr (by rfl)
    (by intro j hj; rewrite [mem_sdiff, mem_range, mem_singleton] at hj; simp_lists)


-- Used in: Dalek32/Auxiliary.lean (toNat_congr), Dalek32/Field/Reduce.lean,
--   Dalek32/Field/ToBytes.lean
/-- Two `UScalar` arrays of `length 10` with pointwise-equal limb values have equal `Nat`
representations in the alternating `2^26/2^25` radix. -/
theorem Array.toNatField2625_congr {ty ty' : UScalarTy}
    (x : Array (UScalar ty) 10#usize) (y : Array (UScalar ty') 10#usize)
    (h : ∀ i, i < 10 → x[i]!.val = y[i]!.val) :
      x.uScalarToNatField2625 = y.uScalarToNatField2625 := by
  unfold uScalarToNatField2625
  rw [sum_congr (by rfl) (by intro i hi; rewrite [mem_range] at hi; rw[h i hi])]


-- Used in: Dalek32/Auxiliary.lean (index_usize_eq, index_mut_usize_eq),
--   Dalek32/Field/AddAssign.lean, Dalek32/Field/ToBytes.lean
/-- Checked indexing into the underlying list of an `Std.Array` agrees with `getElem!`. Unlike
`List.Inhabited_getElem_eq_getElem!` (a `def`) this can be used by `simp`. -/
theorem Array.getElem_val_eq_getElem! {α : Type} [Inhabited α] {N : Usize} (a : Std.Array α N)
    (j : Nat) (h : j < (↑a : List α).length) : (↑a : List α)[j] = a[j]! := by
  rw [Array.getElem!_Nat_eq, List.Inhabited_getElem_eq_getElem! _ _ h]


-- Used in: Dalek32/Field/ConditionalAssign.lean, Dalek32/Field/ConditionalSwap.lean
/-- Writing an array's own entry back at the same index leaves the array unchanged. Unlike
`Array.set_getElem_eq`, it matches the `(↑a)[j]` list-index form produced by `simp`. -/
theorem Array.set_val_getElem_self {α : Type} {n : Usize} (a : Std.Array α n) (i : Usize)
    (j : Nat) (h : j < a.val.length) (h_ij : i.val = j) : a.set i a.val[j] = a := by
  subst h_ij
  apply Subtype.ext
  simp only [Std.Array.set_val_eq, List.set_getElem_self]


end Aeneas.Std


/-! ## Curve25519Dalek specific theorems-/

namespace Curve25519Dalek

/-Characterization API for `p`: later proofs use only these lemmas below, never the literal value.
`p` is made irreducible in `Definitions.lean` to avoid accidental unfolding.-/

-- Used in: Dalek32/Field/Mul.lean, Dalek32/Field/Negate.lean, Dalek32/Field/Reduce.lean,
--   Dalek32/Field/SquareInner.lean, Dalek32/Field/SubAssign.lean, Dalek32/Field/ToBytes.lean
theorem p_add_19 : p + 19 = 2 ^ 255 := by norm_num [p]

-- Used in: Dalek32/Field/ToBytes.lean
theorem p_pos : 0 < p := by norm_num [p]

-- Used in: (none)
theorem two_pow_254_lt_p : 2 ^ 254 < p := by norm_num [p]

-- Used in: Dalek32/Field/ToBytes.lean
theorem p_lt_two_pow_255 : p < 2 ^ 255 := by norm_num [p]


/-! ## Shared scalar-order properties -/

-- Unfold `order` only while establishing its arithmetic interface.

-- Used in: Dalek32/Scalar/MontgomeryReduce.lean
/-- The scalar order is positive. -/
theorem order_pos : 0 < order := by
  unfold order
  decide

-- Used in: (none)
/-- The scalar order exceeds `2^252`. -/
theorem two_pow_252_lt_order : 2 ^ 252 < order := by
  unfold order
  decide

-- Used in: Dalek32/Auxiliary.lean (order_lt_montgomeryRadix), Dalek32/Scalar/Add.lean,
--   Dalek32/Scalar/MontgomeryReduce.lean
/-- The scalar order fits in 253 bits. -/
theorem order_lt_two_pow_253 : order < 2 ^ 253 := by
  unfold order
  decide

-- Used in: Dalek32/Auxiliary.lean (montgomeryRadix_coprime_order)
/-- The scalar order is coprime to two. -/
theorem two_coprime_order : Nat.Coprime 2 order := by
  unfold order
  decide


/-! ## FieldElement2625 specific theorems (nested into Curve25519Dalek)-/

namespace backend.serial.u32.field.FieldElement2625

-- Used in: Dalek32/Auxiliary.lean (toNat_congr, toNat_expand), Dalek32/Field/AddAssign.lean,
--   Dalek32/Field/Reduce.lean, Dalek32/Field/Zeroize.lean
-- Also applied automatically by the tactics its attributes register it with.
@[simp, scalar_tac_simps, grind =, agrind =]
theorem toNat_eq (x : FieldElement2625) : x.toNat = Array.uScalarToNatField2625 x := rfl

-- Used in: (none)
/-- Two field eLements with pointwise-equal limb values have equal `Nat` representations. -/
theorem toNat_congr (x y : FieldElement2625) (h : ∀ i, i < 10 → x[i]!.val = y[i]!.val) :
    x.toNat = y.toNat := by
  rw [toNat_eq, toNat_eq]; rw [Array.toNatField2625_congr]; exact h


-- Used in: (none)
-- Also applied automatically by the tactics its attributes register it with.
/-- Theorem to unfold `limbRadix` for `scalar_tac` and `agrind`, so that `step` can discharge
preconditions stated with it. It is deliberately not a `simp` lemma, so that `simp` keeps
`limbRadix` folded in hypotheses and goals. -/
@[scalar_tac_simps, agrind =]
theorem limbRadix_eq (i : Nat) : limbRadix i = 2 ^ (26 - i % 2) := rfl


-- Used in: (none)
-- Also applied automatically by the tactics its attributes register it with.
/-- Theorem to unfold `limbWeight` for `scalar_tac` and `agrind`. It is deliberately not a `simp`
lemma, so that `simp` keeps `limbWeight` folded in hypotheses and goals. -/
@[scalar_tac_simps, agrind =]
theorem limbWeight_eq (i : Nat) : limbWeight i = 2 ^ (26 * ((i + 1) / 2) + 25 * (i / 2)) := rfl


-- Used in: Dalek32/Field/ToBytes.lean, Dalek32/Field/reduce/Carry.lean
/-- The weight of the (i+1)-st limb is equal to the weight of the i-th limb multiplied by the i-th
radix. -/
theorem limbWeight_succ (i : Nat) :
    limbWeight (i + 1) = limbRadix i * limbWeight i := by
  unfold limbRadix limbWeight
  rewrite [← Nat.pow_add, Nat.pow_right_inj (by decide)]
  omega


-- Used in: Dalek32/Field/ConditionalAssign.lean, Dalek32/Field/Mul.lean, Dalek32/Field/Negate.lean,
--   Dalek32/Field/SquareInner.lean, Dalek32/Field/SubAssign.lean
open Result Aeneas.Std.WP in
/-- At an in-bounds index, `Array.index_usize` on a field element returns the limb. -/
theorem index_usize_eq (a : FieldElement2625) (j : Usize) (h_j : j.val < 10) :
    Array.index_usize a j = ok a[j.val]! := by
  obtain ⟨x, h_eq, h_x⟩ := spec_imp_exists (Array.index_usize_spec a j (by scalar_tac))
  rw [h_eq, h_x, Array.getElem_val_eq_getElem!]


-- Used in: Dalek32/Field/ConditionalAssign.lean, Dalek32/Field/ConditionalSwap.lean
open Result Aeneas.Std.WP in
/-- At an in-bounds index, `Array.index_mut_usize` on a field element returns the limb and the
`set` back-function. -/
theorem index_mut_usize_eq (a : FieldElement2625) (j : Usize) (h_j : j.val < 10) :
    Array.index_mut_usize a j = ok (a[j.val]!, a.set j) := by
  obtain ⟨⟨x, back⟩, h_eq, h_x, h_back⟩ :=
    spec_imp_exists (Array.index_mut_usize_spec a j (by scalar_tac))
  rw [h_eq, h_x, h_back, Array.getElem_val_eq_getElem!]


-- Used in: Dalek32/Field/Mul.lean, Dalek32/Field/Negate.lean, Dalek32/Field/SquareInner.lean,
--   Dalek32/Field/SubAssign.lean
/-- The value of a field element written out as its ten weighted limbs. -/
theorem toNat_expand (x : FieldElement2625) :
    x.toNat =
      x[0]!.val + 2 ^ 26 * x[1]!.val + 2 ^ 51 * x[2]!.val + 2 ^ 77 * x[3]!.val +
        2 ^ 102 * x[4]!.val + 2 ^ 128 * x[5]!.val + 2 ^ 153 * x[6]!.val +
        2 ^ 179 * x[7]!.val + 2 ^ 204 * x[8]!.val + 2 ^ 230 * x[9]!.val := by
  simp only [toNat_eq, Array.uScalarToNatField2625, limbWeight, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  norm_num


-- Used in: Dalek32/Field/Mul.lean, Dalek32/Field/Negate.lean, Dalek32/Field/SubAssign.lean
/-- The alternating-radix value of a ten-element `Array.make` written out as its weighted
entries. -/
theorem uScalarToNatField2625_make {ty : UScalarTy} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : UScalar ty)
    (hl : [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].length = (10#usize).val) :
    (Array.make 10#usize [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] hl).uScalarToNatField2625 =
      a0.val + 2 ^ 26 * a1.val + 2 ^ 51 * a2.val + 2 ^ 77 * a3.val + 2 ^ 102 * a4.val +
        2 ^ 128 * a5.val + 2 ^ 153 * a6.val + 2 ^ 179 * a7.val + 2 ^ 204 * a8.val +
        2 ^ 230 * a9.val := by
  simp only [Array.uScalarToNatField2625, limbWeight, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  simp [Array.make, Array.getElem!_Nat_eq]


-- Used in: Dalek32/Field/Mul.lean, Dalek32/Field/Negate.lean, Dalek32/Field/SubAssign.lean
/-- A common bound on the ten entries of an `Array.make` bounds every entry; this discharges the
limb precondition of `reduce`. -/
theorem getElem!_make_le {ty : UScalarTy} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : UScalar ty)
    (hl : [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].length = (10#usize).val) (B : Nat)
    (h0 : a0.val ≤ B) (h1 : a1.val ≤ B) (h2 : a2.val ≤ B) (h3 : a3.val ≤ B)
    (h4 : a4.val ≤ B) (h5 : a5.val ≤ B) (h6 : a6.val ≤ B) (h7 : a7.val ≤ B)
    (h8 : a8.val ≤ B) (h9 : a9.val ≤ B) :
    ∀ i < 10, (Array.make 10#usize [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] hl)[i]!.val ≤ B := by
  intro i hi
  rewrite [← Finset.mem_range] at hi
  fin_cases hi <;> simpa [Array.make, Array.getElem!_Nat_eq]

end backend.serial.u32.field.FieldElement2625


/-! ## Scalar29 specific theorems (nested into Curve25519Dalek) -/

namespace backend.serial.u32.scalar.Scalar29

set_option exponentiation.threshold 261 in
-- Used in: (none)
/-- The shared scalar order is below the serial-u32 Montgomery radix. -/
theorem order_lt_montgomeryRadix : order < montgomeryRadix := by
  apply lt_trans Curve25519Dalek.order_lt_two_pow_253
  unfold montgomeryRadix
  decide

set_option exponentiation.threshold 261 in
-- Used in: Dalek32/Auxiliary.lean (cancel_montgomeryRadix)
/-- The serial-u32 Montgomery radix is coprime to the shared scalar order. -/
theorem montgomeryRadix_coprime_order : Nat.Coprime montgomeryRadix order := by
  unfold montgomeryRadix
  exact Nat.Coprime.pow_left 261 Curve25519Dalek.two_coprime_order

-- Used in: (none)
/-- Cancel the Montgomery radix from both sides of a congruence modulo the scalar order. -/
theorem cancel_montgomeryRadix {a b : Nat}
    (h : a * montgomeryRadix ≡ b * montgomeryRadix [MOD order]) :
    a ≡ b [MOD order] := by
  exact Nat.ModEq.cancel_right_of_coprime montgomeryRadix_coprime_order.symm h

set_option exponentiation.threshold 261 in
-- Used in: Dalek32/Scalar/Add.lean, Dalek32/Scalar/MontgomeryReduce.lean, Dalek32/Scalar/Sub.lean
/-- Nine radix-`2^29` limbs represent a value below the Montgomery radix. -/
theorem asNat_bounded (s : Scalar29)
    (hs : ∀ i < 9, s[i]!.val < limbRadix) :
    asNat s < montgomeryRadix := by
  unfold limbRadix at hs
  change (∑ i ∈ Finset.range 9, 2 ^ (29 * i) * s[i]!.val) < 2 ^ 261
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  grind

end backend.serial.u32.scalar.Scalar29

end Curve25519Dalek


/-! ## General theorems-/

-- Used in: Dalek32/Field/ToBytes.lean, Dalek32/Field/from_bytes/Load3At.lean,
--   Dalek32/Field/from_bytes/Load4At.lean
/-- Disjoint `|||` is addition: the low operand fits under the shift.
Analogue of `Nat.two_pow_add_eq_or_of_lt` but with reversed order. -/
theorem Nat.or_two_pow_eq_add_of_lt {a b i : Nat} (h : a < 2 ^ i) :
    a ||| b * 2 ^ i = a + b * 2 ^ i := by
  rw [Nat.lor_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h, Nat.add_comm]


-- Used in: Dalek32/Auxiliary.lean (add_mul_mod_mul_left_of_lt)
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


-- Used in: Dalek32/Field/FromBytes.lean
/-- Adding a low part `m < l` to a multiple of `l` commutes with reduction modulo `l * k` -/
theorem Nat.add_mul_mod_mul_left_of_lt {m n k l : Nat} (hm : m < l) :
    (m + l * n) % (l * k) = m + l * n % (l * k) := by
  simp only [Nat.mul_comm]
  exact Nat.add_mul_mod_mul_right_of_lt hm


-- Used in: Dalek32/Field/ToBytes.lean
theorem Nat.lt_mod_mul_add_mod {a b m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    a % m * n + b % n < m * n := by
  calc
    _ ≤ (m - 1) * n + b % n :=
      by rewrite [Nat.add_le_add_iff_right, Nat.mul_le_mul_right_iff hn]
         apply Nat.le_sub_one_of_lt; exact Nat.mod_lt _ hm
    _ < (m - 1) * n + n :=
      by rewrite [Nat.add_lt_add_iff_left]; exact Nat.mod_lt _ hn
    _ = m * n :=
      by rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (by exact Nat.le_mul_of_pos_left _ hm)]


namespace Finset

-- Used in: Dalek32/Field/FromBytes.lean, Dalek32/Field/reduce/Carry.lean
/-- Sums over a finset agree up to `d` when the summands agree except at a subset whose combined
contribution differs by `d`. -/
theorem sum_eq_sum_add_of_subset {ι M : Type*} [AddCommMonoid M] {s : Finset ι} {f g : ι → M}
    {t : Finset ι} (d : M) (ht : t ⊆ s) (heq : ∀ j ∈ s, j ∉ t → f j = g j)
    (hd : ∑ j ∈ t, f j = (∑ j ∈ t, g j) + d) :
    ∑ j ∈ s, f j = (∑ j ∈ s, g j) + d := by
  classical
  have : ∀ x ∈ s \ t, f x = g x := by
    intro x hx
    exact heq x (by rw [mem_sdiff] at hx; exact hx.1) (by rw [mem_sdiff] at hx; exact hx.2)
  calc
    _ = (∑ j ∈ s \ t, f j) + ∑ j ∈ t, f j := (sum_sdiff (by exact ht)).symm
    _ = (∑ j ∈ s \ t, g j) + ∑ j ∈ t, f j := by rw [sum_congr (rfl) ‹_›]
    _ = (∑ j ∈ s \ t, g j) + (∑ j ∈ t, g j) + d := by rw [hd, ← add_assoc]
    _ = (∑ j ∈ s, g j) + d := by rw [sum_sdiff (by exact ht)]

end Finset

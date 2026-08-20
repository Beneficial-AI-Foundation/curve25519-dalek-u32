import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# General lemmas, candidates for upstreaming to mathlib

-/

namespace Finset

/-*Potential room for generalization is to extend the statement*
  *using an arbitrary subset instead of a pair of points*-/
/-- Sums over a finset agree up to `d` when the summands agree except at two points whose combined
contribution differs by `d`. -/
theorem sum_eq_sum_add_of_two_points {ι M : Type*} [AddCommMonoid M] {s : Finset ι} {f g : ι → M}
    {k l : ι} (d : M) (hk : k ∈ s) (hl : l ∈ s) (hne : k ≠ l)
    (heq : ∀ j ∈ s, j ≠ k → j ≠ l → f j = g j) (hkl : f k + f l = g k + g l + d) :
    ∑ j ∈ s, f j = (∑ j ∈ s, g j) + d := by
  classical
  have : ∀ x ∈ s \ {k, l}, f x = g x := by intro x _; exact heq x (by grind) (by grind) (by grind)
  calc
    _ = (∑ j ∈ s \ {k, l}, f j) + ∑ j ∈ {k, l}, f j := (sum_sdiff (by grind)).symm
    _ = (∑ j ∈ s \ {k, l}, f j) + f k + f l := by grind
    _ = (∑ j ∈ s \ {k, l}, g j) + f k + f l := by congr 2; exact sum_congr (rfl) ‹_›
    _ = (∑ j ∈ s \ {k, l}, g j) + g k + g l + d := by simp [add_assoc, hkl]
    _ = ((∑ j ∈ s \ {k, l}, g j) + ∑ j ∈ {k, l}, g j) + d := by simp [sum_pair hne, add_assoc]
    _ = (∑ j ∈ s, g j) + d := by rw [sum_sdiff (by grind)]

end Finset

/-*Maybe this one is a bit overly specific to be in Mathlib*-/
/-- Moving `a / 2 ^ s` one weight level up (from weight `w` to weight `w + s`)
and keeping `a % 2 ^ s` at weight `w` preserves the value. -/
theorem Nat.carry_step (a b s w : Nat) :
    a % 2 ^ s * 2 ^ w + (b + a / 2 ^ s) * 2 ^ (w + s) = a * 2 ^ w + b * 2 ^ (w + s) := by
  conv_rhs => rw [← Nat.mod_add_div a (2 ^ s)]
  ring

/-*This however may deserve its place there*-/
/-- Adding a low part `a < k` to a multiple of `k` commutes with reduction modulo `j * k` -/
theorem Nat.add_mul_mod_mul_right_of_lt {a b j k : Nat} (ha : a < k) :
    (a + b * k) % (j * k) = a + b * k % (j * k) := by
  by_cases hj : 0 < j
  · have hlt : a + b * k % (j * k) < j * k := by
      rw [Nat.mul_mod_mul_right]
      calc a + b % j * k
          < k + b % j * k := Nat.add_lt_add_right ha _
        _ = (b % j + 1) * k := by ring
        _ ≤ j * k := Nat.mul_le_mul_right _ (Nat.mod_lt b hj)
    have hak : a < j * k := Nat.lt_of_lt_of_le ha (Nat.le_mul_of_pos_left k hj)
    rw [Nat.add_mod, Nat.mod_eq_of_lt hak, Nat.mod_eq_of_lt hlt]
  · simp [Nat.eq_zero_of_not_pos hj]
/-Explanation: truncating the high part leaves it a multiple of `k`, so it never reaches
into the range `a` occupies and the two summands still fit below the modulus.-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# General lemmas, candidates for upstreaming to mathlib

-/

namespace Finset

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

/-- Moving `a / 2^s` one weight level up (from weight `w` to weight `w + s`) and keeping `a % 2^s`
at weight `w` preserves the value. -/
theorem Nat.carry_step (a b s w : Nat) :
    a % 2 ^ s * 2 ^ w + (b + a / 2 ^ s) * 2 ^ (w + s) = a * 2 ^ w + b * 2 ^ (w + s) := by
  conv_rhs => rw [← Nat.mod_add_div a (2 ^ s)]
  ring

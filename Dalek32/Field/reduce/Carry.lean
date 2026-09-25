/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.Field.reduce.LOW25BITS
import Dalek32.Field.reduce.LOW26BITS

/-!
# Spec theorem for `reduce.carry`

`reduce.carry z i` carries limb `i` into limb `i + 1` where `z` is an `Array U64 10#usize` and
`i < 9` is an index. The radix alternates between `2^26` and `2^25`, so limb `i` has weight `2^w`
where `w = 26 - i % 2`. During a carry, the high part `z[i] >>> w` is added to `z[i + 1]` and `z[i]`
is masked to its low `w` bits. All the other limbs remain unchanged.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 343:8-354:9
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP Finset
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625


/-Helper theorem: proves the value preserving property assuming the consequences of a carry step on
the limbs. -/
private theorem carry_preserves_toNat (z z' : Array U64 10#usize) (k : Nat) (hk : k < 9)
    (hmask : z'[k]!.val = z[k]!.val % 2 ^ (26 - k % 2))
    (hcarry : z'[k + 1]!.val = z[k + 1]!.val + z[k]!.val / 2 ^ (26 - k % 2))
    (hrest : ∀ j, j < 10 → j ≠ k → j ≠ k + 1 → z'[j]!.val = z[j]!.val) :
    Array.uScalarToNatField2625 z' = Array.uScalarToNatField2625 z := by
  unfold Array.uScalarToNatField2625
  have hexp : 2 ^ (26 * ((k + 1 + 1) / 2) + 25 * ((k + 1) / 2))
      = 2 ^ (26 - k % 2) * 2 ^ (26 * ((k + 1) / 2) + 25 * (k / 2)) := by
    rewrite [← Nat.pow_add, Nat.pow_right_inj (by decide)]; agrind
  exact sum_eq_sum_add_of_subset (d := 0) (t := {k, k + 1}) (s := range 10)
    (f := fun i => 2 ^ (26 * ((i + 1) / 2) + 25 * (i / 2)) * z'[i]!.val)
    (g := fun i => 2 ^ (26 * ((i + 1) / 2) + 25 * (i / 2)) * z[i]!.val)
    (by simp only [insert_subset_iff, singleton_subset_iff, mem_range]; scalar_tac)
    (by intro j hj1 hj2; rewrite [mem_range] at hj1
        simp only [mem_insert, mem_singleton, not_or] at hj2
        rewrite [Nat.mul_left_cancel_iff (by exact Nat.two_pow_pos _)]
        exact hrest j hj1 hj2.1 hj2.2)
    (by rewrite [sum_pair (by exact Nat.ne_add_one k), sum_pair (by exact Nat.ne_add_one k)]
        rewrite [hmask, hcarry, Nat.left_distrib, Nat.add_comm, hexp]
        simp only [Nat.add_zero]
        conv_rhs => rw [← Nat.div_add_mod' (↑z[k]!) (2 ^ (26 - k % 2))]
        ring)


/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::reduce::carry`
The four postconditions give preservation of the represented value, the masked limb, the carried
limb and invariance of the other eight. The precondition `hover` rules out `u64` overflow in the
carry addition. The represented value is preserved, since limb `i + 1` has weight `2 ^ w` times that
of limb `i`. Therefore when the high part `z[i] >>> w` is added to `z[i + 1]` and `z[i]` is masked
to its low `w` bits the total of them doesn't change. -/
@[step]
theorem reduce.carry_spec (z : Array U64 10#usize) (i : Usize)
    (hi : i.val < 9)
    (hover : z[i.val + 1]!.val + z[i.val]!.val / 2 ^ (26 - i.val % 2) < 2 ^ 64) :
    reduce.carry z i ⦃ (z' : Array U64 10#usize) =>
      --Redundant: it follows from the 3 other postconditions as shown above
      Array.uScalarToNatField2625 z' = Array.uScalarToNatField2625 z ∧
      --Independent postconditions
      z'[i.val]!.val = z[i.val]!.val % 2 ^ (26 - i.val % 2) ∧
      z'[i.val + 1]!.val = z[i.val + 1]!.val + z[i.val]!.val / 2 ^ (26 - i.val % 2) ∧
      (∀ j, j < 10 → j ≠ i.val → j ≠ i.val + 1 → z'[j]!.val = z[j]!.val) ⦄ := by
  unfold reduce.carry
  --Covering the odd and even cases with the same code
  cases Nat.mod_two_eq_zero_or_one i.val
  case inl | inr =>
    step*
    · simp only [*, Nat.shiftRight_eq_div_pow, U64.max_def, U64.numBits_eq]
      simp only [‹↑i % 2 = _›, Array.getElem!_Nat_eq,
        ← List.Inhabited_getElem_eq_getElem! z.val i.val (by scalar_tac),
        ← List.Inhabited_getElem_eq_getElem! z.val (i.val + 1) (by scalar_tac)] at hover
      exact Nat.le_sub_one_of_lt hover
    --Proving the redundant statement from the independent ones
    · refine (and_iff_right_of_imp (fun h => ?_)).mpr ?_
      · obtain ⟨h1, h2, h3⟩ := h
        exact carry_preserves_toNat z z' i.val hi h1 h2 h3
    --Proving the independent postconditions
      split_conjs
      --Masking
      · simp only [*, Array.getElem!_Nat_set_eq (z.set _ _) i i.val _ (by scalar_tac)]
        simp_lists
        rewrite [UScalar.val_and]
        conv => lhs; arg 2; rewrite [← UScalar.bv_toNat]
        simp only [*, Nat.and_two_pow_sub_one_eq_mod]
      --Carrying
      · simp only [*, Array.getElem!_Nat_set_ne (z.set _ _) i (i.val + 1) _ (by scalar_tac),
          Array.getElem!_Nat_set_eq z _ (i.val + 1) _ (by exact ⟨by assumption, by scalar_tac⟩),
          Array.getElem!_Nat_eq,
          ← List.Inhabited_getElem_eq_getElem! z.val i.val (by scalar_tac),
          ← List.Inhabited_getElem_eq_getElem! z.val (i.val + 1) (by scalar_tac)]
        rw [Nat.shiftRight_eq_div_pow]
      --Invariance of the rest
      · intro j hj hji hji1
        simp only [*]; simp_lists


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

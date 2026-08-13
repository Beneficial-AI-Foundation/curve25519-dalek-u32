import translated.Funs
import proofs.backend.serial.u32.field.Limbs
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-!
# Spec and proof of `FieldElement2625::reduce` (u32 backend)

Given raw 64-bit limbs (each ≤ 2^64 - 2^40), `reduce` produces a field element whose limbs
are `< 2^26` and whose value is unchanged modulo `p = 2^255 - 19`.

The function `reduce` splits into three phases:
- interleaved carry pass,
- `×19` fold-in,
- final carry + cast packing.

For the purposes of the proof, we split the function and write specs for each phase.
-/

namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-! ## Spec theorems for the `reduce` constants -/

@[step]
theorem reduce.LOW_26_BITS_spec :
    reduce.LOW_26_BITS ⦃ (result : U64) => result.val = 2 ^ 26 - 1 ⦄ := by
  unfold reduce.LOW_26_BITS; rfl

@[step]
theorem reduce.LOW_25_BITS_spec :
    reduce.LOW_25_BITS ⦃ (result : U64) => result.val = 2 ^ 25 - 1 ⦄ := by
  unfold reduce.LOW_25_BITS; rfl

/-! ## Spec theorem for `reduce::carry` -/

/- The post-`step*` argument of `carry_spec`. -/
private theorem carry_post (z z1 z' : Array U64 10#usize) (i i4 : Usize)
    (i3 i6 i7 i8 i9 : U64) (s : Nat) (hi : i.val < 9)
    (hi4 : i4.val = i.val + 1) (hi3 : i3.val = z[i.val]!.val >>> s)
    (hi6 : i6.val = z[i.val + 1]!.val + i3.val) (hz1 : z1 = z.set i4 i6)
    (hi7 : i7 = z[i.val]!) (hi8 : i8.val = 2 ^ s - 1)
    (hi9 : i9.val = (i7 &&& i8).val) (hz' : z' = z1.set i i9) :
    z'[i.val]!.val < 2 ^ s
    ∧ z'[i.val]!.val = z[i.val]!.val % 2 ^ s
    ∧ (∀ j, j < 10 → j ≠ i.val → j ≠ i.val + 1 → z'[j]!.val = z[j]!.val)
    ∧ z'[i.val + 1]!.val = z[i.val + 1]!.val + z[i.val]!.val / 2 ^ s := by
  have h9 : i9.val = z[i.val]!.val % 2 ^ s := by
    rw [hi9, hi7]
    exact UScalar.val_and_mask _ _ s hi8
  have h9lt : i9.val < 2 ^ s := h9 ▸ Nat.mod_lt _ (by positivity)
  split_conjs
  · -- masked limb is bounded by its width
    simp_lists [hz', h9lt]
  · -- masked limb: z'[i.val]! = z[i.val]! % 2^s
    simp_lists [hz', h9]
  · -- untouched limbs
    intro j hj hji hji1
    simp_lists [hz', hz1, hi4]
  · -- carried-into limb
    simp_lists [hz', hz1, hi4, hi6, hi3, Nat.shiftRight_eq_div_pow]

/-- Spec theorem for `FieldElement2625::reduce::carry`.

Carrying at position `i` masks limb `i` down to its allotted width, moves the overflow into limb
`i + 1`, touches nothing else, and preserves the represented value. -/
@[step]
theorem reduce.carry_spec (z : Array U64 10#usize) (i : Usize) (hi : i.val < 9)
    (hof : z[i.val + 1]!.val + z[i.val]!.val / 2 ^ limbBits i.val < 2 ^ 64) :
    reduce.carry z i ⦃ (z' : Array U64 10#usize) =>
      z'[i.val]!.val < 2 ^ limbBits i.val
      ∧ z'[i.val + 1]!.val = z[i.val + 1]!.val + z[i.val]!.val / 2 ^ limbBits i.val
      ∧ (∀ j, j < 10 → j ≠ i.val → j ≠ i.val + 1 → z'[j]!.val = z[j]!.val)
      ∧ limbsVal z' = limbsVal z ⦄ := by
  unfold reduce.carry
  rcases Nat.mod_two_eq_zero_or_one i.val with hp | hp
  case inl | inr =>
    step*
    case hmax =>
      simp_lists [i5_post, i2_post] at hof
      simp [limbBits, hp] at hof
      simp [Nat.shiftRight_eq_div_pow] at i3_post1
      agrind
    obtain ⟨c0, c1, c2, c3⟩ := carry_post z z1 z' i i4 i3 i6 i7 i8 i9 (limbBits i.val)
      hi i4_post (by simp_lists [i3_post1, i2_post]; simp [limbBits, hp])
      (by simp_lists [i6_post, i5_post, i4_post]) z1_post
      (by simp_lists [i7_post, z1_post, i4_post])
      (by simpa [limbBits, hp] using i8_post) i9_post1 z'_post
    exact ⟨c0, c3, c2, limbsVal_carry z z' i.val hi c1 c3 c2⟩

/- `reduce` splits into three phases:
- interleaved carry pass,
- `×19` fold-in,
- final carry + cast packing. -/

set_option linter.hashCommand false in
#decompose reduce reduce_eq
  letRange 0 10 => reduce_carryChain
  letRange 1 10 => reduce_foldIn
  letRange 3 21 => reduce_castsToFE

/- Any carry out of a `U64` limb is at most `(2^64 - 1) / 2^s`. -/
private theorem div_le_max_div (x : U64) (s : Nat) :
    x.val / 2 ^ s ≤ (2 ^ 64 - 1) / 2 ^ s :=
  Nat.div_le_div_right (by scalar_tac)

/-- Spec theorem for the interleaved carry pass of `reduce` (carry order: 0,4,1,5,2,6,3,7,4,8). -/
@[local step]
theorem reduce_carryChain_spec (z : Array U64 10#usize)
    (hz : ∀ j, j < 10 → z[j]!.val ≤ 2 ^ 64 - 2 ^ 40) :
    reduce_carryChain z ⦃ (z10 : Array U64 10#usize) =>
      (∀ j < 9, z10[j]!.val < 2 ^ 26)
      ∧ z10[1]!.val < 2 ^ 25
      ∧ limbsVal z10 = limbsVal z ⦄ := by
  unfold reduce_carryChain
  step*
  · agrind [hz 3 (by decide), div_le_max_div _ 26]
  · agrind [hz 7 (by decide), div_le_max_div _ 26]
  · agrind [div_le_max_div _ 26]
  · agrind [hz 8 (by decide), div_le_max_div _ 26]
  · agrind [div_le_max_div _ 26]
  · agrind [hz 9 (by decide), div_le_max_div _ 26]
  · split_conjs
    · intro j hj
      rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j
      · simp (disch := decide) only [*]; agrind
      · simp (disch := decide) only [*]; agrind
      · simp (disch := decide) only [*]; agrind
      · simp (disch := decide) only [*]; agrind
      · simp (disch := decide) only [*]; agrind
      · simp (disch := decide) only [*]
        agrind [hz 3 (by decide), div_le_max_div _ 25, div_le_max_div _ 26]
      · simp (disch := decide) only [*]; agrind
      · simp (disch := decide) only [*]; agrind
      · agrind
      · exact absurd hj (by agrind)
    · simp (disch := decide) only [*]; agrind
    · simp only [*]

/- Postcondition assembly for `reduce_foldIn_spec`. -/
private theorem foldIn_post (z z11 z' : Array U64 10#usize) (i4 i7 : U64)
    (hi4 : i4.val = z[0]!.val + 19 * (z[9]!.val / 2 ^ 25)) (hi7 : i7.val = z[9]!.val % 2 ^ 25)
    (hz11 : z11 = z.set 0#usize i4) (hz' : z' = z11.set 9#usize i7) :
    z'[0]!.val = z[0]!.val + 19 * (z[9]!.val / 2 ^ 25)
    ∧ z'[9]!.val < 2 ^ 25
    ∧ (∀ j, j < 10 → j ≠ 0 → j ≠ 9 → z'[j]!.val = z[j]!.val)
    ∧ limbsVal z' ≡ limbsVal z [ZMOD p] := by
  have h0 : z'[0]!.val = z[0]!.val + 19 * (z[9]!.val / 2 ^ 25) := by
    simp_lists [hz', hz11, hi4]
  have h9 : z'[9]!.val = z[9]!.val % 2 ^ 25 := by simp_lists [hz', hi7]
  have hrest : ∀ j, j < 10 → j ≠ 0 → j ≠ 9 → z'[j]!.val = z[j]!.val := by
    intro j hj hj0 hj9
    simp_lists [hz', hz11]
  refine ⟨h0, h9 ▸ Nat.mod_lt _ (by positivity), hrest, ?_⟩
  sorry
  -- rw [limbsVal_foldin z z' h0 h9 hrest, Nat.add_mul_mod_self_right]

/-- Spec theorem for the `×19` fold-in phase of `reduce`. -/
@[local step]
theorem reduce_foldIn_spec (z : Array U64 10#usize)
    (hof : z[0]!.val + 19 * (z[9]!.val / 2 ^ 25) < 2 ^ 64) :
    reduce_foldIn z ⦃ (z' : Array U64 10#usize) =>
      z'[0]!.val = z[0]!.val + 19 * (z[9]!.val / 2 ^ 25)
      ∧ z'[9]!.val < 2 ^ 25
      ∧ (∀ j, j < 10 → j ≠ 0 → j ≠ 9 → z'[j]!.val = z[j]!.val)
      ∧ limbsVal z' ≡ limbsVal z [ZMOD p] ⦄ := by
  unfold reduce_foldIn
  step*
  case hmax =>
    -- `19 · (z[9] >>> 25)` fits a U64 unconditionally: the quotient is < 2^39
    have h1 : i1.val ≤ (2 ^ 64 - 1) / 2 ^ 25 := by
      rw [i1_post1, Nat.shiftRight_eq_div_pow]
      exact div_le_max_div i 25
    simp only [U64.max_eq]
    agrind
  case hmax =>
    -- `z[0] + 19·(z[9]/2^25)` fits a U64: exactly the `hof` hypothesis
    have h2 : i2.val = 19 * (z[9]!.val / 2 ^ 25) := by
      simp [i2_post, i1_post1, i_post, Nat.shiftRight_eq_div_pow]
    have h3 : i3.val = z[0]!.val := by simp [i3_post]
    simp only [U64.max_eq]
    agrind
  have hi4 : i4.val = z[0]!.val + 19 * (z[9]!.val / 2 ^ 25) := by
    simp [i4_post, i3_post, i2_post, i1_post1, i_post, Nat.shiftRight_eq_div_pow]
  have hi7 : i7.val = z[9]!.val % 2 ^ 25 := by
    have e5 : i5 = z[9]! := by simp_lists [i5_post, z11_post]
    rw [i7_post1, e5]
    exact UScalar.val_and_mask _ _ 25 i6_post
  exact foldIn_post z z11 z' i4 i7 hi4 hi7 z11_post z'_post

/-- Spec theorem for the cast phase of `reduce`. -/
theorem reduce_castsToFE_spec' (z : Array U64 10#usize)
    (hbounds : ∀ j, j < 10 → z[j]!.val < 2 ^ 32) :
    reduce_castsToFE z ⦃ (result : FieldElement2625) =>
      (∀ j, j < 10 → result[j]!.val = z[j]!.val) ⦄ := by
  unfold reduce_castsToFE
  step*
  intro j hj
  simp only [Array.make, Array.getElem!_Nat_eq, *]
  interval_cases j
  · simpa using hbounds 0 (by grind)
  · simpa using hbounds 1 (by grind)
  · simpa using hbounds 2 (by grind)
  · simpa using hbounds 3 (by grind)
  · simpa using hbounds 4 (by grind)
  · simpa using hbounds 5 (by grind)
  · simpa using hbounds 6 (by grind)
  · simpa using hbounds 7 (by grind)
  · simpa using hbounds 8 (by grind)
  · simpa using hbounds 9 (by grind)

/-- Spec theorem for the cast phase of `reduce` with extra postcondition. -/
@[local step]
theorem reduce_castsToFE_spec (z : Array U64 10#usize)
    (hbounds : ∀ j, j < 10 → z[j]!.val < 2 ^ 32) :
    reduce_castsToFE z ⦃ (result : FieldElement2625) =>
      (∀ j, j < 10 → result[j]!.val = z[j]!.val) ∧ result.val = limbsVal z ⦄ := by
  have := reduce_castsToFE_spec'
  step*
  exact ⟨‹_›, limbsVal_congr ‹_›⟩

/-! ## Spec theorem for `reduce` -/

/- TODO: in `reduce_spec`, most likely the precondition `z[j]!.val ≤ 2 ^ 63` (rather than
`≤ 2 ^ 64 - 2 ^ 40`) would suffice for all the uses of this function. -/

/-- Spec theorem for `FieldElement2625::reduce`.

Given limbs `≤ 2^64 - 2^40`, `reduce` returns limbs which are `< 2^26` and represent the same value
mod `p`. -/
@[step]
theorem reduce_spec (z : Array U64 10#usize) (hz : ∀ j, j < 10 → z[j]!.val ≤ 2 ^ 64 - 2 ^ 40) :
    reduce z ⦃ (result : FieldElement2625) =>
      (∀ j, j < 10 → result[j]!.val < 2 ^ 26) ∧ result.val ≡ limbsVal z [ZMOD p] ⦄ := by
  rw [reduce_eq]
  step*

end curve25519_dalek.backend.serial.u32.field.FieldElement2625

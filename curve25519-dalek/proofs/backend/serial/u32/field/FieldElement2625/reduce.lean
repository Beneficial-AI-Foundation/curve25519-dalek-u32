import translated.Funs
import proofs.backend.serial.u32.field.Limbs

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
    (hover : z[i.val + 1]!.val + z[i.val]!.val / 2 ^ limbBits i.val < 2 ^ 64) :
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
      simp_lists [i5_post, i2_post] at hover
      simp [limbBits, hp] at hover
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

/- A masked limb plus an incoming carry quotient stays within its 26-bit budget. -/
private theorem mask_add_quotient_lt (a b : ℕ) (ha : a < 2 ^ 25) (hb : b < 2 ^ 44) :
    a + b / 2 ^ 26 < 2 ^ 26 := by
  have hq : b / 2 ^ 26 < 2 ^ 18 := Nat.div_lt_of_lt_mul (by agrind)
  agrind

/-- Spec theorem for the interleaved carry pass of `reduce` (carry order: 0,4,1,5,2,6,3,7,4,8). -/
@[local step]
theorem reduce_carryChain_spec (z : Array U64 10#usize)
    (hz : ∀ j, j < 10 → z[j]!.val ≤ 2 ^ 64 - 2 ^ 40) :
    reduce_carryChain z ⦃ (z10 : Array U64 10#usize) =>
      (∀ j, j < 9 → z10[j]!.val < 2 ^ 26)
      ∧ z10[1]!.val < 2 ^ 25
      ∧ limbsVal z10 = limbsVal z ⦄ := by
  unfold reduce_carryChain
  step as ⟨z1, hb1, hc1, hu1, hs1⟩
  step as ⟨z2, hb2, hc2, hu2, hs2⟩
  step as ⟨z3, hb3, hc3, hu3, hs3⟩
  step as ⟨z4, hb4, hc4, hu4, hs4⟩
  step as ⟨z5, hb5, hc5, hu5, hs5⟩
  case hover =>
    change z4[3]!.val + z4[2]!.val / 2 ^ 26 < 2 ^ 64
    simp (disch := decide) only [hu4, hu3, hu2, hu1]
    have := hz 3 (by decide)
    have := div_le_max_div z3[2]! 26
    agrind
  step as ⟨z6, hb6, hc6, hu6, hs6⟩
  case hover =>
    change z5[7]!.val + z5[6]!.val / 2 ^ 26 < 2 ^ 64
    simp (disch := decide) only [hu5, hu4, hu3, hu2, hu1]
    have := hz 7 (by decide)
    have := div_le_max_div z4[6]! 26
    agrind
  step as ⟨z7, hb7, hc7, hu7, hs7⟩
  case hover =>
    -- limb 4 was masked by carry(4) at step 2 and untouched since
    change z6[4]!.val + z6[3]!.val / 2 ^ 25 < 2 ^ 64
    have b4 : z6[4]!.val < 2 ^ 26 := by
      simp (disch := decide) only [hu6, hu5, hu4, hu3]
      exact hb2
    have := div_le_max_div z6[3]! 25
    agrind
  step as ⟨z8, hb8, hc8, hu8, hs8⟩
  case hover =>
    change z7[8]!.val + z7[7]!.val / 2 ^ 25 < 2 ^ 64
    simp (disch := decide) only [hu7, hu6, hu5, hu4, hu3, hu2, hu1]
    have := hz 8 (by decide)
    have := div_le_max_div z6[7]! 25
    agrind
  step as ⟨z9, hb9, hc9, hu9, hs9⟩
  case hover =>
    -- limb 5 was masked by carry(5) at step 4 and untouched since
    change z8[5]!.val + z8[4]!.val / 2 ^ 26 < 2 ^ 64
    have b5 : z8[5]!.val < 2 ^ 25 := by
      simp (disch := decide) only [hu8, hu7, hu6, hu5]
      exact hb4
    have := div_le_max_div z8[4]! 26
    agrind
  step as ⟨z10, hb10, hc10, hu10, hs10⟩
  case hover =>
    change z9[9]!.val + z9[8]!.val / 2 ^ 26 < 2 ^ 64
    simp (disch := decide) only [hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1]
    have := hz 9 (by decide)
    have := div_le_max_div z8[8]! 26
    agrind
  split_conjs
  · /- Each limb reads back through the unchanged-chains to its masking step; limb 5 was re-carried
    into at step 9, so its value is a 25-bit mask plus a tiny quotient of an almost-masked limb. -/
    intro j hj
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j
    · simp (disch := decide) only [hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2]
      exact hb1
    · simp (disch := decide) only [hu10, hu9, hu8, hu7, hu6, hu5, hu4]
      have hb3' : z3[1]!.val < 2 ^ 25 := hb3
      agrind
    · simp (disch := decide) only [hu10, hu9, hu8, hu7, hu6]
      exact hb5
    · simp (disch := decide) only [hu10, hu9, hu8]
      have hb7' : z7[3]!.val < 2 ^ 25 := hb7
      agrind
    · simp (disch := decide) only [hu10]
      exact hb9
    · -- limb 5 = 25-bit mask (step 4) + the carry out of limb 4 (step 9)
      rw [hu10 5 (by decide) (by decide) (by decide)]
      have hc9' : z9[5]!.val = z8[5]!.val + z8[4]!.val / 2 ^ 26 := hc9
      rw [hc9']
      have b5 : z8[5]!.val < 2 ^ 25 := by
        simp (disch := decide) only [hu8, hu7, hu6, hu5]
        exact hb4
      have b4 : z8[4]!.val < 2 ^ 44 := by
        rw [hu8 4 (by decide) (by decide) (by decide)]
        have hc7' : z7[4]!.val = z6[4]!.val + z6[3]!.val / 2 ^ 25 := hc7
        rw [hc7']
        have b4' : z6[4]!.val < 2 ^ 26 := by
          simp (disch := decide) only [hu6, hu5, hu4, hu3]
          exact hb2
        have := div_le_max_div z6[3]! 25
        agrind
      exact mask_add_quotient_lt _ _ b5 b4
    · simp (disch := decide) only [hu10, hu9, hu8, hu7]
      exact hb6
    · -- limb 7 = 25-bit mask (step 8), untouched after
      simp (disch := decide) only [hu10, hu9]
      have hb8' : z8[7]!.val < 2 ^ 25 := hb8
      agrind
    · exact hb10
    · exact absurd hj (by scalar_tac)
  · -- limb 1's tight 25-bit mask survives from step 3 untouched
    simp (disch := decide) only [hu10, hu9, hu8, hu7, hu6, hu5, hu4]
    exact hb3
  · -- every carry preserved the value exactly, so the pass telescopes
    rw [hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]

/- Postcondition assembly for `reduce_foldIn_spec`. -/
private theorem foldIn_post (z z11 z' : Array U64 10#usize) (i4 i7 : U64)
    (hi4 : i4.val = z[0]!.val + 19 * (z[9]!.val / 2 ^ 25)) (hi7 : i7.val = z[9]!.val % 2 ^ 25)
    (hz11 : z11 = z.set 0#usize i4) (hz' : z' = z11.set 9#usize i7) :
    z'[0]!.val = z[0]!.val + 19 * (z[9]!.val / 2 ^ 25)
    ∧ z'[9]!.val < 2 ^ 25
    ∧ (∀ j, j < 10 → j ≠ 0 → j ≠ 9 → z'[j]!.val = z[j]!.val)
    ∧ limbsVal z' % p = limbsVal z % p := by
  have h0 : z'[0]!.val = z[0]!.val + 19 * (z[9]!.val / 2 ^ 25) := by
    simp_lists [hz', hz11, hi4]
  have h9 : z'[9]!.val = z[9]!.val % 2 ^ 25 := by simp_lists [hz', hi7]
  have hrest : ∀ j, j < 10 → j ≠ 0 → j ≠ 9 → z'[j]!.val = z[j]!.val := by
    intro j hj hj0 hj9
    simp_lists [hz', hz11]
  exact ⟨h0, h9 ▸ Nat.mod_lt _ (by positivity), hrest,
    by rw [limbsVal_foldin z z' h0 h9 hrest, Nat.add_mul_mod_self_right]⟩

/-- Spec theorem for the `×19` fold-in phase of `reduce`. -/
@[local step]
theorem reduce_foldIn_spec (z : Array U64 10#usize)
    (hover : z[0]!.val + 19 * (z[9]!.val / 2 ^ 25) < 2 ^ 64) :
    reduce_foldIn z ⦃ (z' : Array U64 10#usize) =>
      z'[0]!.val = z[0]!.val + 19 * (z[9]!.val / 2 ^ 25)
      ∧ z'[9]!.val < 2 ^ 25
      ∧ (∀ j, j < 10 → j ≠ 0 → j ≠ 9 → z'[j]!.val = z[j]!.val)
      ∧ limbsVal z' % p = limbsVal z % p ⦄ := by
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
    -- `z[0] + 19·(z[9]/2^25)` fits a U64: exactly the `hover` hypothesis
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
@[local step]
theorem reduce_castsToFE_spec (z : Array U64 10#usize)
    (hbounds : ∀ j, j < 10 → z[j]!.val < 2 ^ 32) :
    reduce_castsToFE z ⦃ (result : FieldElement2625) =>
      (∀ j, j < 10 → result[j]!.val = z[j]!.val)
      ∧ result.val = limbsVal z ⦄ := by
  unfold reduce_castsToFE
  step*
  have hFE : Array.make 10#usize [i9, i11, i13, i15, i17, i19, i21, i23, i25, i27]
      = ArrayU64_to_FE z := by
    apply Subtype.ext
    simp only [i9_post, i8_post, i11_post, i10_post, i13_post, i12_post, i15_post,
      i14_post, i17_post, i16_post, i19_post, i18_post, i21_post, i20_post, i23_post,
      i22_post, i25_post, i24_post, i27_post, i26_post, ArrayU64_to_FE,
      Aeneas.Std.Array.val_map, Array.make]
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp at h1
        scalar_tac
  rw [hFE]
  constructor
  · intro j hj
    rw [ArrayU64_to_FE_getElem! z j hj]
    exact Nat.mod_eq_of_lt (hbounds j hj)
  · exact ArrayU64_to_FE_val z hbounds

/-! ## Spec theorem for `reduce` -/

/-- Spec theorem for `FieldElement2625::reduce`.

Given limbs `≤ 2^64 - 2^40`, `reduce` returns limbs `< 2^26` representing the same value mod `p`. -/
@[step]
theorem reduce_spec (z : Array U64 10#usize) (hz : ∀ j, j < 10 → z[j]!.val ≤ 2 ^ 64 - 2 ^ 40) :
    reduce z ⦃ (result : FieldElement2625) =>
      (∀ j, j < 10 → result[j]!.val < 2 ^ 26) ∧ result.val % p = limbsVal z % p ⦄ := by
  rw [reduce_eq]
  step*

end curve25519_dalek.backend.serial.u32.field.FieldElement2625

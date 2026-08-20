import translated.Funs
open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# ######################################-/
/-*Spec theorem for `from_bytes.load4_at`*-/
/-# ######################################-/

/-Same concept as `from_bytes.load3_at` just takes an additional byte.-/

/- Disjoint `|||` is addition: the low operand fits under the shift.
Core's `Nat.two_pow_add_eq_or_of_lt` states this as `2 ^ k * b + a`; the goals
coming out of `step*` have the shifted factor on the right. -/
private theorem lor_mul_two_pow {a b k : Nat} (h : a < 2 ^ k) :
    a ||| b * 2 ^ k = a + b * 2 ^ k := by
  rw [Nat.lor_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h, Nat.add_comm, Nat.mul_comm]


/-Pre: `i.val + 4 ≤ b.length` is the only precondition: it covers the three
`index_usize` bounds, and the two `Usize` additions follow from it via
`b.length ≤ Usize.max`. The shifts need nothing, since Aeneas' shift spec
only requires the shift amount to be below the bit width.
 Post: the main statement is that 4 consecutive 8-bit numbers multiplied by
 2 ^ (8 * i), i = 0, 1, 2, 3 and then added, represent the same number as the same bits
 stacked into a 32-bit representation.
 Even though it is redundant, a uniform bound on this representation is worth
 stating here as it will be useful later.-/
@[step]
theorem from_bytes.load4_at_spec (b : Slice U8) (i : Usize)
    (hi : i.val + 4 ≤ b.length) :
    from_bytes.load4_at b i ⦃ (r : U64) =>
      r.val = b[i.val]!.val + 2 ^ 8 * b[i.val + 1]!.val +
      2 ^ 16 * b[i.val + 2]! + 2 ^ 24 * b[i.val + 3]!.val
      /- Redundant: it follows from the other conjunct. -/
      ∧ r.val < 2 ^ 32 ⦄ := by
  unfold from_bytes.load4_at
  step*
  /- Bridge the checked indexing of the `step*` hypotheses to the `!` of the goal. -/
  simp only [i3_post, i8_post, i13_post] at i4_post i9_post i14_post
  simp_lists
  rw [← i1_post, ← i4_post, ← i9_post, ← i14_post]
  /- Casts are exact and the shifts stay well below `2 ^ 64`, so both `%` vanish. -/
  simp only [UScalar.val_or, i12_post1, i16_post1, i7_post1, i6_post1,
    i11_post1, i2_post, i5_post, i10_post, i15_post,
    U8.cast_U64_val_eq, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by scalar_tac : i4.val * 2 ^ 8 < U64.size),
    Nat.mod_eq_of_lt (by scalar_tac : i9.val * 2 ^ 16 < U64.size),
    Nat.mod_eq_of_lt (by scalar_tac : i14.val * 2 ^ 24 < U64.size)]
  /- Innermost `|||` first: the explicit `a` stops `rw` matching the outer one. -/
  rw [lor_mul_two_pow (a := i1.val) (by scalar_tac),
     lor_mul_two_pow (a := i1.val + i4.val * 2^8) (by scalar_tac), lor_mul_two_pow (by scalar_tac)]
  split_conjs
  · scalar_tac
  · scalar_tac


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

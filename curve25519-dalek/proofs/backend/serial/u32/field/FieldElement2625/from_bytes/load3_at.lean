import translated.Funs
open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# ######################################-/
/-*Spec theorem for `from_bytes.load3_at`*-/
/-# ######################################-/

/-def backend.serial.u32.field.FieldElement2625.from_bytes.load3_at
  *b is a List Std.U8 with length ≤ 2^64, 0 ≤ i ≤ 2^64*
  (b : Slice Std.U8) (i : Std.Usize) : Result Std.U64 := do
  let i1 ← Slice.index_usize b i *=b[i]?*
  let i2 ← lift (UScalar.cast .U64 i1) *b[i]? with padding 0s to get a U64*
  let i3 ← i + 1#usize
  let i4 ← Slice.index_usize b i3 *=b[i+1]?*
  let i5 ← lift (UScalar.cast .U64 i4) *b[i+1]? with padding 0s to get a U64*
  let i6 ← i5 <<< 8#i32 *bit shift to the left by 8, i.e. 2^8 · b[i+1]? as U64*
  let i7 ← lift (i2 ||| i6) *bitwise OR of b[i]? and 2^8 · b[i+1]?,*
  *since b[i] < 2^8 this equals b[i]? + 2^8 · b[i+1]?*
  let i8 ← i + 2#usize
  let i9 ← Slice.index_usize b i8 *b[i+2]?*
  let i10 ← lift (UScalar.cast .U64 i9) *b[i+2]? with padding 0s to get a U64*
  let i11 ← i10 <<< 16#i32 *bit shift to the left by 16, i.e. 2^16 · b[i+2]?*
  ok (i7 ||| i11) *bitwise OR of (b[i]? + 2^8 · b[i+1]?) and 2^16 · b[i+2]?,*
  *which equals b[i]? + 2^8 · b[i+1]? + 2^16 · b[i+2]?*
-/

/- Disjoint `|||` is addition: the low operand fits under the shift.
Core's `Nat.two_pow_add_eq_or_of_lt` states this as `2 ^ k * b + a`; the goals
coming out of `step*` have the shifted factor on the right. -/
private theorem lor_mul_two_pow {a b k : Nat} (h : a < 2 ^ k) :
    a ||| b * 2 ^ k = a + b * 2 ^ k := by
  rw [Nat.lor_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h, Nat.add_comm, Nat.mul_comm]


/-Pre: `i.val + 3 ≤ b.length` is the only precondition. It covers the three
`index_usize` bounds, and the two `Usize` additions follow from it via
`b.length ≤ Usize.max`. The shifts need nothing, since Aeneas' shift spec
only requires the shift amount to be below the bit width.
 Post: the main statement is that 3 consecutive 8-bit numbers multiplied by
 2 ^ (8 * i), i = 0, 1, 2 and then added up, represent the same number as the same bits
 stacked into a 24-bit representation.
 Even though it is redundant, a uniform bound on this representation is worth
 stating here as it will be useful later.-/
@[step]
theorem from_bytes.load3_at_spec (b : Slice U8) (i : Usize)
    (hi : i.val + 3 ≤ b.length) :
    from_bytes.load3_at b i ⦃ (r : U64) =>
      r.val = b[i.val]!.val + 2 ^ 8 * b[i.val + 1]!.val + 2 ^ 16 * b[i.val + 2]!.val
      /- Redundant: it follows from the other conjunct. -/
      ∧ r.val < 2 ^ 24 ⦄ := by
  unfold from_bytes.load3_at
  step*
  /- Bridge the checked indexing of the `step*` hypotheses to the `!` of the goal. -/
  simp only [i3_post, i8_post] at i4_post i9_post
  simp_lists
  rw [← i1_post, ← i4_post, ← i9_post]
  /- Casts are exact and the shifts stay well below `2 ^ 64`, so both `%` vanish. -/
  simp only [UScalar.val_or, i7_post1, i6_post1, i11_post1, i2_post, i5_post, i10_post,
    U8.cast_U64_val_eq, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by scalar_tac : i4.val * 2 ^ 8 < U64.size),
    Nat.mod_eq_of_lt (by scalar_tac : i9.val * 2 ^ 16 < U64.size)]
  /- Innermost `|||` first: the explicit `a` stops `rw` matching the outer one. -/
  rw [lor_mul_two_pow (a := i1.val) (by scalar_tac), lor_mul_two_pow (by scalar_tac)]
  split_conjs
  · scalar_tac
  · scalar_tac

end curve25519_dalek.backend.serial.u32.field.FieldElement2625

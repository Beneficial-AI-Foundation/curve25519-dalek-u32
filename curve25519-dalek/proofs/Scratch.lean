import translated.Funs
open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-Set the value of the prime that gives the order of the field.-/
def p := 2^255 - 19

/-Helper theorem to avoid resolving p in decimal format.-/
@[simp]
theorem p_in_decimal :
(p = 57896044618658097711785492504343953926634992332820282019728792003956564819949) := by rfl

axiom p_prime : Nat.Prime p

namespace curve25519_dalek
namespace backend.serial.u32.field
#check FieldElement2625
--Array Std.U32 10#usize

/- A `FieldElement2625` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// In the 32-bit implementation, a `FieldElement` is represented in
/// radix \\(2\^{25.5}\\) as ten `u32`s. This means that a field
/// element \\(x\\) is represented as
/// $$
/// x = \sum\_{i=0}\^9 x\_i 2\^{\lceil i \frac {51} 2 \rceil}
///   = x\_0 + x\_1 2\^{26} + x\_2 2\^{51} + x\_3 2\^{77} + \cdots + x\_9 2\^{230};
/// $$
/// the coefficients are alternately bounded by \\(2\^{25}\\) and
/// \\(2\^{26}\\). The limbs are allowed to grow between reductions up
/// to \\(2\^{25+b}\\) or \\(2\^{26+b}\\), where \\(b = 1.75\\).
-/

/-Define a function that maps from backend.serial.u32.field.FieldElement2625 to Nat.
Uses `!`-indexing rather than checked `x[0]`: the specs below must index at
*symbolic* positions (e.g. `z[i.val]!` in `reduce.carry_spec`, where `i` is
only known to satisfy `i.val < 9`), and checked indexing there would put proof
terms inside theorem type signatures. Aeneas normalises toward `getElem!` for
the same reason, so keeping this function in `!` form lets `simp_lists`
connect it to the specs without per-position bridge lemmas. -/
def FieldElement2625_to_Nat (x : FieldElement2625) : Nat :=
  x[0]!.val
  + x[1]!.val * 2^26
  + x[2]!.val * 2^(26 + 25)
  + x[3]!.val * 2^(26 + 25 + 26)
  + x[4]!.val * 2^(26 + 25 + 26 + 25)
  + x[5]!.val * 2^(26 + 25 + 26 + 25 + 26)
  + x[6]!.val * 2^(26 + 25 + 26 + 25 + 26 + 25)
  + x[7]!.val * 2^(26 + 25 + 26 + 25 + 26 + 25 + 26)
  + x[8]!.val * 2^(26 + 25 + 26 + 25 + 26 + 25 + 26 + 25)
  + x[9]!.val * 2^(26 + 25 + 26 + 25 + 26 + 25 + 26 + 25 + 26)

end backend.serial.u32.field

#check WP.spec --funny brackets in the proof are syntactic sugar for this.
#check Result


namespace backend.serial.u32.field.FieldElement2625

/-# #################################################-/
/-*Spec theorems for `LOW_26_BITS` and `LOW_25_BITS`*-/
/-# #################################################-/

@[step]
theorem LOW_26_BITS_spec :
    reduce.LOW_26_BITS ⦃ (result : U64) => result.bv.toNat = 2^26-1 ⦄ := by
  unfold reduce.LOW_26_BITS
  rfl

@[step]
theorem LOW_25_BITS_spec :
    reduce.LOW_25_BITS ⦃ (result : U64) => result.bv.toNat = 2^25-1 ⦄ := by
  unfold reduce.LOW_25_BITS
  rfl


/-# ############################-/
/-*Spec theorem for `MINUS_ONE`*-/
/-# ############################-/

@[step]
theorem MINUS_ONE_spec :
    MINUS_ONE ⦃ (result : FieldElement2625) => FieldElement2625_to_Nat result = p - 1 ⦄ := by
  unfold MINUS_ONE from_limbs
  step*
  unfold FieldElement2625_to_Nat Array.make
  simp [p_in_decimal]


/-Playing around with `reduce.carry`-/

/-67108869 = 2^26+5-/
#eval reduce.carry (Array.make 10#usize [
      67108869#u64, 0#u64, 0#u64, 0#u64, 0#u64, 0#u64, 0#u64, 0#u64, 0#u64, 0#u64
      ]) (0#usize)

/-The function takes an array of 10, 64-bit limbs and an index which is at
most 8 for the reasonable cases (otherwise it throws an error).
Then it takes the limb corresponding to the index and if it exceeds the
allotted width for that limb then it takes the overflow to the next index and
reduces the limb down to its proper width.
Limbs with even idices have allotted width 26, while with odd indices have allotted width 25.-/

/-def backend.serial.u32.field.FieldElement2625.reduce.carry
  (z : Array Std.U64 10#usize) (i : Std.Usize) :  *arguments*
  Result (Array Std.U64 10#usize) *return type*
  := do
  massert (i < 9#usize) *checks if index is at most 8, if not throws error*
  let i1 ← i % 2#usize  *takes i mod 2 to split cases for different radix*
  if i1 = 0#usize
  then  *Even index case*
    let i2 ← Array.index_usize z i *takes the i-th term from input array*
    let i3 ← i2 >>> 26#i32  *int(i-th term/(2^26)) or (right shift by 26 bits)*
    let i4 ← i + 1#usize  *increases the index by 1*
    let i5 ← Array.index_usize z i4 *takes the (i+1)-st term of z*
    let i6 ← i5 + i3  *adds up the (i+1)-st term and int(i-th term/(2^26))*
    let z1 ← Array.update z i4 i6 *updates the (i+1)-st term to the sum*
    let i7 ← Array.index_usize z1 i *takes the i-th term of the new array*
    let i8 ← backend.serial.u32.field.FieldElement2625.reduce.LOW_26_BITS *2^26-1*
    let i9 ← lift (i7 &&& i8) *bitwise AND of the i-th term and 2^26-1, i.e.*
    *(i-th term) mod 2^26*
    Array.update z1 i i9 *updates the i-th term to the bitwise AND result*
  else  *Odd index case*  `same as above except for the 2 differences noted`
    let i2 ← Array.index_usize z
    let i3 ← i2 >>> 25#i32  *int(i-th term/(2^25)) or (right shift by 25 bits)*
    let i4 ← i + 1#usize
    let i5 ← Array.index_usize z i4
    let i6 ← i5 + i3  *adds up the (i+1)-st term and int(i-th term/(2^25))*
    let z1 ← Array.update z i4 i6
    let i7 ← Array.index_usize z1 i
    let i8 ← backend.serial.u32.field.FieldElement2625.reduce.LOW_25_BITS *2^25-1*
    let i9 ← lift (i7 &&& i8) *bitwise AND of the i-th term and 2^25-1, i.e.*
    *(i-th term) mod 2^25*
    Array.update z1 i i9-/

/-# ###############################-/
/-*Spec theorem for `reduce.carry`*-/
/-# ###############################-/

/- Nat representation of a raw 10-limb `U64` array using the alternating 26/25-bit radixes-/
def ArrayU64_to_Nat (z : Array U64 10#usize) : Nat :=
  z[0]!.val
  + z[1]!.val * 2^26
  + z[2]!.val * 2^(26 + 25)
  + z[3]!.val * 2^(26 + 25 + 26)
  + z[4]!.val * 2^(26 + 25 + 26 + 25)
  + z[5]!.val * 2^(26 + 25 + 26 + 25 + 26)
  + z[6]!.val * 2^(26 + 25 + 26 + 25 + 26 + 25)
  + z[7]!.val * 2^(26 + 25 + 26 + 25 + 26 + 25 + 26)
  + z[8]!.val * 2^(26 + 25 + 26 + 25 + 26 + 25 + 26 + 25)
  + z[9]!.val * 2^(26 + 25 + 26 + 25 + 26 + 25 + 26 + 25 + 26)

/- Conjunct-3 helper for `carry_spec`: the Nat-repr equality at a touched
   position `k`, covering both parities via the same `if k % 2 = 0 then 26
   else 25` shift `carry_spec`'s own postcondition uses.

   A case split on `k` is needed because `ArrayU64_to_Nat` is a flat sum of 10
   named terms, so relating the symbolic `z[k]!` to one of them requires
   knowing `k`. Keeping the split in this lemma means it is written once and
   both parity branches of `carry_spec` just call it.

   `hmd` is hoisted out of the split so every branch is the same one-liner:
   `simp` rewrites the three touched/untouched limb facts (with `decide`
   discharging the `j ≠ k, k+1` side conditions — cheaper than `scalar_tac`
   since `k`,`j` are concrete literals per branch), then `agrind` finishes
   using `hmd` to recombine `z[k]! % 2^s` with `z[k]! / 2^s`. -/
private theorem carry_sum_pos (z z' : Array U64 10#usize) (k : Nat) (hk : k < 9)
    (hmasked : z'[k]!.val = z[k]!.val % 2 ^ (if k % 2 = 0 then 26 else 25))
    (hcarry : z'[k + 1]!.val = z[k + 1]!.val + z[k]!.val / 2 ^ (if k % 2 = 0 then 26 else 25))
    (hunchanged : ∀ j, j < 10 → j ≠ k → j ≠ k + 1 → z'[j]!.val = z[j]!.val) :
    ArrayU64_to_Nat z' = ArrayU64_to_Nat z := by
  have hmd : ∀ a m : Nat, a % m + m * (a / m) = a := Nat.mod_add_div
  unfold ArrayU64_to_Nat
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · simp (disch := decide) only [hmasked, hcarry, hunchanged]; agrind
  · simp (disch := decide) only [hmasked, hcarry, hunchanged]; agrind
  · simp (disch := decide) only [hmasked, hcarry, hunchanged]; agrind
  · simp (disch := decide) only [hmasked, hcarry, hunchanged]; agrind
  · simp (disch := decide) only [hmasked, hcarry, hunchanged]; agrind
  · simp (disch := decide) only [hmasked, hcarry, hunchanged]; agrind
  · simp (disch := decide) only [hmasked, hcarry, hunchanged]; agrind
  · simp (disch := decide) only [hmasked, hcarry, hunchanged]; agrind
  · simp (disch := decide) only [hmasked, hcarry, hunchanged]; agrind
  · exact absurd hk (by scalar_tac)

/- *Alternative to `carry_sum_pos`, proving the same statement without the
   9-way case split on `k`.* Not currently used by `carry_spec` — kept as the
   case-free option, since its length is independent of the limb count whereas
   `carry_sum_pos` grows a branch per position.

   The trade: this route needs a weight function plus a bridge lemma to an
   indexed sum (below), which at 10 limbs costs more lines than the 9
   one-liners it replaces. `ArrayU64_to_Nat` itself is untouched — the bridge
   is a lemma, not a redefinition, so the flat form stays usable elsewhere. -/

/- Weight exponent of limb `j`: 0, 26, 51, 77, 102, 128, 153, 179, 204, 230 —
   i.e. the exponents appearing in `ArrayU64_to_Nat`, in closed form. -/
private def limbWeight (j : Nat) : Nat := 26 * ((j + 1) / 2) + 25 * (j / 2)

/- Consecutive weights differ by exactly the shift `carry` applies at `k`. This
   is the one fact that makes the carry value-preserving, and the only place a
   parity split is still needed (2 cases about the weights, not 9 about positions). -/
private theorem limbWeight_succ (k : Nat) :
    limbWeight (k + 1) = limbWeight k + (if k % 2 = 0 then 26 else 25) := by
  unfold limbWeight
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by scalar_tac⟩
    simp only [h, if_pos]; agrind
  · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by scalar_tac⟩
    simp only [h]; norm_num; agrind

/- Bridge: the flat 10-term sum viewed as an indexed sum over `limbWeight`. -/
private theorem ArrayU64_to_Nat_eq_sum (z : Array U64 10#usize) :
    ArrayU64_to_Nat z = ∑ j ∈ Finset.range 10, z[j]!.val * 2 ^ limbWeight j := by
  simp [ArrayU64_to_Nat, Finset.sum_range_succ, limbWeight]

/- Split `range 10` into the touched pair `{k, k+1}` and its complement:
   `hunchanged` handles the complement termwise, and on the pair the shift
   identity `limbWeight_succ` plus `Nat.mod_add_div` recombine
   `z[k]! % 2^s` with `z[k]! / 2^s` back into `z[k]!`. -/
private theorem carry_sum_pos_generic (z z' : Array U64 10#usize) (k : Nat) (hk : k < 9)
    (hmasked : z'[k]!.val = z[k]!.val % 2 ^ (if k % 2 = 0 then 26 else 25))
    (hcarry : z'[k + 1]!.val = z[k + 1]!.val + z[k]!.val / 2 ^ (if k % 2 = 0 then 26 else 25))
    (hunchanged : ∀ j, j < 10 → j ≠ k → j ≠ k + 1 → z'[j]!.val = z[j]!.val) :
    ArrayU64_to_Nat z' = ArrayU64_to_Nat z := by
  have hne : k ≠ k + 1 := by scalar_tac
  have hsub : ({k, k + 1} : Finset Nat) ⊆ Finset.range 10 := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_range]
    agrind
  rw [ArrayU64_to_Nat_eq_sum, ArrayU64_to_Nat_eq_sum,
      ← Finset.sum_sdiff hsub, ← Finset.sum_sdiff hsub,
      Finset.sum_congr rfl (fun j hj => by
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton] at hj
        rw [hunchanged j hj.1 (by agrind) (by agrind)]),
      Finset.sum_pair hne, Finset.sum_pair hne, hmasked, hcarry, limbWeight_succ, pow_add]
  have := Nat.mod_add_div z[k]!.val (2 ^ (if k % 2 = 0 then 26 else 25))
  ring_nf
  agrind



@[step]
theorem reduce.carry_spec (z : Array U64 10#usize) (i : Usize)
    (hi : i.val < 9)
    (hover : z[i.val + 1]!.val + z[i.val]!.val / 2 ^ (if i.val % 2 = 0 then 26 else 25) < 2 ^ 64) :
    reduce.carry z i ⦃ (z' : Array U64 10#usize) =>
      let shift := if i.val % 2 = 0 then 26 else 25
      z'[i.val]!.val = z[i.val]!.val % 2^shift
      /- Redundant: it follows from the other 3 conjuncts. -/
      ∧ z'[i.val + 1]!.val = z[i.val + 1]!.val + z[i.val]!.val / 2^shift
      ∧ (∀ j, j < 10 → j ≠ i.val → j ≠ i.val + 1 → z'[j]!.val = z[j]!.val)
      ∧ ArrayU64_to_Nat z' = ArrayU64_to_Nat z ⦄ := by
  unfold reduce.carry
  /- The two parity branches of `reduce.carry` differ only in the shift width
  and the mask constant, so the entire post-`step*` argument is proven once
  here, generic in the shift `s`.
     Conjunct 1 is the masking step: `i9 = i7 &&& i8` with `i8` the low-`s`-bit
     mask, so `Nat.and_two_pow_sub_one_eq_mod` turns the bitwise AND into `%
     2^s` directly — no `bv_tac` and no concrete mask literal, which is what
     lets this be shift-generic. Conjuncts 2 and 3 are the two `set`s read
     back off the untouched and the carried-into positions. -/
  have key : ∀ (z1 z' : Array U64 10#usize) (i4 : Usize) (i3 i6 i7 i8 i9 : U64) (s : Nat),
      i4.val = i.val + 1 → i3.val = z[i.val]!.val >>> s →
      i6.val = z[i.val + 1]!.val + i3.val → z1 = z.set i4 i6 →
      i7 = z[i.val]! → i8.bv.toNat = 2 ^ s - 1 → i9.val = (i7 &&& i8).val →
      z' = z1.set i i9 →
      z'[i.val]!.val = z[i.val]!.val % 2 ^ s
      ∧ (∀ j, j < 10 → j ≠ i.val → j ≠ i.val + 1 → z'[j]!.val = z[j]!.val)
      ∧ z'[i.val + 1]!.val = z[i.val + 1]!.val + z[i.val]!.val / 2 ^ s := by
    intro z1 z' i4 i3 i6 i7 i8 i9 s hi4 hi3 hi6 hz1 hi7 hi8 hi9 hz'
    have h9 : i9.val = z[i.val]!.val % 2 ^ s := by
      rw [hi9, hi7, UScalar.val_and, show i8.val = 2 ^ s - 1 from hi8,
        Nat.and_two_pow_sub_one_eq_mod]
    split_conjs
    · -- conjunct 1: masked value, z'[i.val]! = z[i.val]! % 2^s
      simp_lists [hz', h9]
    · -- conjunct 2: unchanged elsewhere, z'[j]! = z[j]! for j ∉ {i.val, i.val + 1}
      intro j hj hji hji1
      simp_lists [hz', hz1, hi4]
    · -- conjunct 3 input: the carried-into limb z'[i.val + 1]!
      simp_lists [hz', hz1, hi4, hi6, hi3, Nat.shiftRight_eq_div_pow]
  /- Both parity branches are discharged by this single block. Two things make
  it parity-agnostic:
  `key` is applied at the shift `if i.val % 2 = 0 then 26 else 25`
  itself (rather than at 26 / 25), so its conclusion already matches both the
  goal and `carry_sum_pos` with no conversion; and every parity-specific step
  reduces that `if` with `simp [hp]`, which resolves it in either direction
  from `hp` alone. Note `simp only [hp]` will not do — it rewrites `i.val % 2`
  to `0`/`1` but leaves the `if` standing, so full `simp` is needed for the
  decision step.
  The `simp_lists` calls must run before `simp [hp]`: the latter normalises
  `z[j]!` into `getD` form and powers into numerals, which no longer match the
  `*_post` hypotheses. -/
  rcases Nat.mod_two_eq_zero_or_one i.val with hp | hp
  case inl | inr =>
    step*
    case hmax =>
      simp_lists [i5_post, i2_post] at hover
      simp [hp] at hover
      simp [Nat.shiftRight_eq_div_pow] at i3_post1
      agrind
    obtain ⟨c1, c2, c3⟩ := key z1 z' i4 i3 i6 i7 i8 i9 (if i.val % 2 = 0 then 26 else 25)
      i4_post (by simp_lists [i3_post1, i2_post]; simp [hp])
      (by simp_lists [i6_post, i5_post, i4_post]) z1_post
      (by simp_lists [i7_post, z1_post, i4_post]) (by simpa [hp] using i8_post)
      i9_post1 z'_post
    exact ⟨c1, c3, c2, carry_sum_pos z z' i.val hi c1 c3 c2⟩


/-# #########################-/
/-*Spec theorem for `reduce`*-/
/-# #########################-/

/- The pointwise `U64 → U32` conversion that `reduce` ends with. Note the cast is the
   *wrapping* one (`UScalar.cast_val_eq : (cast tgt x).val = x.val % 2^tgt.numBits`), so
   it only preserves values on limbs below `2^32` — hence the hypothesis on
   `ArrayU64_to_FE_val` below. -/
def ArrayU64_to_FE (z : Array U64 10#usize) : FieldElement2625 :=
  Array.make 10#usize
    [UScalar.cast .U32 z[0]!, UScalar.cast .U32 z[1]!, UScalar.cast .U32 z[2]!,
     UScalar.cast .U32 z[3]!, UScalar.cast .U32 z[4]!, UScalar.cast .U32 z[5]!,
     UScalar.cast .U32 z[6]!, UScalar.cast .U32 z[7]!, UScalar.cast .U32 z[8]!,
     UScalar.cast .U32 z[9]!]

/- Both lemmas are stated per-limb rather than as whole-array identities: that keeps them
   in `!` form, matching the specs, and gives conjunct 1 the bound version and conjunct 2
   the value version directly. The `simpa using h j …` is load-bearing — unfolding
   `Array.make` leaves the goal in *checked* `(↑z)[j]` form while `h` is in `!` form, and
   `simpa` normalises both to meet. -/
/- `linter.flexible` would have us replace `simp [ArrayU64_to_FE]` with a pinned
   `simp only [...]`. We deliberately don't: the explicit list runs to eight lemmas,
   several of them internal Aeneas names (`UScalar.ofNatCore_val_eq`,
   `List.Vector.length_val`), which per `aeneas-lean-core` ("avoid large `simp only`
   calls in implementation proofs") is *more* exposed to model churn than plain `simp`,
   not less. The trailing `simpa using h` also re-normalises, so the coupling the
   linter guards against is already loose here. -/
set_option linter.flexible false in
theorem ArrayU64_to_FE_lt (z : Array U64 10#usize) (n j : Nat) (hj : j < 10)
    (h : z[j]!.val < 2 ^ n) : (ArrayU64_to_FE z)[j]!.val < 2 ^ n := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · simp [ArrayU64_to_FE]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by simpa using h)
  · exact absurd hj (by scalar_tac)

set_option linter.flexible false in
theorem ArrayU64_to_FE_val (z : Array U64 10#usize) (j : Nat) (hj : j < 10)
    (h : z[j]!.val < 2 ^ 32) : (ArrayU64_to_FE z)[j]!.val = z[j]!.val := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · simp [ArrayU64_to_FE]; exact Nat.mod_eq_of_lt (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.mod_eq_of_lt (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.mod_eq_of_lt (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.mod_eq_of_lt (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.mod_eq_of_lt (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.mod_eq_of_lt (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.mod_eq_of_lt (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.mod_eq_of_lt (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.mod_eq_of_lt (by simpa using h)
  · simp [ArrayU64_to_FE]; exact Nat.mod_eq_of_lt (by simpa using h)
  · exact absurd hj (by scalar_tac)

/- Postcondition of `reduce`, as a *pure* lemma — no monadic block, no `⦃ ⦄`.

   Splitting here rather than at `z10` is what keeps this monad-free: `reduce_spec` does
   all the stepping itself (which is affordable — `step*` handled the whole tail including
   the ten casts), and only the reasoning moves out. What blew the budget inline was never
   `step*` but proving these two conjuncts, so this is the cut that matters.

   Every hypothesis is a fact `step*` hands over for free: `hL`/`hL1` bound `z10`'s limbs
   (limb 9 is deliberately unbounded — it is still raw, which is what the `×19` fold-in
   is for), `hsum` is the chain's value preservation, `hz11`/`hz12`/`hi4`/`hi7` describe
   the fold-in, and `h13*` are `carry_spec`'s four conjuncts at the final `carry 0`. -/
private theorem reduce_post (z z10 z11 z12 z13 : Array U64 10#usize) (i4 i7 : U64)
    (hL : ∀ j, j < 9 → z10[j]!.val < 2 ^ 26)
    (hL1 : z10[1]!.val < 2 ^ 25)
    (hsum : ArrayU64_to_Nat z10 = ArrayU64_to_Nat z)
    (hz11 : z11 = z10.set 0#usize i4) (hz12 : z12 = z11.set 9#usize i7)
    (hi4 : i4.val = z10[0]!.val + 19 * (z10[9]!.val / 2 ^ 25))
    (hi7 : i7.val = z10[9]!.val % 2 ^ 25)
    (h13m : z13[0]!.val = z12[0]!.val % 2 ^ 26)
    (h13c : z13[1]!.val = z12[1]!.val + z12[0]!.val / 2 ^ 26)
    (h13u : ∀ j, j < 10 → j ≠ 0 → j ≠ 1 → z13[j]!.val = z12[j]!.val)
    (h13s : ArrayU64_to_Nat z13 = ArrayU64_to_Nat z12) :
    (∀ j, j < 10 → (ArrayU64_to_FE z13)[j]!.val < 2 ^ 26)
    ∧ FieldElement2625_to_Nat (ArrayU64_to_FE z13) % p = ArrayU64_to_Nat z % p := by
  /- `z12` reads off the fold-in: limb 0 became `i4`, limb 9 became `i7`, rest unchanged. -/
  have e0 : z12[0]!.val = i4.val := by simp_lists [hz12, hz11]
  have e9 : z12[9]!.val = i7.val := by simp_lists [hz12]
  have ej : ∀ j, j < 10 → j ≠ 0 → j ≠ 9 → z12[j]!.val = z10[j]!.val := by
    intro j hj h0 h9; simp_lists [hz12, hz11]
  /- Output limb bounds. Limb 1 is the only interesting one: it takes the fold-in carry
     `(z10[0]! + 19·c)/2^26 < 2^18` on top of its 25-bit mask, so `hL1`'s tight bound is
     what keeps the total under `2^26`. -/
  have hb13 : ∀ j, j < 10 → z13[j]!.val < 2 ^ 26 := by
    intro j hj
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
    · rw [h13m]; exact Nat.mod_lt _ (by decide)
    · rw [h13c, ej 1 (by decide) (by decide) (by decide), e0, hi4]
      have hc : z10[9]!.val / 2 ^ 25 ≤ (2 ^ 64 - 1) / 2 ^ 25 :=
        Nat.div_le_div_right (by scalar_tac)
      have h0' := hL 0 (by decide)
      agrind
    · rw [h13u 2 (by decide) (by decide) (by decide), ej 2 (by decide) (by decide) (by decide)]
      exact hL 2 (by decide)
    · rw [h13u 3 (by decide) (by decide) (by decide), ej 3 (by decide) (by decide) (by decide)]
      exact hL 3 (by decide)
    · rw [h13u 4 (by decide) (by decide) (by decide), ej 4 (by decide) (by decide) (by decide)]
      exact hL 4 (by decide)
    · rw [h13u 5 (by decide) (by decide) (by decide), ej 5 (by decide) (by decide) (by decide)]
      exact hL 5 (by decide)
    · rw [h13u 6 (by decide) (by decide) (by decide), ej 6 (by decide) (by decide) (by decide)]
      exact hL 6 (by decide)
    · rw [h13u 7 (by decide) (by decide) (by decide), ej 7 (by decide) (by decide) (by decide)]
      exact hL 7 (by decide)
    · rw [h13u 8 (by decide) (by decide) (by decide), ej 8 (by decide) (by decide) (by decide)]
      exact hL 8 (by decide)
    · rw [h13u 9 (by decide) (by decide) (by decide), e9, hi7]
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    · exact absurd hj (by scalar_tac)
  have hb32 : ∀ j, j < 10 → z13[j]!.val < 2 ^ 32 := fun j hj =>
    Nat.lt_trans (hb13 j hj) (by decide)
  /- The casts preserve every limb, so the converted array carries the same value. -/
  have hFEsum : FieldElement2625_to_Nat (ArrayU64_to_FE z13) = ArrayU64_to_Nat z13 := by
    unfold FieldElement2625_to_Nat ArrayU64_to_Nat
    rw [ArrayU64_to_FE_val z13 0 (by decide) (hb32 0 (by decide)),
      ArrayU64_to_FE_val z13 1 (by decide) (hb32 1 (by decide)),
      ArrayU64_to_FE_val z13 2 (by decide) (hb32 2 (by decide)),
      ArrayU64_to_FE_val z13 3 (by decide) (hb32 3 (by decide)),
      ArrayU64_to_FE_val z13 4 (by decide) (hb32 4 (by decide)),
      ArrayU64_to_FE_val z13 5 (by decide) (hb32 5 (by decide)),
      ArrayU64_to_FE_val z13 6 (by decide) (hb32 6 (by decide)),
      ArrayU64_to_FE_val z13 7 (by decide) (hb32 7 (by decide)),
      ArrayU64_to_FE_val z13 8 (by decide) (hb32 8 (by decide)),
      ArrayU64_to_FE_val z13 9 (by decide) (hb32 9 (by decide))]
  /- The heart of it: the fold-in drops `c·2^255` off limb 9 and adds `19·c` at limb 0,
     and since `2^255 = p + 19` that is a change of exactly `c·p`. Stated as an addition
     (not a subtraction) so it stays inside `Nat`. -/
  have hkey : ArrayU64_to_Nat z10 = ArrayU64_to_Nat z12 + (z10[9]!.val / 2 ^ 25) * p := by
    unfold ArrayU64_to_Nat
    rw [e0, e9, ej 1 (by decide) (by decide) (by decide),
      ej 2 (by decide) (by decide) (by decide), ej 3 (by decide) (by decide) (by decide),
      ej 4 (by decide) (by decide) (by decide), ej 5 (by decide) (by decide) (by decide),
      ej 6 (by decide) (by decide) (by decide), ej 7 (by decide) (by decide) (by decide),
      ej 8 (by decide) (by decide) (by decide), hi4, hi7]
    have := Nat.mod_add_div z10[9]!.val (2 ^ 25)
    simp only [p_in_decimal]
    agrind
  refine ⟨fun j hj => ArrayU64_to_FE_lt z13 26 j hj (hb13 j hj), ?_⟩
  rw [hFEsum, h13s, ← hsum, hkey, Nat.add_mul_mod_self_right]

/- Monadic tail of `reduce`. The long `do` block is forced: after `reduce_spec`'s ten
   carries the goal *is* this term, and it is not defeq to `ok …` (every `index_usize`,
   the `19 *`, the `+` and the final `carry` are fallible), so the statement has to
   mirror the code for `reduce_spec`'s `exact` to typecheck.

   This layer exists purely for the budget: `reduce_spec` cannot afford both the carry
   chain and this stepping in one declaration (measured — restoring the tail there times
   out). All the *reasoning* still lives in the monad-free `reduce_post`; this proof only
   steps through the code and repackages `step*`'s opaque `i` variables for it. -/
private theorem reduce_tail (z z10 : Array U64 10#usize)
    (hL : ∀ j, j < 9 → z10[j]!.val < 2 ^ 26)
    (hL1 : z10[1]!.val < 2 ^ 25)
    (hsum : ArrayU64_to_Nat z10 = ArrayU64_to_Nat z) :
    (do
      let i ← z10.index_usize 9#usize
      let i1 ← i >>> 25#i32
      let i2 ← 19#u64 * i1
      let i3 ← z10.index_usize 0#usize
      let i4 ← i3 + i2
      let z11 ← z10.update 0#usize i4
      let i5 ← z11.index_usize 9#usize
      let i6 ← reduce.LOW_25_BITS
      let i7 ← lift (i5 &&& i6)
      let z12 ← z11.update 9#usize i7
      let z13 ← reduce.carry z12 0#usize
      let i8 ← z13.index_usize 0#usize
      let i9 ← lift (UScalar.cast UScalarTy.U32 i8)
      let i10 ← z13.index_usize 1#usize
      let i11 ← lift (UScalar.cast UScalarTy.U32 i10)
      let i12 ← z13.index_usize 2#usize
      let i13 ← lift (UScalar.cast UScalarTy.U32 i12)
      let i14 ← z13.index_usize 3#usize
      let i15 ← lift (UScalar.cast UScalarTy.U32 i14)
      let i16 ← z13.index_usize 4#usize
      let i17 ← lift (UScalar.cast UScalarTy.U32 i16)
      let i18 ← z13.index_usize 5#usize
      let i19 ← lift (UScalar.cast UScalarTy.U32 i18)
      let i20 ← z13.index_usize 6#usize
      let i21 ← lift (UScalar.cast UScalarTy.U32 i20)
      let i22 ← z13.index_usize 7#usize
      let i23 ← lift (UScalar.cast UScalarTy.U32 i22)
      let i24 ← z13.index_usize 8#usize
      let i25 ← lift (UScalar.cast UScalarTy.U32 i24)
      let i26 ← z13.index_usize 9#usize
      let i27 ← lift (UScalar.cast UScalarTy.U32 i26)
      ok (Array.make 10#usize [i9, i11, i13, i15, i17, i19, i21, i23, i25, i27]))
    ⦃ (result : FieldElement2625) =>
      (∀ j, j < 10 → result[j]!.val < 2 ^ 26)
      ∧ FieldElement2625_to_Nat result % p = ArrayU64_to_Nat z % p ⦄ := by
  have dbound : ∀ (x : U64) (s : Nat), x.val / 2 ^ s ≤ (2 ^ 64 - 1) / 2 ^ s :=
    fun x s => Nat.div_le_div_right (by scalar_tac)
  have b0 : z10[0]!.val < 2 ^ 26 := hL 0 (by decide)
  step*
  case hmax =>
    -- `19 · (z10[9]! >>> 25) ≤ 19 · 2^39` fits a U64
    have h1 : i1.val ≤ (2 ^ 64 - 1) / 2 ^ 25 := by
      rw [i1_post1, Nat.shiftRight_eq_div_pow]; exact dbound i 25
    simp only [U64.max_eq]
    agrind
  case hmax =>
    -- `z10[0]! + 19·(z10[9]! >>> 25) < 2^26 + 19·2^39` fits a U64 with room to spare
    have h1 : i1.val ≤ (2 ^ 64 - 1) / 2 ^ 25 := by
      rw [i1_post1, Nat.shiftRight_eq_div_pow]; exact dbound i 25
    have h3 : i3.val < 2 ^ 26 := by simpa [i3_post] using b0
    simp only [U64.max_eq]
    agrind
  case hover =>
    -- the final carry(0): limb 1 still carries its step-3 mask, limb 0 is the fold-in
    change z12[1]!.val + z12[0]!.val / 2 ^ 26 < 2 ^ 64
    have e1 : z12[1]!.val = z10[1]!.val := by simp_lists [z12_post, z11_post]
    have := dbound z12[0]! 26
    agrind
  /- Repackage the fold-in values and identify the cast block with `ArrayU64_to_FE`,
     then hand everything to the pure lemma. -/
  have hi4' : i4.val = z10[0]!.val + 19 * (z10[9]!.val / 2 ^ 25) := by
    simp [i4_post, i2_post, i1_post1, Nat.shiftRight_eq_div_pow, i_post, i3_post]
  have hi7' : i7.val = z10[9]!.val % 2 ^ 25 := by
    -- same trick as `carry_spec`'s masking step: AND with a low-bit mask *is* `% 2^n`
    have e5 : i5 = z10[9]! := by simp_lists [i5_post, z11_post]
    rw [i7_post1, e5, UScalar.val_and, show i6.val = 2 ^ 25 - 1 from i6_post,
      Nat.and_two_pow_sub_one_eq_mod]
  have hFE : Array.make 10#usize [i9, i11, i13, i15, i17, i19, i21, i23, i25, i27]
      = ArrayU64_to_FE z13 := by
    simp [ArrayU64_to_FE, i9_post, i8_post, i11_post, i10_post, i13_post, i12_post,
      i15_post, i14_post, i17_post, i16_post, i19_post, i18_post, i21_post, i20_post,
      i23_post, i22_post, i25_post, i24_post, i27_post, i26_post]
  rw [hFE]
  exact reduce_post z z10 z11 z12 z13 i4 i7 hL hL1 hsum z11_post z12_post hi4' hi7'
    (by simpa using z13_post1) (by simpa using z13_post2) z13_post3 z13_post4

/- `2^40` of headroom below `2^64` on every input limb. This is the "one carry of
   headroom" condition: the largest carry arriving at any limb during the chain is
   `z >>> 25 < 2^39`, and `2^40` is the clean power-of-two margin above that.
   Measured to be the right scale — `reduce` succeeds on all limbs `= 2^64-2^39-1`
   but overflows on `2^64-2^38-1`. It admits every caller; the tightest is
   `square2`, whose limbs reach `2·(77·2^55.5 + 190·2^53.5) ≈ 2^63.46`. -/
theorem reduce_spec (z : Array U64 10#usize)
    (hz : ∀ j, j < 10 → z[j]!.val ≤ 2 ^ 64 - 2 ^ 40) :
    reduce z ⦃ (result : FieldElement2625) =>
      (∀ j, j < 10 → result[j]!.val < 2^26)
      ∧ FieldElement2625_to_Nat result % p = ArrayU64_to_Nat z % p ⦄ := by
  unfold reduce
  /- Every limb is a `U64`, so any carry out of it is at most `(2^64-1)/2^s`.
     `agrind` cannot bound a division of an otherwise-unconstrained limb, so each
     `hover` below feeds it this fact for the source limb. -/
  have dbound : ∀ (x : U64) (s : Nat), x.val / 2 ^ s ≤ (2 ^ 64 - 1) / 2 ^ s :=
    fun x s => Nat.div_le_div_right (by scalar_tac)
  /- Each `hover` states `zPrev[i+1]! + zPrev[i]!/2^shift < 2^64` but indexes at
     `↑i#usize + 1` rather than a literal, so it starts with `change` to put it in
     literal form (defeq). The receiving limb `i+1` then needs a real bound: either
     it is still raw, and a chain of `hu`s carries it back to `hz`, or it was already
     masked, and the chain ends at the relevant `hm`. `agrind` manages the chain
     unaided up to ~3 links, which is why steps 1-4 need nothing here. -/
  step as ⟨z1, hm1, hc1, hu1, hs1⟩
  step as ⟨z2, hm2, hc2, hu2, hs2⟩
  step as ⟨z3, hm3, hc3, hu3, hs3⟩
  step as ⟨z4, hm4, hc4, hu4, hs4⟩
  step as ⟨z5, hm5, hc5, hu5, hs5⟩
  case hover =>
    change z4[3]!.val + z4[2]!.val / 2 ^ 26 < 2 ^ 64
    simp (disch := decide) only [hu4, hu3, hu2, hu1]
    have := hz 3 (by decide)
    have := dbound z3[2]! 26
    agrind
  step as ⟨z6, hm6, hc6, hu6, hs6⟩
  case hover =>
    change z5[7]!.val + z5[6]!.val / 2 ^ 26 < 2 ^ 64
    simp (disch := decide) only [hu5, hu4, hu3, hu2, hu1]
    have := hz 7 (by decide)
    have := dbound z4[6]! 26
    agrind
  step as ⟨z7, hm7, hc7, hu7, hs7⟩
  case hover =>
    -- limb 4 was masked by carry(4) at step 2 and untouched since
    change z6[4]!.val + z6[3]!.val / 2 ^ 25 < 2 ^ 64
    have b4 : z6[4]!.val < 2 ^ 26 := by
      simp (disch := decide) only [hu6, hu5, hu4, hu3, hm2]
      exact Nat.mod_lt _ (by decide)
    have := dbound z6[3]! 25
    agrind
  step as ⟨z8, hm8, hc8, hu8, hs8⟩
  case hover =>
    change z7[8]!.val + z7[7]!.val / 2 ^ 25 < 2 ^ 64
    simp (disch := decide) only [hu7, hu6, hu5, hu4, hu3, hu2, hu1]
    have := hz 8 (by decide)
    have := dbound z6[7]! 25
    agrind
  step as ⟨z9, hm9, hc9, hu9, hs9⟩
  case hover =>
    -- limb 5 was masked by carry(5) at step 4 and untouched since
    change z8[5]!.val + z8[4]!.val / 2 ^ 26 < 2 ^ 64
    have b5 : z8[5]!.val < 2 ^ 25 := by
      simp (disch := decide) only [hu8, hu7, hu6, hu5, hm4]
      exact Nat.mod_lt _ (by decide)
    have := dbound z8[4]! 26
    agrind
  step as ⟨z10, hm10, hc10, hu10, hs10⟩
  case hover =>
    change z9[9]!.val + z9[8]!.val / 2 ^ 26 < 2 ^ 64
    simp (disch := decide) only [hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1]
    have := hz 9 (by decide)
    have := dbound z8[8]! 26
    agrind
  /- After the chain every limb of `z10` has been masked (or received only a tiny
     carry) except limb 9, which is still raw — which is exactly why the `×19`
     fold-in below exists. So the whole limb-bound table collapses to one `∀`, and
     `simp only [*]` normalises each limb back to its masking point uniformly. -/
  have hL : ∀ j, j < 9 → z10[j]!.val < 2 ^ 26 := by
    intro j hj
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j
    · simp (disch := decide) only [*]; agrind
    · simp (disch := decide) only [*]; agrind
    · simp (disch := decide) only [*]; agrind
    · simp (disch := decide) only [*]; agrind
    · simp (disch := decide) only [*]; agrind
    · simp (disch := decide) only [*]; agrind
    · simp (disch := decide) only [*]; agrind
    · simp (disch := decide) only [*]; agrind
    · simp (disch := decide) only [*]; agrind
    · exact absurd hj (by scalar_tac)
  /- Limb 1's tight 25-bit mask: `hL`'s uniform `2^26` is not enough, because the final
     carry folds the `×19` carry into limb 1 and `2^26 + anything` would overshoot. -/
  have hL1 : z10[1]!.val < 2 ^ 25 := by
    simp (disch := decide) only [hu10, hu9, hu8, hu7, hu6, hu5, hu4, hm3]
    exact Nat.mod_lt _ (by decide)
  /- Every carry preserved the value exactly, so the whole chain telescopes. -/
  have hsum : ArrayU64_to_Nat z10 = ArrayU64_to_Nat z := by
    rw [hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
  exact reduce_tail z z10 hL hL1 hsum

end backend.serial.u32.field.FieldElement2625
end curve25519_dalek

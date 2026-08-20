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

/-# #############################-/
/-*Spec theorem for `from_limbs`*-/
/-# #############################-/

theorem from_limbs_spec (l : Array Std.U32 10#usize) :
    from_limbs l ⦃ (result : Array Std.U32 10#usize) => result = l ⦄ := by
  unfold from_limbs
  rfl

/-# ###############################################################-/
/-*Spec theorems for `LOW_23_BITS`,`LOW_26_BITS` and `LOW_25_BITS`*-/
/-# ###############################################################-/

@[step]
theorem from_bytes.LOW_23_BITS_spec :
    from_bytes.LOW_23_BITS ⦃ (result : U64) => result.bv.toNat = 2^23-1 ⦄ := by
  unfold from_bytes.LOW_23_BITS
  rfl

@[step]
theorem to_bytes.LOW_26_BITS_spec :
    to_bytes.LOW_26_BITS ⦃ (result : U32) => result.bv.toNat = 2^26-1 ⦄ := by
  unfold to_bytes.LOW_26_BITS
  rfl

@[step]
theorem to_bytes.LOW_25_BITS_spec :
    to_bytes.LOW_25_BITS ⦃ (result : U32) => result.bv.toNat = 2^25-1 ⦄ := by
  unfold to_bytes.LOW_25_BITS
  rfl

@[step]
theorem reduce.LOW_26_BITS_spec :
    reduce.LOW_26_BITS ⦃ (result : U64) => result.bv.toNat = 2^26-1 ⦄ := by
  unfold reduce.LOW_26_BITS
  rfl

@[step]
theorem reduce.LOW_25_BITS_spec :
    reduce.LOW_25_BITS ⦃ (result : U64) => result.bv.toNat = 2^25-1 ⦄ := by
  unfold reduce.LOW_25_BITS
  rfl


/-# ###############################################-/
/-*Spec theorems for `ZERO`, `ONE` and `MINUS_ONE`*-/
/-# ###############################################-/

@[step]
theorem ZERO_spec :
    ZERO ⦃ (result : FieldElement2625) => FieldElement2625_to_Nat result = 0 ⦄ := by
  unfold ZERO from_limbs
  step*
  unfold Array.repeat FieldElement2625_to_Nat
  rfl

@[step]
theorem ONE_spec :
    ONE ⦃ (result : FieldElement2625) => FieldElement2625_to_Nat result = 1 ⦄ := by
  unfold ONE from_limbs
  step*
  unfold Array.make FieldElement2625_to_Nat
  rfl

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
@[step]
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
  *since b[i] < 2^8 this is practically b[i]? + 2^8 · b[i+1]?*
  let i8 ← i + 2#usize
  let i9 ← Slice.index_usize b i8 *b[i+2]?*
  let i10 ← lift (UScalar.cast .U64 i9) *b[i+2]? with padding 0s to get a U64*
  let i11 ← i10 <<< 16#i32 *bit shift to the left by 16, i.e. 2^16 · b[i+2]?*
  ok (i7 ||| i11) *bitwise OR of (b[i]? + 2^8 · b[i+1]?) and 2^16 · b[i+2]?,*
  *practically b[i]? + 2^8 · b[i+1]? + 2^16 · b[i+2]?*
-/

/- Disjoint `|||` is addition: the low operand fits under the shift.
Core's `Nat.two_pow_add_eq_or_of_lt` states this as `2^k * b + a`; the goals
coming out of `step*` have the shifted factor on the right. -/
private theorem lor_mul_two_pow {a b k : Nat} (h : a < 2 ^ k) :
    a ||| b * 2 ^ k = a + b * 2 ^ k := by
  rw [Nat.lor_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h, Nat.add_comm, Nat.mul_comm]

/-Pre: `i.val + 3 ≤ b.length` is the only precondition: it covers the three
`index_usize` bounds, and the two `Usize` additions follow from it via
`b.length ≤ Usize.max`. The shifts need nothing, since Aeneas' shift spec
only requires the shift amount to be below the bit width.
 Post: the main statement is that 3 consecutive 8-bit numbers multiplied by
 2^(8*i), i=0,1,2 and then added, represent the same number as the same bits
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
  /- Casts are exact and the shifts stay well below `2^64`, so both `%` vanish. -/
  simp only [UScalar.val_or, i7_post1, i6_post1, i11_post1, i2_post, i5_post, i10_post,
    U8.cast_U64_val_eq, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by scalar_tac : i4.val * 2 ^ 8 < U64.size),
    Nat.mod_eq_of_lt (by scalar_tac : i9.val * 2 ^ 16 < U64.size)]
  /- Innermost `|||` first: the explicit `a` stops `rw` matching the outer one. -/
  rw [lor_mul_two_pow (a := i1.val) (by scalar_tac), lor_mul_two_pow (by scalar_tac)]
  split_conjs
  · scalar_tac
  · scalar_tac


/-# ######################################-/
/-*Spec theorem for `from_bytes.load4_at`*-/
/-# ######################################-/

/-Same concept as `from_bytes.load3_at` just takes an additional byte.-/

/-Pre: `i.val + 4 ≤ b.length` is the only precondition: it covers the three
`index_usize` bounds, and the two `Usize` additions follow from it via
`b.length ≤ Usize.max`. The shifts need nothing, since Aeneas' shift spec
only requires the shift amount to be below the bit width.
 Post: the main statement is that 4 consecutive 8-bit numbers multiplied by
 2^(8*i), i=0,1,2,3 and then added, represent the same number as the same bits
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
  /- Casts are exact and the shifts stay well below `2^64`, so both `%` vanish. -/
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


/-# #############################-/
/-*Spec theorem for `from_bytes`*-/
/-# #############################-/

/-Let's denote elements of data by d[i], which are of type U8.
h[0] =  load4_at(data,  0); *h[0]=d[0]+2^8·d[1]+2^16·d[2]+2^24·d[3]*
h[1] =  load3_at(data,  4) << 6; *h[1]=2^6·(d[4]+2^8·d[5]+2^16·d[6])*
h[2] =  load3_at(data,  7) << 5; *h[2]=2^5·(d[7]+2^8·d[8]+2^16·d[9])*
h[3] =  load3_at(data, 10) << 3; *h[3]=2^3·(d[10]+2^8·d[11]+2^16·d[12])*
h[4] =  load3_at(data, 13) << 2; *h[4]=2^2·(d[13]+2^8·d[14]+2^16·d[15])*
h[5] =  load4_at(data, 16); *h[5]=d[16]+2^8·d[17]+2^16·d[18]+2^24·d[19]*
h[6] =  load3_at(data, 20) << 7; *h[6]=2^7·(d[20]+2^8·d[21]+2^16·d[22])*
h[7] =  load3_at(data, 23) << 5; *h[7]=2^5·(d[23]+2^8·d[24]+2^16·d[25])*
h[8] =  load3_at(data, 26) << 4; *h[8]=2^4·(d[26]+2^8·d[27]+2^16·d[28])*
h[9] = (load3_at(data, 29) & LOW_23_BITS) << 2; *h[9]=2^2·(d[29]+2^8·d[30]+2^16·d[31] mod 2^23)*

Therefore
*h[0]=d[0]+2^8·d[1]+2^16·d[2]+2^24·d[3]*
*2^26·h[1]=2^32·(d[4]+2^8·d[5]+2^16·d[6])*
*2^51·h[2]=2^56·(d[7]+2^8·d[8]+2^16·d[9])*
*2^77·h[3]=2^80·(d[10]+2^8·d[11]+2^16·d[12])*
*2^102·h[4]=2^104·(d[13]+2^8·d[14]+2^16·d[15])*
*2^128·h[5]=2^128·(d[16]+2^8·d[17]+2^16·d[18]+2^24·d[19])*
*2^153·h[6]=2^160·(d[20]+2^8·d[21]+2^16·d[22])*
*2^179·h[7]=2^184·(d[23]+2^8·d[24]+2^16·d[25])*
*2^204·h[8]=2^208·(d[26]+2^8·d[27]+2^16·d[28])*
*2^230·h[9]=2^232·(d[29]+2^8·d[30]+2^16·d[31] mod 2^23)*

The last step is why there is the *warning* in the original comment.
The function from_bytes preserves the Nat representation only if the input is < 2^255.
Example for when the bound doesn't hold: converting 2^255 into a FieldElement2625.
Without the masking the result would be a field element
with Nat representation 19, but instead it gives 0.-/
def try_1 : Option Nat :=
  let result := from_bytes (Array.make 32#usize [0#u8,0#u8,0#u8,0#u8,0#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,128#u8])
  match result with
  | Result.ok x => some (FieldElement2625_to_Nat x)
  | _ => none

#eval try_1

/-When `input < 2^255` the Nat representation of the result is correct,
even when `input > p`.
Example from original comment: convert 2^255-18 into a FieldElement2625 by applying from_bytes.
The result as a field element has Nat representation 1.-/
def try_2 : Nat :=
  let result := from_bytes (Array.make 32#usize [238#u8,255#u8,255#u8,255#u8,
  255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,
  255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,
  255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,127#u8])
  match result with
  | Result.ok x => FieldElement2625_to_Nat x
  | _ => 0

#eval try_2
#eval try_2 % (2^255-19)

/-Helper function to convert Array U8 32#usize to Nat:-/
def ArrayU8_to_Nat (a : Array U8 32#usize) : Nat :=
  a[0]!.val +
  2^8 * a[1]!.val + 2^16 * a[2]!.val + 2^24 * a[3]!.val +
  2^32 * a[4]!.val + 2^40 * a[5]!.val + 2^48 * a[6]!.val +
  2^56 * a[7]!.val + 2^64 * a[8]!.val + 2^72 * a[9]!.val +
  2^80 * a[10]!.val + 2^88 * a[11]!.val + 2^96 * a[12]!.val +
  2^104 * a[13]!.val + 2^112 * a[14]!.val + 2^120 * a[15]!.val +
  2^128 * a[16]!.val + 2^136 * a[17]!.val + 2^144 * a[18]!.val +
  2^152 * a[19]!.val + 2^160 * a[20]!.val + 2^168 * a[21]!.val +
  2^176 * a[22]!.val + 2^184 * a[23]!.val + 2^192 * a[24]!.val +
  2^200 * a[25]!.val + 2^208 * a[26]!.val + 2^216 * a[27]!.val +
  2^224 * a[28]!.val + 2^232 * a[29]!.val + 2^240 * a[30]!.val +
  2^248 * a[31]!.val

/-- Helper lemma stating that if all 10 elements of a 10-long array are
bounded by 2^32 and we update an element by a value `x` of the form
`x = y <<< m % U64.size` where `y < 2 ^ n` and `n + m ≤ 32`
then each term of the resulting array is still bounded by 2 ^ 32: -/
private theorem set_bound {a a' : Array U64 10#usize} {x y : U64} {k : Usize} {n m : Nat}
(heq : (a' = a.set k x)) (ha : ∀ j, j < 10 → a[j]!.val < 2 ^ 32)
(hx : x.val = y.val <<< m % U64.size) (hy : y.val < 2 ^ n) (hexp : n + m ≤ 32) :
    ∀ j, j < 10 → a'[j]!.val < 2^32 :=
  by
  intro j hj; subst a'; by_cases j = k.val
  --The non-trivial case when a'[j] is a[j] replaced by x:
  case pos =>
    simp_lists
    rewrite [hx, Nat.shiftLeft_eq]
    have hmul := Nat.mul_lt_mul_of_pos_right (k := 2 ^ m) hy (by exact Nat.two_pow_pos m)
    rewrite [← Nat.pow_add] at hmul
    rewrite [U64.size_def, U64.numBits_eq, Nat.mod_eq_of_lt (by
    --Closing the intermediate goal coming from rewriting the mod:
      exact Nat.lt_of_lt_of_le (k := 2 ^ 64) hmul (by
        exact Nat.pow_le_pow_of_le (by decide) (by exact Nat.le_trans (k := 64) hexp (by decide))
        )
      )]
    exact Nat.lt_of_lt_of_le (k := 2 ^ 32) hmul (by exact Nat.pow_le_pow_of_le (by decide) hexp )
  --The simple case when a'[j] = a[j]:
  case neg =>
    have h := ha j hj; simp_lists at h ⊢; exact h

/-- Helper lemma that states that if one updates a limb from `0` to `x` in
an `Array U64 10#usize` representation of a `FieldElement2625` then
the Nat value of the element increases by `x times the limb's weight`: -/
private theorem set_zero_to_x {a a' : Array U64 10#usize} {k : Usize} {x : U64} {n : Nat}
(heq : (a' = a.set k x)) (hindex : k.val < 10) (hzero : a[k.val]!.val = 0)
(hold_sum : ArrayU64_to_Nat a = n) :
    ArrayU64_to_Nat a' = n + (↑x) * 2 ^ (26 * ((k.val + 1) / 2) + 25 * (k.val / 2)) :=
  by
  rewrite [heq, ← hold_sum]
  unfold ArrayU64_to_Nat
  rcases hk : k.val with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k.val
  iterate 10
    · rewrite [hk] at hzero; rewrite [hzero]; simp_lists; scalar_tac
  exact absurd hk (by scalar_tac)


#exit
theorem from_bytes_spec (data : Array U8 32#usize) :
    from_bytes data ⦃ (result : FieldElement2625) =>
      FieldElement2625_to_Nat result % p = ((ArrayU8_to_Nat data) % 2^255) % p ⦄ := by
  unfold from_bytes
  step*
  /-# Proving that from_bytes.load3_at has the bound for index 29:-/
  case hi =>
    rewrite [s9_post]; simp
  /-# Proving the precondition bound from reduce:-/
  case hz =>
  --Introduce and prove the bound i18 < 2 ^ 23:
    have i18_post : ↑i18 < (2 ^ 23 : Nat) := by
      rewrite [U64.bv_toNat] at i17_post
      rewrite [i18_post1]
      have i17_post1 := Nat.lt_of_le_sub_one (by decide) (Nat.le_of_eq i17_post)
      exact Nat.lt_of_le_of_lt (Nat.and_le_right) i17_post1
    --Helper step stating that each element of a constant 0 array is < 2^32:
    have hinit_bound : ∀ j, j < 10 → (Array.repeat 10#usize 0#u64)[j]!.val < 2^32 := by
      simp_lists [Array.repeat_val]; decide
    /-Introducing hypotheses for the two cases, where no bit-shift happens,
    to be able to use the helper lemma set_bound:-/
    have i_post : ↑i = ↑i <<< 0 % U64.size := by
      rewrite [Nat.shiftLeft_zero, U64.val_mod_size_eq]; rfl
    have i9_post : ↑i9 = ↑i9 <<< 0 % U64.size := by
      rewrite [Nat.shiftLeft_zero, U64.val_mod_size_eq]; rfl
    --Renaming the initial hypothesis to fit the general pattern:
    rename' hinit_bound => b_old
    --Rolling forward the bounds on the arrays:
    iterate 10
      --Step forward and establish the bound on the next array:
      have b_next := set_bound (by assumption) b_old (by assumption) (by assumption) (by decide)
      --Clean-up:
      clear b_old
      --Rename to be able to iterate the process:
      rename' b_next => b_old
    intro j hj
    have hb_old := b_old j hj
    apply_rewrite [Nat.le_of_lt] at hb_old
    exact Nat.le_trans hb_old (by decide)
  /-# Proving that the result represents the same field element as data % 2^255:-/
  rewrite [result_post2]
  unfold ArrayU8_to_Nat
  --experimenting
  have hinit_to_Nat : ArrayU64_to_Nat (Array.repeat 10#usize 0#u64) = 0 := by
    rfl
  iterate 10
    have hnext_to_Nat := set_zero_to_x (by assumption) (by decide) (by simp [*]) hinit_to_Nat
    simp [-Nat.reducePow] at hnext_to_Nat
    clear hinit_to_Nat
    rename' hnext_to_Nat => hinit_to_Nat
  rewrite [hinit_to_Nat]
  clear hinit_to_Nat
  --Introduce and prove the bound i18 < 2 ^ 23:
  have i18_post : ↑i18 < (2 ^ 23 : Nat) := by
    rewrite [U64.bv_toNat] at i17_post
    rewrite [i18_post1]
    have i17_post1 := Nat.lt_of_le_sub_one (by decide) (Nat.le_of_eq i17_post)
    exact Nat.lt_of_le_of_lt (Nat.and_le_right) i17_post1
  iterate 8
    have hmod_kill := (by assumption : _ = _ <<< _ % U64.size)
    rewrite [hmod_kill, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (b := U64.size) (by
      rewrite [U64.size_def, U64.numBits_eq]
      exact Nat.lt_trans (k := 2 ^ 64)
        (Nat.mul_lt_mul_of_pos_right (k := 2 ^ _) (by assumption) (by decide))
        (by decide) )]
    clear hmod_kill
    clear (by assumption : _ = _ <<< _ % U64.size) --kind of a risky move...
  rewrite [i18_post1, UScalar.val_and, ← U64.bv_toNat i17, i17_post, Nat.and_two_pow_sub_one_eq_mod]
  simp [Nat.mul_assoc, ← Nat.mul_mod_mul_right, -Nat.reducePow, ← Nat.pow_add, -p_in_decimal]
  have hadd_mod_disj_bits : ∀ a b m n : Nat, (a < 2 ^ m) → (m ≤ n) →
    a + b * 2 ^ m % 2 ^ n = (a + b * 2 ^ m) % 2 ^ n := by
    intro a b m n ha hexp
    rewrite [← Nat.mod_eq_of_lt (a := a) (b := 2 ^ n) (by
      exact Nat.lt_of_lt_of_le (k := 2 ^ n) ha (by
        exact Nat.pow_le_pow_right (by decide) hexp) )]
    rewrite [Nat.mod_add_mod, Nat.mod_add_mod_eq]
    simp
    nth_rewrite 2 [ ← Nat.pow_sub_mul_pow 2 hexp, Nat.mul_comm]
    rewrite [Nat.mul_comm, Nat.mul_mod_mul_left]
    rewrite [Nat.mod_eq_of_lt (a := a) (b := 2 ^ n) (by
      exact Nat.lt_of_lt_of_le (k := 2 ^ n) ha (by
        exact Nat.pow_le_pow_right (by decide) (hexp)) )]
    have hlt_shiftLeft_mod_two_pow : 2 ^ m * (b % 2 ^ (n - m)) ≤ 2 ^ n - 2 ^ m := by
      nth_rewrite 2 [← Nat.one_mul (2 ^ m)]
      rewrite [← Nat.pow_sub_mul_pow 2 hexp, ← Nat.mul_sub_right_distrib, Nat.mul_comm]
      exact Nat.mul_le_mul_right (k := 2 ^ m) (by
        exact Nat.le_sub_one_of_lt (by
          exact Nat.mod_lt b (by exact Nat.two_pow_pos (n - m))))
    rewrite [Nat.add_comm, ← Nat.sub_add_cancel (n := 2 ^ n) (m := 2 ^ m) (by exact Nat.pow_le_pow_right (by decide) hexp)]
    exact Nat.add_lt_add_of_le_of_lt hlt_shiftLeft_mod_two_pow ha
  rewrite [hadd_mod_disj_bits _ _ _ _ (by scalar_tac) (by decide)]
  simp [*, -Nat.reducePow, -p_in_decimal]
  agrind



/-# #########################-/
/-*Spec theorem for `negate`*-/
/-# #########################-/

/- *p in binary is 255 consecutive 1s minus 18*
*This leads to i, i4 and i8, which are the limbs for 2^4 · p in the 26/25 radix representation*
*The function computes -x as 2^4 · p - x to avoid underflow*
def backend.serial.u32.field.FieldElement2625.negate
  (self : backend.serial.u32.field.FieldElement2625) :
  Result backend.serial.u32.field.FieldElement2625
  := do
  let i ← 67108845#u32 <<< 4#i32 *67108845 = 2^26-1-18, so i=2^4(2^26-19)*
  let i1 ← Array.index_usize self 0#usize *=x[0]*
  let i2 ← i - i1
  let i3 ← lift (UScalar.cast .U64 i2)
  let i4 ← 33554431#u32 <<< 4#i32 *33554431 = 2^25-1, so i4=2^4(2^25-1)*
  let i5 ← Array.index_usize self 1#usize *=x[1]*
  let i6 ← i4 - i5
  let i7 ← lift (UScalar.cast .U64 i6)
  let i8 ← 67108863#u32 <<< 4#i32 *67108863 = 2^26-1, so i8=2^4(2^26-1)*
  let i9 ← Array.index_usize self 2#usize *=x[2]*
  let i10 ← i8 - i9
  let i11 ← lift (UScalar.cast .U64 i10)
  let i12 ← Array.index_usize self 3#usize *=x[3]*
  let i13 ← i4 - i12
  let i14 ← lift (UScalar.cast .U64 i13)
  let i15 ← Array.index_usize self 4#usize *=x[4]*
  let i16 ← i8 - i15
  let i17 ← lift (UScalar.cast .U64 i16)
  let i18 ← Array.index_usize self 5#usize *=x[5]*
  let i19 ← i4 - i18
  let i20 ← lift (UScalar.cast .U64 i19)
  let i21 ← Array.index_usize self 6#usize *=x[6]*
  let i22 ← i8 - i21
  let i23 ← lift (UScalar.cast .U64 i22)
  let i24 ← Array.index_usize self 7#usize *=x[7]*
  let i25 ← i4 - i24
  let i26 ← lift (UScalar.cast .U64 i25)
  let i27 ← Array.index_usize self 8#usize *=x[8]*
  let i28 ← i8 - i27
  let i29 ← lift (UScalar.cast .U64 i28)
  let i30 ← Array.index_usize self 9#usize *=x[9]*
  let i31 ← i4 - i30
  let i32 ← lift (UScalar.cast .U64 i31)
  *up to this point each limb of x is subtracted from the corresponding limb of 2^4 · p*
  let neg ←
    backend.serial.u32.field.FieldElement2625.reduce
      (Array.make 10#usize [ i3, i7, i11, i14, i17, i20, i23, i26, i29, i32 ])
  *this step reduces each limb to fit the 26/25 width accordingly*
  ok neg
*For the final postcondition we going to need addition of field elements first*
-/

end backend.serial.u32.field.FieldElement2625
end curve25519_dalek

/- Adding a low part `a < k` to a multiple of `k` commutes with reduction modulo
`j * k`: truncating the high part leaves it a multiple of `k`, so it never reaches
into the range `a` occupies and the two summands still fit below the modulus.
Stated with the single `%` outermost on the left, so use `←` to push a `%` outwards. -/
theorem Nat.add_mul_mod_mul_right_of_lt {a b j k : Nat} (ha : a < k) (hj : 0 < j) :
    (a + b * k) % (j * k) = a + b * k % (j * k) := by
  have hlt : a + b * k % (j * k) < j * k := by
    rw [Nat.mul_mod_mul_right]
    calc a + b % j * k
        < k + b % j * k := Nat.add_lt_add_right ha _
      _ = (b % j + 1) * k := by ring
      _ ≤ j * k := Nat.mul_le_mul_right _ (Nat.mod_lt b hj)
  have hak : a < j * k := Nat.lt_of_lt_of_le ha (Nat.le_mul_of_pos_left k hj)
  rw [Nat.add_mod, Nat.mod_eq_of_lt hak, Nat.mod_eq_of_lt hlt]

/- Radix version: a limb below `2 ^ m` plus a multiple of `2 ^ m`, reduced into a
`2 ^ n` window. Base 2 contributes only the factorisation `2 ^ n = 2 ^ (n-m) * 2 ^ m`;
positivity of the cofactor is automatic. -/
theorem Nat.add_mul_two_pow_mod_two_pow_of_lt {a b m n : Nat}
    (ha : a < 2 ^ m) (hmn : m ≤ n) :
    (a + b * 2 ^ m) % 2 ^ n = a + b * 2 ^ m % 2 ^ n := by
  have hsplit : (2:Nat) ^ n = 2 ^ (n - m) * 2 ^ m := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hmn]
  rw [hsplit]
  exact Nat.add_mul_mod_mul_right_of_lt ha (Nat.two_pow_pos _)

/- Original hand-rolled derivation of the radix version, kept for reference:
  rewrite [← Nat.mod_eq_of_lt (a := a) (b := 2 ^ n) (by
    exact Nat.lt_of_lt_of_le (k := 2 ^ n) ha (by
      exact Nat.pow_le_pow_right (by decide) hexp) )]
  rewrite [Nat.mod_add_mod, Nat.mod_add_mod_eq]
  simp
  nth_rewrite 2 [ ← Nat.pow_sub_mul_pow 2 hexp, Nat.mul_comm]
  rewrite [Nat.mul_comm, Nat.mul_mod_mul_left]
  rewrite [Nat.mod_eq_of_lt (a := a) (b := 2 ^ n) (by
    exact Nat.lt_of_lt_of_le (k := 2 ^ n) ha (by
      exact Nat.pow_le_pow_right (by decide) (hexp)) )]
  have hlt_shiftLeft_mod_two_pow : 2 ^ m * (b % 2 ^ (n - m)) ≤ 2 ^ n - 2 ^ m := by
    nth_rewrite 2 [← Nat.one_mul (2 ^ m)]
    rewrite [← Nat.pow_sub_mul_pow 2 hexp, ← Nat.mul_sub_right_distrib, Nat.mul_comm]
    exact Nat.mul_le_mul_right (k := 2 ^ m) (by
      exact Nat.le_sub_one_of_lt (by
        exact Nat.mod_lt b (by exact Nat.two_pow_pos (n - m))))
  rewrite [Nat.add_comm, ← Nat.sub_add_cancel (n := 2 ^ n) (m := 2 ^ m) (by
  exact Nat.pow_le_pow_right (by decide) hexp)]
  exact Nat.add_lt_add_of_le_of_lt hlt_shiftLeft_mod_two_pow ha
-/

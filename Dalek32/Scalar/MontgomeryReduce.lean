/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Aeneas.Command.Decompose
import Dalek32.Auxiliary
import Dalek32.Constants.L
import Dalek32.Constants.Lfactor
import Dalek32.Lint.Basic
import Dalek32.Scalar.Index
import Dalek32.Scalar.M
import Dalek32.Scalar.Sub
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Spec theorem for `montgomery_reduce`

Montgomery reduction of seventeen radix-`2^29` coefficients.
Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 328-369.

The generated function is one long straight-line computation, so `#decompose` splits it into

* `montgomery_reduce_adjust`, the nine `part1` rows that produce the Montgomery quotient
  digits `n0, …, n8` and cancel the low nine radix digits, and
* `montgomery_reduce_extract`, the eight `part2` rows that read off the result digits
  `r0, …, r7` and the top carry.

The two halves of the wide value and of the product `n * L` are given names (`lowWide`,
`highWide`, `adjustPartial`, `extractPartial`), each half is verified against its own half of
the Montgomery identity (`adjust_identity` and `extract_identity`), and
`montgomery_reduce_spec` glues the halves together before the final conditional subtraction.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

namespace montgomery_reduce

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_reduce::part1`**

Cancels the low radix digit and returns the exact carry. -/
@[step]
theorem part1_spec (sum : U64) (h_sum : sum.val + limbRadix * limbRadix ≤ U64.max) :
    part1 sum ⦃ (carry : U64) (p : U32) =>
      p.val < limbRadix ∧
      -- Redundant: follows from the other two conjuncts (see the proof).
      carry.val < 2 ^ 35 ∧
      carry.val * limbRadix = sum.val + p.val * constants.L[0]!.val ⦄ := by
  unfold part1
  step as ⟨low, h_low⟩
  step as ⟨multiple, h_multiple⟩
  step as ⟨shifted, h_shifted⟩
  step as ⟨mask, h_mask⟩
  have h_mask_value : mask.val = limbRadix - 1 := by
    rw [h_mask, h_shifted, U32.size, U32.numBits]
    rfl
  step as ⟨p, h_p⟩
  have h_p_value : p.val = (sum.val * constants.LFACTOR.val) % limbRadix := by
    simp only [h_p, UScalar.val_and, h_mask_value, limbRadix,
      Nat.and_two_pow_sub_one_eq_mod, h_multiple, core.num.U32.wrapping_mul_val_eq,
      h_low, UScalar.cast_val_eq, UScalar.size, UScalarTy.numBits]
    rw [Nat.mod_mul_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 29 ∣ 2 ^ 32)]
  have h_p_bound : p.val < limbRadix := by
    rw [h_p_value]
    exact Nat.mod_lt _ (by decide)
  have h_low_order : order % limbRadix = constants.L[0]!.val % limbRadix := by
    rw [← constants.L_spec]
    unfold asNat Array.uScalarToNatRadix constants.L limbRadix
    decide
  have h_factor : (constants.L[0]!.val * constants.LFACTOR.val + 1) % limbRadix = 0 := by
    have h := constants.LFACTOR_spec.1
    rw [Nat.add_mod, Nat.mul_mod, h_low_order] at h
    rw [Nat.add_mod, Nat.mul_mod]
    exact h
  have h_cancel : (sum.val + p.val * constants.L[0]!.val) % limbRadix = 0 := by
    rw [h_p_value]
    calc
      (sum.val + (sum.val * constants.LFACTOR.val % limbRadix) *
          constants.L[0]!.val) % limbRadix =
          (sum.val * (constants.L[0]!.val * constants.LFACTOR.val + 1)) % limbRadix := by
        rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod]
        congr 1
        ring
      _ = 0 := by
        rw [Nat.mul_mod, h_factor]
        simp only [Nat.mul_zero, Nat.zero_mod]
  step with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨l0, h_l0⟩
  have h_l0_bound : l0.val < limbRadix := by
    simpa only [h_l0, Array.getElem!_Nat_eq] using constants.L_limbs_lt 0 (by decide)
  step with m_spec as ⟨product, h_product⟩
  have h_product_bound : product.val ≤ limbRadix * limbRadix := by
    rw [h_product]
    exact Nat.mul_le_mul h_p_bound.le h_l0_bound.le
  step -threadGrindState -grind with U64.add_spec as ⟨joined, h_joined⟩ by
    simp only [limbRadix, U64.max_eq] at h_sum h_product_bound ⊢
    omega
  step as ⟨carry, h_carry⟩
  have h_carry_value : carry.val = joined.val / limbRadix := by
    simpa only [Nat.shiftRight_eq_div_pow, limbRadix] using h_carry
  have h_eq : carry.val * limbRadix = sum.val + p.val * constants.L[0]!.val := by
    have h_div := Nat.mod_add_div joined.val limbRadix
    have h_joined_value : joined.val = sum.val + p.val * constants.L[0]!.val := by
      simp only [h_joined, h_product, h_l0, Array.getElem!_Nat_eq]
    rw [h_joined_value, h_cancel] at h_div
    rw [h_carry_value, h_joined_value]
    simpa only [Nat.zero_add, Nat.mul_comm] using h_div
  -- The carry bound is redundant: the equation, `p < B` and the overflow precondition give
  -- `carry * B < 2 ^ 64`.
  have h_carry_bound : carry.val < 2 ^ 35 := by
    have h_prod : p.val * constants.L[0]!.val < limbRadix * limbRadix :=
      Nat.mul_lt_mul'' h_p_bound (constants.L_limbs_lt 0 (by decide))
    simp only [limbRadix, U64.max_eq] at h_eq h_prod h_sum
    omega
  exact ⟨h_p_bound, h_carry_bound, h_eq⟩

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_reduce::part2`**

Splits off one radix digit without losing high bits. -/
@[step]
theorem part2_spec (sum : U64) :
    part2 sum ⦃ (carry : U64) (w : U32) =>
      w.val < limbRadix ∧
      -- Redundant: follows from the other two conjuncts (see the proof).
      carry.val < 2 ^ 35 ∧
      carry.val * limbRadix + w.val = sum.val ⦄ := by
  unfold part2
  step as ⟨low, h_low⟩
  step as ⟨shifted, h_shifted⟩
  step as ⟨mask, h_mask⟩
  have h_mask_value : mask.val = limbRadix - 1 := by
    rw [h_mask, h_shifted, U32.size, U32.numBits]
    rfl
  step as ⟨w, h_w⟩
  step as ⟨carry, h_carry⟩
  have h_w_value : w.val = sum.val % limbRadix := by
    simp only [h_w, UScalar.val_and, h_mask_value, limbRadix,
      Nat.and_two_pow_sub_one_eq_mod, h_low, UScalar.cast_val_eq, UScalarTy.numBits]
    exact Nat.mod_mod_of_dvd _ (by decide : 2 ^ 29 ∣ 2 ^ 32)
  have h_carry_value : carry.val = sum.val / limbRadix := by
    simpa only [Nat.shiftRight_eq_div_pow, limbRadix] using h_carry
  have h_w_bound : w.val < limbRadix := by
    rw [h_w_value]
    exact Nat.mod_lt _ (by decide)
  have h_eq : carry.val * limbRadix + w.val = sum.val := by
    rw [h_carry_value, h_w_value]
    simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div sum.val limbRadix
  -- The carry bound is redundant: the equation and `sum < 2 ^ 64` give `carry * B < 2 ^ 64`.
  have h_carry_bound : carry.val < 2 ^ 35 := by
    have h_bound : sum.val < 2 ^ 64 := sum.hBounds
    simp only [limbRadix] at h_eq
    omega
  exact ⟨h_w_bound, h_carry_bound, h_eq⟩

end montgomery_reduce

/-! ## Splitting the generated function

The generated body is a single `do` block with 146 let-bindings.  Bindings `0 … 84` are the
nine `part1` rows (the last of them binds `(carry8, n8)`), and the remaining bindings up to
the concluding cast and subtraction are the eight `part2` rows.  Because `#decompose` clauses
apply sequentially, after the first clause the body starts with the `montgomery_reduce_adjust`
call at index `0`, so the second clause skips it and takes the following `144 - 85 + 1 = 60`
bindings.

The five `letRange`-crossing values `i3, i8, i15, i24, i65` are the cached lookups
`constants.L[1]!, constants.L[2]!, constants.L[3]!, constants.L[4]!, constants.L[8]!`, which
is why the adjust phase returns a fourteen-wide tuple.  The quotient digit `n0` is *not*
returned: it is dead after the adjust phase, its whole contribution already being folded into
`carry8`. -/
-- `#decompose` generates declarations rather than querying the environment, so the Mathlib
-- convention that forbids `#`-commands in library files does not apply to it.
set_option linter.hashCommand false in
#decompose montgomery_reduce montgomery_reduce_eq
  letRange 0 85 => montgomery_reduce_adjust
  letRange 1 60 => montgomery_reduce_extract

/-! ## Naming the partial sums

`B` denotes `limbRadix`, `t_i` the coefficient `limbs[i]!`, `l_k` the limb `constants.L[k]!`
(with `l5 = l6 = l7 = 0`) and `n_j` the Montgomery quotient digits.  Compare with the rows of
"curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 346-364. -/

/-- The low half of the wide value, `Σ_{i<9} B^i · t_i`. -/
private def lowWide (limbs : Array U64 17#usize) : Nat :=
  limbs[0]!.val + limbRadix * limbs[1]!.val + limbRadix ^ 2 * limbs[2]!.val +
    limbRadix ^ 3 * limbs[3]!.val + limbRadix ^ 4 * limbs[4]!.val +
    limbRadix ^ 5 * limbs[5]!.val + limbRadix ^ 6 * limbs[6]!.val +
    limbRadix ^ 7 * limbs[7]!.val + limbRadix ^ 8 * limbs[8]!.val

/-- The high half of the wide value divided by `B^9`, `Σ_{i<8} B^i · t_{9+i}`. -/
private def highWide (limbs : Array U64 17#usize) : Nat :=
  limbs[9]!.val + limbRadix * limbs[10]!.val + limbRadix ^ 2 * limbs[11]!.val +
    limbRadix ^ 3 * limbs[12]!.val + limbRadix ^ 4 * limbs[13]!.val +
    limbRadix ^ 5 * limbs[14]!.val + limbRadix ^ 6 * limbs[15]!.val +
    limbRadix ^ 7 * limbs[16]!.val

/-- The part of `n * L` of weight below `B^9`: the coefficient of `B^i` collects the products
`n_j * l_k` with `j + k = i`, in the order the `part1` rows accumulate them. -/
private def adjustPartial (n0 n1 n2 n3 n4 n5 n6 n7 n8 : Nat) : Nat :=
  n0 * constants.L[0]!.val +
    limbRadix * (n0 * constants.L[1]!.val + n1 * constants.L[0]!.val) +
    limbRadix ^ 2 * (n0 * constants.L[2]!.val + n1 * constants.L[1]!.val +
      n2 * constants.L[0]!.val) +
    limbRadix ^ 3 * (n0 * constants.L[3]!.val + n1 * constants.L[2]!.val +
      n2 * constants.L[1]!.val + n3 * constants.L[0]!.val) +
    limbRadix ^ 4 * (n0 * constants.L[4]!.val + n1 * constants.L[3]!.val +
      n2 * constants.L[2]!.val + n3 * constants.L[1]!.val + n4 * constants.L[0]!.val) +
    limbRadix ^ 5 * (n1 * constants.L[4]!.val + n2 * constants.L[3]!.val +
      n3 * constants.L[2]!.val + n4 * constants.L[1]!.val + n5 * constants.L[0]!.val) +
    limbRadix ^ 6 * (n2 * constants.L[4]!.val + n3 * constants.L[3]!.val +
      n4 * constants.L[2]!.val + n5 * constants.L[1]!.val + n6 * constants.L[0]!.val) +
    limbRadix ^ 7 * (n3 * constants.L[4]!.val + n4 * constants.L[3]!.val +
      n5 * constants.L[2]!.val + n6 * constants.L[1]!.val + n7 * constants.L[0]!.val) +
    limbRadix ^ 8 * (n0 * constants.L[8]!.val + n4 * constants.L[4]!.val +
      n5 * constants.L[3]!.val + n6 * constants.L[2]!.val + n7 * constants.L[1]!.val +
      n8 * constants.L[0]!.val)

/-- The part of `n * L` of weight at least `B^9`, divided by `B^9`: the coefficient of `B^i`
collects the products `n_j * l_k` with `j + k = 9 + i`, in the order the `part2` rows
accumulate them. -/
private def extractPartial (n1 n2 n3 n4 n5 n6 n7 n8 : Nat) : Nat :=
  n1 * constants.L[8]!.val + n5 * constants.L[4]!.val + n6 * constants.L[3]!.val +
      n7 * constants.L[2]!.val + n8 * constants.L[1]!.val +
    limbRadix * (n2 * constants.L[8]!.val + n6 * constants.L[4]!.val +
      n7 * constants.L[3]!.val + n8 * constants.L[2]!.val) +
    limbRadix ^ 2 * (n3 * constants.L[8]!.val + n7 * constants.L[4]!.val +
      n8 * constants.L[3]!.val) +
    limbRadix ^ 3 * (n4 * constants.L[8]!.val + n8 * constants.L[4]!.val) +
    limbRadix ^ 4 * (n5 * constants.L[8]!.val) +
    limbRadix ^ 5 * (n6 * constants.L[8]!.val) +
    limbRadix ^ 6 * (n7 * constants.L[8]!.val) +
    limbRadix ^ 7 * (n8 * constants.L[8]!.val)

/-- The wide value splits at weight `B^9`. -/
private theorem wideAsNat_split (limbs : Array U64 17#usize) :
    wideAsNat limbs = lowWide limbs + limbRadix ^ 9 * highWide limbs := by
  simp only [wideAsNat, Array.uScalarToNatRadix, lowWide, highWide, UScalar.ofNatCore_val_eq,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, limbRadix, pow_mul]
  ring

/-- The product of a nine-limb value with `L` splits at weight `B^9`. -/
private theorem asNat_mul_order_split (a : Scalar29) :
    asNat a * order =
      adjustPartial a[0]!.val a[1]!.val a[2]!.val a[3]!.val a[4]!.val a[5]!.val a[6]!.val
          a[7]!.val a[8]!.val +
        limbRadix ^ 9 * extractPartial a[1]!.val a[2]!.val a[3]!.val a[4]!.val a[5]!.val
          a[6]!.val a[7]!.val a[8]!.val := by
  rw [← constants.L_spec]
  simp only [asNat, Array.uScalarToNatRadix, adjustPartial, extractPartial,
    UScalar.ofNatCore_val_eq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, limbRadix,
    pow_mul, constants.L, Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
    List.getElem!_cons_succ]
  ring

private theorem montgomeryRadix_eq : montgomeryRadix = limbRadix ^ 9 := by
  simp only [montgomeryRadix, limbRadix, ← pow_mul]

/-! ## The two halves -/
section Halves

/-! ### A prepared lemma kit for `step*`

Each operation of the two halves gets a specification that threads an explicit bound through
the accumulator as a ghost variable.  `step*` infers the ghost variables by matching the
hypotheses against the bounds already in the context, so no side condition ever needs the
equality chain: every remaining proof obligation is a check between numerals. -/

/-- Addition with the bound `A + B` threaded through. -/
@[local step]
private theorem add_bounded {A B : Nat} (x y : U64) (hx : x.val < A) (hy : y.val < B)
    (hAB : A + B ≤ U64.max) :
    x + y ⦃ (z : U64) => z.val = x.val + y.val ∧ z.val < A + B ⦄ := by
  step -grind -threadGrindState with U64.add_spec as ⟨z, hz⟩ by omega
  omega

/-- The product of two radix digits is below `2 ^ 58`. -/
@[local step]
private theorem m_bounded (x y : U32) (hx : x.val < limbRadix) (hy : y.val < limbRadix) :
    m x y ⦃ (r : U64) => r.val = x.val * y.val ∧ r.val < 2 ^ 58 ⦄ := by
  step -grind -threadGrindState with m_spec as ⟨r, hr⟩
  refine ⟨hr, ?_⟩
  rw [hr]
  exact (Nat.mul_lt_mul'' hx hy).trans_le (by norm_num [limbRadix])

/-- Looking up a limb of `constants.L` returns a radix digit. -/
@[local step]
private theorem L_index_bounded (k : Usize) (hk : k.val < 9) :
    Insts.CoreOpsIndexIndexUsizeU32.index constants.L k ⦃ (r : U32) =>
      r = constants.L[k.val]! ∧ r.val < limbRadix ⦄ := by
  step -grind -threadGrindState with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨r, hr⟩
  rw [← Array.getElem!_Nat_eq] at hr
  exact ⟨hr, hr ▸ constants.L_limbs_lt k.val hk⟩

-- `step` does not backtrack when the precondition of the lemma it picked cannot be discharged;
-- it leaves the precondition as an open goal instead of trying the next candidate.  A single
-- limb-lookup lemma assuming `∀ i < 9, …` would thus be applied to `limbs[9]` in the extract
-- half and get stuck, so each half registers its own lookup lemma, scoped to its section.
section Adjust

/-- Looking up one of the low nine coefficients returns a bounded value. -/
@[local step]
private theorem low_limb_index_bounded (limbs : Array U64 17#usize) (k : Usize)
    (h_bounds : ∀ i < 9, limbs[i]!.val < 2 ^ 63) (hk : k.val < 9) :
    limbs.index_usize k ⦃ (r : U64) => r = limbs[k.val]! ∧ r.val < 2 ^ 63 ⦄ := by
  step -grind -threadGrindState with Array.index_usize_spec as ⟨r, hr⟩ by scalar_tac
  have h : r = limbs[k.val]! := by
    rw [hr, Array.getElem!_Nat_eq]
    exact (getElem!_pos _ _ (by scalar_tac)).symm
  exact ⟨h, h ▸ h_bounds k.val hk⟩

/-- `part1_spec` with its overflow precondition split into a bound on the input and a check
between numerals. -/
@[local step]
private theorem part1_bounded {A : Nat} (sum : U64) (hs : sum.val < A)
    (hA : A + 2 ^ 58 ≤ U64.max) :
    montgomery_reduce.part1 sum ⦃ (carry : U64) (p : U32) =>
      p.val < limbRadix ∧
      carry.val < 2 ^ 35 ∧
      carry.val * limbRadix = sum.val + p.val * constants.L[0]!.val ⦄ := by
  step -grind -threadGrindState with montgomery_reduce.part1_spec as ⟨carry, p, h1, h2, h3⟩ by
    simp only [limbRadix, U64.max_eq] at hA ⊢
    omega
  exact ⟨h1, h2, h3⟩

/-- The carry out of the adjust phase is bounded by the identity alone: the low half of the wide
value is below `2 ^ 295` and the low half of `n * L` below `2 ^ 293`. -/
private theorem adjust_carry_bound (limbs : Array U64 17#usize)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 c8 : Nat)
    (h_bounds : ∀ i < 9, limbs[i]!.val < 2 ^ 63)
    (hn0 : n0 < limbRadix) (hn1 : n1 < limbRadix) (hn2 : n2 < limbRadix) (hn3 : n3 < limbRadix)
    (hn4 : n4 < limbRadix) (hn5 : n5 < limbRadix) (hn6 : n6 < limbRadix) (hn7 : n7 < limbRadix)
    (hn8 : n8 < limbRadix)
    (h : lowWide limbs + adjustPartial n0 n1 n2 n3 n4 n5 n6 n7 n8 = c8 * limbRadix ^ 9) :
    c8 < 2 ^ 35 := by
  have t0 := h_bounds 0 (by decide); have t1 := h_bounds 1 (by decide)
  have t2 := h_bounds 2 (by decide); have t3 := h_bounds 3 (by decide)
  have t4 := h_bounds 4 (by decide); have t5 := h_bounds 5 (by decide)
  have t6 := h_bounds 6 (by decide); have t7 := h_bounds 7 (by decide)
  have t8 := h_bounds 8 (by decide)
  simp only [lowWide, adjustPartial, limbRadix, constants.L, Array.getElem!_Nat_eq, Array.make,
    List.getElem!_cons_zero, List.getElem!_cons_succ, UScalar.ofNatCore_val_eq, Nat.reducePow]
    at h hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 t0 t1 t2 t3 t4 t5 t6 t7 t8
  omega

/-- The nine `part1` rows telescope to the low half of the Montgomery identity. -/
private theorem adjust_identity {limbs : Array U64 17#usize}
    {n0 n1 n2 n3 n4 n5 n6 n7 n8 c0 c1 c2 c3 c4 c5 c6 c7 c8 : Nat}
    (h0 : c0 * limbRadix = limbs[0]!.val + n0 * constants.L[0]!.val)
    (h1 : c1 * limbRadix = c0 + limbs[1]!.val + n0 * constants.L[1]!.val +
      n1 * constants.L[0]!.val)
    (h2 : c2 * limbRadix = c1 + limbs[2]!.val + n0 * constants.L[2]!.val +
      n1 * constants.L[1]!.val + n2 * constants.L[0]!.val)
    (h3 : c3 * limbRadix = c2 + limbs[3]!.val + n0 * constants.L[3]!.val +
      n1 * constants.L[2]!.val + n2 * constants.L[1]!.val + n3 * constants.L[0]!.val)
    (h4 : c4 * limbRadix = c3 + limbs[4]!.val + n0 * constants.L[4]!.val +
      n1 * constants.L[3]!.val + n2 * constants.L[2]!.val + n3 * constants.L[1]!.val +
      n4 * constants.L[0]!.val)
    (h5 : c5 * limbRadix = c4 + limbs[5]!.val + n1 * constants.L[4]!.val +
      n2 * constants.L[3]!.val + n3 * constants.L[2]!.val + n4 * constants.L[1]!.val +
      n5 * constants.L[0]!.val)
    (h6 : c6 * limbRadix = c5 + limbs[6]!.val + n2 * constants.L[4]!.val +
      n3 * constants.L[3]!.val + n4 * constants.L[2]!.val + n5 * constants.L[1]!.val +
      n6 * constants.L[0]!.val)
    (h7 : c7 * limbRadix = c6 + limbs[7]!.val + n3 * constants.L[4]!.val +
      n4 * constants.L[3]!.val + n5 * constants.L[2]!.val + n6 * constants.L[1]!.val +
      n7 * constants.L[0]!.val)
    (h8 : c8 * limbRadix = c7 + limbs[8]!.val + n0 * constants.L[8]!.val +
      n4 * constants.L[4]!.val + n5 * constants.L[3]!.val + n6 * constants.L[2]!.val +
      n7 * constants.L[1]!.val + n8 * constants.L[0]!.val) :
    lowWide limbs + adjustPartial n0 n1 n2 n3 n4 n5 n6 n7 n8 = c8 * limbRadix ^ 9 := by
  simp only [lowWide, adjustPartial]
  zify at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  linear_combination -(h0 + h1 * (limbRadix : Int) + h2 * (limbRadix : Int) ^ 2 +
    h3 * (limbRadix : Int) ^ 3 + h4 * (limbRadix : Int) ^ 4 + h5 * (limbRadix : Int) ^ 5 +
    h6 * (limbRadix : Int) ^ 6 + h7 * (limbRadix : Int) ^ 7 + h8 * (limbRadix : Int) ^ 8)

/-- **Spec theorem for the adjust phase of
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_reduce`**

Returns the cached `constants.L` lookups, the Montgomery quotient digits `n1, …, n8` and the
carry out of the ninth row; the digit `n0` is existentially quantified since the phase does not
return it. -/
@[scoped step]
theorem montgomery_reduce_adjust_spec (limbs : Array U64 17#usize)
    (h_bounds : ∀ i < 9, limbs[i]!.val < 2 ^ 63) :
    montgomery_reduce_adjust limbs ⦃ (i3 n1 i8 n2 i15 n3 i24 n4 n5 n6 n7 i65 : U32)
        (carry8 : U64) (n8 : U32) =>
      i3 = constants.L[1]! ∧ i8 = constants.L[2]! ∧ i15 = constants.L[3]! ∧
      i24 = constants.L[4]! ∧ i65 = constants.L[8]! ∧
      n1.val < limbRadix ∧ n2.val < limbRadix ∧ n3.val < limbRadix ∧ n4.val < limbRadix ∧
      n5.val < limbRadix ∧ n6.val < limbRadix ∧ n7.val < limbRadix ∧ n8.val < limbRadix ∧
      -- Redundant: follows from the identity below (see the proof).
      carry8.val < 2 ^ 35 ∧
      ∃ n0 : U32, n0.val < limbRadix ∧
        lowWide limbs + adjustPartial n0.val n1.val n2.val n3.val n4.val n5.val n6.val n7.val
          n8.val = carry8.val * limbRadix ^ 9 ⦄ := by
  unfold montgomery_reduce_adjust
  step* -grind -threadGrindState by first | assumption | norm_num [U64.max_eq, limbRadix]
  -- Express the nine rows in the input coefficients and quotient digits.
  simp only [*] at carry_post3 carry1_post3 carry2_post3 carry3_post3 carry4_post3
  simp only [*] at carry5_post3 carry6_post3 carry7_post3 carry8_post3
  have h_identity := adjust_identity carry_post3 carry1_post3 carry2_post3 carry3_post3
    carry4_post3 carry5_post3 carry6_post3 carry7_post3 carry8_post3
  -- The carry bound is redundant: it follows from the identity.
  have h_carry8 := adjust_carry_bound limbs _ _ _ _ _ _ _ _ _ _ h_bounds carry_post1 carry1_post1
    carry2_post1 carry3_post1 carry4_post1 carry5_post1 carry6_post1 carry7_post1 carry8_post1
    h_identity
  exact ⟨i3_post1, i8_post1, i15_post1, i24_post1, i65_post1, carry1_post1, carry2_post1,
    carry3_post1, carry4_post1, carry5_post1, carry6_post1, carry7_post1, carry8_post1,
    h_carry8, n0, carry_post1, h_identity⟩

end Adjust

section Extract

/-- Looking up one of the high eight coefficients returns a bounded value. -/
@[local step]
private theorem high_limb_index_bounded (limbs : Array U64 17#usize) (k : Usize)
    (h_bounds : ∀ i, 9 ≤ i → i < 17 → limbs[i]!.val < 2 ^ 63) (hk : 9 ≤ k.val)
    (hk' : k.val < 17) :
    limbs.index_usize k ⦃ (r : U64) => r = limbs[k.val]! ∧ r.val < 2 ^ 63 ⦄ := by
  step -grind -threadGrindState with Array.index_usize_spec as ⟨r, hr⟩ by scalar_tac
  have h : r = limbs[k.val]! := by
    rw [hr, Array.getElem!_Nat_eq]
    exact (getElem!_pos _ _ (by scalar_tac)).symm
  exact ⟨h, h ▸ h_bounds k.val hk hk'⟩

/-- The eight `part2` rows telescope to the high half of the Montgomery identity. -/
private theorem extract_identity {limbs : Array U64 17#usize}
    {n1 n2 n3 n4 n5 n6 n7 n8 c8 c9 c10 c11 c12 c13 c14 c15 c16 r0 r1 r2 r3 r4 r5 r6 r7 : Nat}
    (h9 : c9 * limbRadix + r0 = c8 + limbs[9]!.val + n1 * constants.L[8]!.val +
      n5 * constants.L[4]!.val + n6 * constants.L[3]!.val + n7 * constants.L[2]!.val +
      n8 * constants.L[1]!.val)
    (h10 : c10 * limbRadix + r1 = c9 + limbs[10]!.val + n2 * constants.L[8]!.val +
      n6 * constants.L[4]!.val + n7 * constants.L[3]!.val + n8 * constants.L[2]!.val)
    (h11 : c11 * limbRadix + r2 = c10 + limbs[11]!.val + n3 * constants.L[8]!.val +
      n7 * constants.L[4]!.val + n8 * constants.L[3]!.val)
    (h12 : c12 * limbRadix + r3 = c11 + limbs[12]!.val + n4 * constants.L[8]!.val +
      n8 * constants.L[4]!.val)
    (h13 : c13 * limbRadix + r4 = c12 + limbs[13]!.val + n5 * constants.L[8]!.val)
    (h14 : c14 * limbRadix + r5 = c13 + limbs[14]!.val + n6 * constants.L[8]!.val)
    (h15 : c15 * limbRadix + r6 = c14 + limbs[15]!.val + n7 * constants.L[8]!.val)
    (h16 : c16 * limbRadix + r7 = c15 + limbs[16]!.val + n8 * constants.L[8]!.val) :
    c8 + highWide limbs + extractPartial n1 n2 n3 n4 n5 n6 n7 n8 =
      r0 + limbRadix * r1 + limbRadix ^ 2 * r2 + limbRadix ^ 3 * r3 + limbRadix ^ 4 * r4 +
        limbRadix ^ 5 * r5 + limbRadix ^ 6 * r6 + limbRadix ^ 7 * r7 + limbRadix ^ 8 * c16 := by
  simp only [highWide, extractPartial]
  zify at h9 h10 h11 h12 h13 h14 h15 h16 ⊢
  linear_combination -(h9 + h10 * (limbRadix : Int) + h11 * (limbRadix : Int) ^ 2 +
    h12 * (limbRadix : Int) ^ 3 + h13 * (limbRadix : Int) ^ 4 + h14 * (limbRadix : Int) ^ 5 +
    h15 * (limbRadix : Int) ^ 6 + h16 * (limbRadix : Int) ^ 7)

/-- **Spec theorem for the extract phase of
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_reduce`**

Applied to the cached `constants.L` lookups, the phase returns the eight low digits of the
exact Montgomery quotient together with the top carry. -/
@[scoped step]
theorem montgomery_reduce_extract_spec (limbs : Array U64 17#usize)
    (n1 n2 n3 n4 n5 n6 n7 : U32) (carry8 : U64) (n8 : U32)
    (h_bounds : ∀ i, 9 ≤ i → i < 17 → limbs[i]!.val < 2 ^ 63)
    (hn1 : n1.val < limbRadix) (hn2 : n2.val < limbRadix) (hn3 : n3.val < limbRadix)
    (hn4 : n4.val < limbRadix) (hn5 : n5.val < limbRadix) (hn6 : n6.val < limbRadix)
    (hn7 : n7.val < limbRadix) (hn8 : n8.val < limbRadix)
    (h_carry8 : carry8.val < 2 ^ 35) :
    montgomery_reduce_extract limbs constants.L[1]! n1 constants.L[2]! n2 constants.L[3]! n3
      constants.L[4]! n4 n5 n6 n7 constants.L[8]! carry8 n8
      ⦃ (r0 r1 r2 r3 r4 r5 r6 : U32) (carry16 : U64) (r7 : U32) =>
      r0.val < limbRadix ∧ r1.val < limbRadix ∧ r2.val < limbRadix ∧ r3.val < limbRadix ∧
      r4.val < limbRadix ∧ r5.val < limbRadix ∧ r6.val < limbRadix ∧ r7.val < limbRadix ∧
      carry8.val + highWide limbs + extractPartial n1.val n2.val n3.val n4.val n5.val n6.val
          n7.val n8.val =
        r0.val + limbRadix * r1.val + limbRadix ^ 2 * r2.val + limbRadix ^ 3 * r3.val +
          limbRadix ^ 4 * r4.val + limbRadix ^ 5 * r5.val + limbRadix ^ 6 * r6.val +
          limbRadix ^ 7 * r7.val + limbRadix ^ 8 * carry16.val ⦄ := by
  unfold montgomery_reduce_extract
  step* -grind -threadGrindState by
    first | assumption | exact constants.L_limbs_lt _ (by decide) | norm_num [U64.max_eq, limbRadix]
  refine ⟨carry9_post1, carry10_post1, carry11_post1, carry12_post1, carry13_post1,
    carry14_post1, carry15_post1, carry16_post1, ?_⟩
  -- Express the eight rows in the input coefficients and quotient digits.
  simp only [*] at carry9_post3 carry10_post3 carry11_post3 carry12_post3
  simp only [*] at carry13_post3 carry14_post3 carry15_post3 carry16_post3
  exact extract_identity carry9_post3 carry10_post3 carry11_post3 carry12_post3 carry13_post3
    carry14_post3 carry15_post3 carry16_post3

end Extract

end Halves

/-- The Montgomery quotient is below `2 * order` when the input is below `R * order`: the
adjustment contributes less than `R * order`, and the identity divides the total by `R`. -/
private theorem quotient_lt_two_order {wide adj q : Nat}
    (h_range : wide < montgomeryRadix * order) (h_adj : adj < montgomeryRadix)
    (h_identity : wide + adj * order = q * montgomeryRadix) : q < 2 * order := by
  have h_radix_pos : 0 < montgomeryRadix := pow_pos (by decide : 0 < (2 : Nat)) 261
  apply (Nat.mul_lt_mul_right h_radix_pos).mp
  rw [← h_identity]
  calc
    wide + adj * order < montgomeryRadix * order + montgomeryRadix * order :=
      Nat.add_lt_add h_range (Nat.mul_lt_mul_of_pos_right h_adj order_pos)
    _ = 2 * order * montgomeryRadix := by ring

/-- A quotient below `2 * order < 2 ^ 254` has its weight-`B ^ 8` digit below `2 ^ 22`. -/
private theorem top_limb_lt {q c : Nat} (hq : q < 2 * order) (hc : limbRadix ^ 8 * c ≤ q) :
    c < 2 ^ 22 := by
  have h_small : q < 2 ^ 254 := by
    calc
      q < 2 * order := hq
      _ < 2 * 2 ^ 253 := Nat.mul_lt_mul_of_pos_left order_lt_two_pow_253 (by decide)
      _ = 2 ^ 254 := by decide
  apply (Nat.mul_lt_mul_left (by decide : 0 < 2 ^ 232)).mp
  rw [← pow_add]
  have h_weight : 2 ^ 232 * c ≤ q := by
    simpa only [limbRadix, ← pow_mul, show 29 * 8 = 232 from rfl] using hc
  exact lt_of_le_of_lt h_weight h_small

/-- A nine-entry literal array is normalized when every entry is a radix digit. -/
private theorem isNormalized_make (a0 a1 a2 a3 a4 a5 a6 a7 a8 : U32)
    (h0 : a0.val < limbRadix) (h1 : a1.val < limbRadix) (h2 : a2.val < limbRadix)
    (h3 : a3.val < limbRadix) (h4 : a4.val < limbRadix) (h5 : a5.val < limbRadix)
    (h6 : a6.val < limbRadix) (h7 : a7.val < limbRadix) (h8 : a8.val < limbRadix) :
    IsNormalized (Array.make 9#usize [a0, a1, a2, a3, a4, a5, a6, a7, a8]) := by
  intro j hj
  simp only [Array.getElem!_Nat_eq, Array.make]
  match j, hj with
  | 0, _ => simpa only [List.getElem!_cons_zero] using h0
  | 1, _ => simpa only [List.getElem!_cons_zero, List.getElem!_cons_succ] using h1
  | 2, _ => simpa only [List.getElem!_cons_zero, List.getElem!_cons_succ] using h2
  | 3, _ => simpa only [List.getElem!_cons_zero, List.getElem!_cons_succ] using h3
  | 4, _ => simpa only [List.getElem!_cons_zero, List.getElem!_cons_succ] using h4
  | 5, _ => simpa only [List.getElem!_cons_zero, List.getElem!_cons_succ] using h5
  | 6, _ => simpa only [List.getElem!_cons_zero, List.getElem!_cons_succ] using h6
  | 7, _ => simpa only [List.getElem!_cons_zero, List.getElem!_cons_succ] using h7
  | 8, _ => simpa only [List.getElem!_cons_zero, List.getElem!_cons_succ] using h8
  | _ + 9, h => exact absurd h (by omega)

/-! ## Gluing the two halves -/

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_reduce`**

Returns the normalized canonical Montgomery residue. -/
@[step]
theorem montgomery_reduce_spec (limbs : Array U64 17#usize)
    (h_bounds : ∀ i < 17, limbs[i]!.val < 2 ^ 63)
    (h_range : wideAsNat limbs < montgomeryRadix * order) :
    montgomery_reduce limbs ⦃ (result : Scalar29) =>
      (asNat result * montgomeryRadix) % order = wideAsNat limbs % order ∧
      IsNormalized result ∧
      asNat result < order ⦄ := by
  rw [montgomery_reduce_eq]
  step -grind -threadGrindState as ⟨i3, n1, i8, n2, i15, n3, i24, n4, n5, n6, n7, i65, carry8, n8,
      h_i3, h_i8, h_i15, h_i24, h_i65, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hc8, n0, hn0,
      h_adjust⟩ by
    exact fun i hi => h_bounds i (by omega)
  -- The extract phase is specified for the actual `constants.L` limbs.
  simp only [h_i3, h_i8, h_i15, h_i24, h_i65]
  step -grind -threadGrindState as ⟨r0, r1, r2, r3, r4, r5, r6, carry16, r7, hr0, hr1, hr2, hr3,
      hr4, hr5, hr6, hr7, h_extract⟩ by
    exact fun i _ hi => h_bounds i hi
  -- Assemble the exact quotient before narrowing the top carry.
  let adjustment : Scalar29 := Array.make 9#usize [n0, n1, n2, n3, n4, n5, n6, n7, n8]
  let quotient : Nat := r0.val + limbRadix * r1.val + limbRadix ^ 2 * r2.val +
    limbRadix ^ 3 * r3.val + limbRadix ^ 4 * r4.val + limbRadix ^ 5 * r5.val +
    limbRadix ^ 6 * r6.val + limbRadix ^ 7 * r7.val + limbRadix ^ 8 * carry16.val
  have h_adjustment : asNat adjustment < montgomeryRadix :=
    asNat_bounded adjustment
      (isNormalized_make n0 n1 n2 n3 n4 n5 n6 n7 n8 hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8)
  have h_identity : wideAsNat limbs + asNat adjustment * order = quotient * montgomeryRadix := by
    -- Weighting the extract identity by `limbRadix ^ 9` and adding the adjust identity
    -- recovers the full Montgomery identity.
    rw [wideAsNat_split, asNat_mul_order_split, montgomeryRadix_eq]
    simp only [adjustment, quotient, Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
      List.getElem!_cons_succ]
    zify at h_adjust h_extract ⊢
    linear_combination h_adjust + (limbRadix : Int) ^ 9 * h_extract
  have h_quotient : quotient < 2 * order := quotient_lt_two_order h_range h_adjustment h_identity
  have h_top_weight : limbRadix ^ 8 * carry16.val ≤ quotient := Nat.le_add_left _ _
  have h_top : carry16.val < 2 ^ 22 := top_limb_lt h_quotient h_top_weight
  step -grind -threadGrindState with UScalar.cast_inBounds_spec as ⟨r8, h_r8⟩ by
    rw [UScalar.max_UScalarTy_U32_eq, U32.max_eq]
    exact h_top.le.trans (by decide)
  let pre : Scalar29 := Array.make 9#usize [r0, r1, r2, r3, r4, r5, r6, r7, r8]
  have h_pre : asNat pre = quotient := by
    simp only [pre, asNat, Array.uScalarToNatRadix, UScalar.ofNatCore_val_eq,
      pow_mul, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
      List.getElem!_cons_succ, quotient, limbRadix, h_r8, pow_zero, pow_one, one_mul]
  have h_r8_bound : r8.val < limbRadix := by
    rw [h_r8]
    exact h_top.trans (by decide)
  have h_normalized : IsNormalized pre :=
    isNormalized_make r0 r1 r2 r3 r4 r5 r6 r7 r8 hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 h_r8_bound
  have h_L : IsNormalized constants.L := constants.L_limbs_lt
  have h_lower : asNat constants.L ≤ asNat pre + order := by
    rw [constants.L_spec]
    omega
  have h_upper : asNat pre < asNat constants.L + order := by
    rw [constants.L_spec, h_pre]
    omega
  step* -grind -threadGrindState
  have h_residue : asNat result % order = quotient % order := by
    rw [constants.L_spec, h_pre] at result_post2
    simpa only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod] using result_post2
  have h_scaled : (quotient * montgomeryRadix) % order = wideAsNat limbs % order := by
    have h := congrArg (fun n : Nat => n % order) h_identity
    simpa only [Nat.add_mul_mod_self_right] using h.symm
  refine ⟨?_, result_post1, result_post3⟩
  calc
    (asNat result * montgomeryRadix) % order =
        ((asNat result % order) * (montgomeryRadix % order)) % order := Nat.mul_mod _ _ _
    _ = ((quotient % order) * (montgomeryRadix % order)) % order := by rw [h_residue]
    _ = (quotient * montgomeryRadix) % order := (Nat.mul_mod _ _ _).symm
    _ = wideAsNat limbs % order := h_scaled

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

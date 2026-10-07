/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.Field.square_inner.M

/-!
# Spec theorem for `square_inner`

`square_inner self` is the optimised squaring kernel of `FieldElement2625`. It computes the ten
`u64` coefficients of `self ^ 2` in the alternating `2^26/2^25` radix, folding the upper half of
the schoolbook product back into the lower limbs scaled by `19` (using that
`2 ^ 255 ≡ 19 [MOD p]`), so the result represents `self ^ 2` modulo `p`.

Source: "curve25519-dalek/src/backend/serial/u32/field.rs", lines 551:4-592:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/- `square_inner` is split into its ten coefficient blocks; each block is specified on its own so
that no single declaration carries the full symbolic-execution context. -/
set_option linter.hashCommand false in
#decompose square_inner square_inner_decomp
  letRange 24 12 => squareInnerCoeff0
  letRange 26 10 => squareInnerCoeff1
  letRange 28 12 => squareInnerCoeff2
  letRange 30 10 => squareInnerCoeff3
  letRange 32 12 => squareInnerCoeff4
  letRange 34 10 => squareInnerCoeff5
  letRange 36 12 => squareInnerCoeff6
  letRange 38 10 => squareInnerCoeff7
  letRange 40 12 => squareInnerCoeff8
  letRange 42 9 => squareInnerCoeff9

/-- Coefficient `0` of `square_inner`: its exact value and a bound below `267 * 2 ^ 54`. -/
@[local step]
private theorem squareInnerCoeff0_spec
    (x0 x1_2 x2_2 x3_2 x4_2 x5 x5_19 x6_19 x7_19 x8_19 x9_19 : U32)
    (hx0 : x0.val ≤ 2 ^ 27 - 1) (hx1_2 : x1_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx2_2 : x2_2.val ≤ 2 * (2 ^ 27 - 1)) (hx3_2 : x3_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx4_2 : x4_2.val ≤ 2 * (2 ^ 27 - 1)) (hx5 : x5.val ≤ 2 ^ 27 - 1)
    (hx5_19 : x5_19.val ≤ 19 * (2 ^ 27 - 1)) (hx6_19 : x6_19.val ≤ 19 * (2 ^ 27 - 1))
    (hx7_19 : x7_19.val ≤ 19 * (2 ^ 27 - 1)) (hx8_19 : x8_19.val ≤ 19 * (2 ^ 27 - 1))
    (hx9_19 : x9_19.val ≤ 19 * (2 ^ 27 - 1)) :
    squareInnerCoeff0 x0 x1_2 x2_2 x3_2 x4_2 x5 x5_19 x6_19 x7_19 x8_19 x9_19 ⦃ (r : U64) =>
      r.val = x0.val * x0.val + x2_2.val * x8_19.val + x4_2.val * x6_19.val +
        (x1_2.val * x9_19.val + x3_2.val * x7_19.val + x5.val * x5_19.val) * 2 ∧
      r.val < 267 * 2 ^ 54 ⦄ := by
  unfold squareInnerCoeff0
  repeat' first
    | (step with square_inner.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
    | (step with U64.mul_spec as ⟨twice, h_twice⟩
       have h_twice_bound := h_twice.trans_le (Nat.mul_le_mul ‹_› (le_refl _)))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `1` of `square_inner`: its exact value and a bound below `267 * 2 ^ 54`. -/
@[local step]
private theorem squareInnerCoeff1_spec
    (x0_2 x1 x2 x3_2 x4 x5_2 x6_19 x7_19 x8_19 x9_19 : U32)
    (hx0_2 : x0_2.val ≤ 2 * (2 ^ 27 - 1)) (hx1 : x1.val ≤ 2 ^ 27 - 1)
    (hx2 : x2.val ≤ 2 ^ 27 - 1) (hx3_2 : x3_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx4 : x4.val ≤ 2 ^ 27 - 1) (hx5_2 : x5_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx6_19 : x6_19.val ≤ 19 * (2 ^ 27 - 1)) (hx7_19 : x7_19.val ≤ 19 * (2 ^ 27 - 1))
    (hx8_19 : x8_19.val ≤ 19 * (2 ^ 27 - 1)) (hx9_19 : x9_19.val ≤ 19 * (2 ^ 27 - 1)) :
    squareInnerCoeff1 x0_2 x1 x2 x3_2 x4 x5_2 x6_19 x7_19 x8_19 x9_19 ⦃ (r : U64) =>
      r.val = x0_2.val * x1.val + x3_2.val * x8_19.val + x5_2.val * x6_19.val +
        (x2.val * x9_19.val + x4.val * x7_19.val) * 2 ∧
      r.val < 267 * 2 ^ 54 ⦄ := by
  unfold squareInnerCoeff1
  repeat' first
    | (step with square_inner.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
    | (step with U64.mul_spec as ⟨twice, h_twice⟩
       have h_twice_bound := h_twice.trans_le (Nat.mul_le_mul ‹_› (le_refl _)))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `2` of `square_inner`: its exact value and a bound below `267 * 2 ^ 54`. -/
@[local step]
private theorem squareInnerCoeff2_spec
    (x0_2 x1 x1_2 x2 x3_2 x4_2 x5_2 x6 x6_19 x7_19 x8_19 x9_19 : U32)
    (hx0_2 : x0_2.val ≤ 2 * (2 ^ 27 - 1)) (hx1 : x1.val ≤ 2 ^ 27 - 1)
    (hx1_2 : x1_2.val ≤ 2 * (2 ^ 27 - 1)) (hx2 : x2.val ≤ 2 ^ 27 - 1)
    (hx3_2 : x3_2.val ≤ 2 * (2 ^ 27 - 1)) (hx4_2 : x4_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx5_2 : x5_2.val ≤ 2 * (2 ^ 27 - 1)) (hx6 : x6.val ≤ 2 ^ 27 - 1)
    (hx6_19 : x6_19.val ≤ 19 * (2 ^ 27 - 1)) (hx7_19 : x7_19.val ≤ 19 * (2 ^ 27 - 1))
    (hx8_19 : x8_19.val ≤ 19 * (2 ^ 27 - 1)) (hx9_19 : x9_19.val ≤ 19 * (2 ^ 27 - 1)) :
    squareInnerCoeff2 x0_2 x1 x1_2 x2 x3_2 x4_2 x5_2 x6 x6_19 x7_19 x8_19 x9_19 ⦃ (r : U64) =>
      r.val = x0_2.val * x2.val + x1_2.val * x1.val + x4_2.val * x8_19.val +
        x6.val * x6_19.val + (x3_2.val * x9_19.val + x5_2.val * x7_19.val) * 2 ∧
      r.val < 267 * 2 ^ 54 ⦄ := by
  unfold squareInnerCoeff2
  repeat' first
    | (step with square_inner.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
    | (step with U64.mul_spec as ⟨twice, h_twice⟩
       have h_twice_bound := h_twice.trans_le (Nat.mul_le_mul ‹_› (le_refl _)))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `3` of `square_inner`: its exact value and a bound below `267 * 2 ^ 54`. -/
@[local step]
private theorem squareInnerCoeff3_spec
    (x0_2 x1_2 x2 x3 x4 x5_2 x6 x7_19 x8_19 x9_19 : U32)
    (hx0_2 : x0_2.val ≤ 2 * (2 ^ 27 - 1)) (hx1_2 : x1_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx2 : x2.val ≤ 2 ^ 27 - 1) (hx3 : x3.val ≤ 2 ^ 27 - 1) (hx4 : x4.val ≤ 2 ^ 27 - 1)
    (hx5_2 : x5_2.val ≤ 2 * (2 ^ 27 - 1)) (hx6 : x6.val ≤ 2 ^ 27 - 1)
    (hx7_19 : x7_19.val ≤ 19 * (2 ^ 27 - 1)) (hx8_19 : x8_19.val ≤ 19 * (2 ^ 27 - 1))
    (hx9_19 : x9_19.val ≤ 19 * (2 ^ 27 - 1)) :
    squareInnerCoeff3 x0_2 x1_2 x2 x3 x4 x5_2 x6 x7_19 x8_19 x9_19 ⦃ (r : U64) =>
      r.val = x0_2.val * x3.val + x1_2.val * x2.val + x5_2.val * x8_19.val +
        (x4.val * x9_19.val + x6.val * x7_19.val) * 2 ∧
      r.val < 267 * 2 ^ 54 ⦄ := by
  unfold squareInnerCoeff3
  repeat' first
    | (step with square_inner.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
    | (step with U64.mul_spec as ⟨twice, h_twice⟩
       have h_twice_bound := h_twice.trans_le (Nat.mul_le_mul ‹_› (le_refl _)))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `4` of `square_inner`: its exact value and a bound below `267 * 2 ^ 54`. -/
@[local step]
private theorem squareInnerCoeff4_spec
    (x0_2 x1_2 x2 x3_2 x4 x5_2 x6_2 x7 x7_19 x8_19 x9_19 : U32)
    (hx0_2 : x0_2.val ≤ 2 * (2 ^ 27 - 1)) (hx1_2 : x1_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx2 : x2.val ≤ 2 ^ 27 - 1) (hx3_2 : x3_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx4 : x4.val ≤ 2 ^ 27 - 1) (hx5_2 : x5_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx6_2 : x6_2.val ≤ 2 * (2 ^ 27 - 1)) (hx7 : x7.val ≤ 2 ^ 27 - 1)
    (hx7_19 : x7_19.val ≤ 19 * (2 ^ 27 - 1)) (hx8_19 : x8_19.val ≤ 19 * (2 ^ 27 - 1))
    (hx9_19 : x9_19.val ≤ 19 * (2 ^ 27 - 1)) :
    squareInnerCoeff4 x0_2 x1_2 x2 x3_2 x4 x5_2 x6_2 x7 x7_19 x8_19 x9_19 ⦃ (r : U64) =>
      r.val = x0_2.val * x4.val + x1_2.val * x3_2.val + x2.val * x2.val +
        x6_2.val * x8_19.val + (x5_2.val * x9_19.val + x7.val * x7_19.val) * 2 ∧
      r.val < 267 * 2 ^ 54 ⦄ := by
  unfold squareInnerCoeff4
  repeat' first
    | (step with square_inner.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
    | (step with U64.mul_spec as ⟨twice, h_twice⟩
       have h_twice_bound := h_twice.trans_le (Nat.mul_le_mul ‹_› (le_refl _)))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `5` of `square_inner`: its exact value and a bound below `267 * 2 ^ 54`. -/
@[local step]
private theorem squareInnerCoeff5_spec
    (x0_2 x1_2 x2_2 x3 x4 x5 x6 x7_2 x8_19 x9_19 : U32)
    (hx0_2 : x0_2.val ≤ 2 * (2 ^ 27 - 1)) (hx1_2 : x1_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx2_2 : x2_2.val ≤ 2 * (2 ^ 27 - 1)) (hx3 : x3.val ≤ 2 ^ 27 - 1)
    (hx4 : x4.val ≤ 2 ^ 27 - 1) (hx5 : x5.val ≤ 2 ^ 27 - 1) (hx6 : x6.val ≤ 2 ^ 27 - 1)
    (hx7_2 : x7_2.val ≤ 2 * (2 ^ 27 - 1)) (hx8_19 : x8_19.val ≤ 19 * (2 ^ 27 - 1))
    (hx9_19 : x9_19.val ≤ 19 * (2 ^ 27 - 1)) :
    squareInnerCoeff5 x0_2 x1_2 x2_2 x3 x4 x5 x6 x7_2 x8_19 x9_19 ⦃ (r : U64) =>
      r.val = x0_2.val * x5.val + x1_2.val * x4.val + x2_2.val * x3.val +
        x7_2.val * x8_19.val + x6.val * x9_19.val * 2 ∧
      r.val < 267 * 2 ^ 54 ⦄ := by
  unfold squareInnerCoeff5
  repeat' first
    | (step with square_inner.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
    | (step with U64.mul_spec as ⟨twice, h_twice⟩
       have h_twice_bound := h_twice.trans_le (Nat.mul_le_mul ‹_› (le_refl _)))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `6` of `square_inner`: its exact value and a bound below `267 * 2 ^ 54`. -/
@[local step]
private theorem squareInnerCoeff6_spec
    (x0_2 x1_2 x2_2 x3 x3_2 x4 x5_2 x6 x7_2 x8 x8_19 x9_19 : U32)
    (hx0_2 : x0_2.val ≤ 2 * (2 ^ 27 - 1)) (hx1_2 : x1_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx2_2 : x2_2.val ≤ 2 * (2 ^ 27 - 1)) (hx3 : x3.val ≤ 2 ^ 27 - 1)
    (hx3_2 : x3_2.val ≤ 2 * (2 ^ 27 - 1)) (hx4 : x4.val ≤ 2 ^ 27 - 1)
    (hx5_2 : x5_2.val ≤ 2 * (2 ^ 27 - 1)) (hx6 : x6.val ≤ 2 ^ 27 - 1)
    (hx7_2 : x7_2.val ≤ 2 * (2 ^ 27 - 1)) (hx8 : x8.val ≤ 2 ^ 27 - 1)
    (hx8_19 : x8_19.val ≤ 19 * (2 ^ 27 - 1)) (hx9_19 : x9_19.val ≤ 19 * (2 ^ 27 - 1)) :
    squareInnerCoeff6 x0_2 x1_2 x2_2 x3 x3_2 x4 x5_2 x6 x7_2 x8 x8_19 x9_19 ⦃ (r : U64) =>
      r.val = x0_2.val * x6.val + x1_2.val * x5_2.val + x2_2.val * x4.val +
        x3_2.val * x3.val + x8.val * x8_19.val + x7_2.val * x9_19.val * 2 ∧
      r.val < 267 * 2 ^ 54 ⦄ := by
  unfold squareInnerCoeff6
  repeat' first
    | (step with square_inner.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
    | (step with U64.mul_spec as ⟨twice, h_twice⟩
       have h_twice_bound := h_twice.trans_le (Nat.mul_le_mul ‹_› (le_refl _)))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `7` of `square_inner`: its exact value and a bound below `267 * 2 ^ 54`. -/
@[local step]
private theorem squareInnerCoeff7_spec
    (x0_2 x1_2 x2_2 x3_2 x4 x5 x6 x7 x8 x9_19 : U32)
    (hx0_2 : x0_2.val ≤ 2 * (2 ^ 27 - 1)) (hx1_2 : x1_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx2_2 : x2_2.val ≤ 2 * (2 ^ 27 - 1)) (hx3_2 : x3_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx4 : x4.val ≤ 2 ^ 27 - 1) (hx5 : x5.val ≤ 2 ^ 27 - 1) (hx6 : x6.val ≤ 2 ^ 27 - 1)
    (hx7 : x7.val ≤ 2 ^ 27 - 1) (hx8 : x8.val ≤ 2 ^ 27 - 1)
    (hx9_19 : x9_19.val ≤ 19 * (2 ^ 27 - 1)) :
    squareInnerCoeff7 x0_2 x1_2 x2_2 x3_2 x4 x5 x6 x7 x8 x9_19 ⦃ (r : U64) =>
      r.val = x0_2.val * x7.val + x1_2.val * x6.val + x2_2.val * x5.val +
        x3_2.val * x4.val + x8.val * x9_19.val * 2 ∧
      r.val < 267 * 2 ^ 54 ⦄ := by
  unfold squareInnerCoeff7
  repeat' first
    | (step with square_inner.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
    | (step with U64.mul_spec as ⟨twice, h_twice⟩
       have h_twice_bound := h_twice.trans_le (Nat.mul_le_mul ‹_› (le_refl _)))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `8` of `square_inner`: its exact value and a bound below `267 * 2 ^ 54`. -/
@[local step]
private theorem squareInnerCoeff8_spec
    (x0_2 x1_2 x2_2 x3_2 x4 x5_2 x6 x7_2 x8 x9 x9_19 : U32)
    (hx0_2 : x0_2.val ≤ 2 * (2 ^ 27 - 1)) (hx1_2 : x1_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx2_2 : x2_2.val ≤ 2 * (2 ^ 27 - 1)) (hx3_2 : x3_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx4 : x4.val ≤ 2 ^ 27 - 1) (hx5_2 : x5_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx6 : x6.val ≤ 2 ^ 27 - 1) (hx7_2 : x7_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx8 : x8.val ≤ 2 ^ 27 - 1) (hx9 : x9.val ≤ 2 ^ 27 - 1)
    (hx9_19 : x9_19.val ≤ 19 * (2 ^ 27 - 1)) :
    squareInnerCoeff8 x0_2 x1_2 x2_2 x3_2 x4 x5_2 x6 x7_2 x8 x9 x9_19 ⦃ (r : U64) =>
      r.val = x0_2.val * x8.val + x1_2.val * x7_2.val + x2_2.val * x6.val +
        x3_2.val * x5_2.val + x4.val * x4.val + x9.val * x9_19.val * 2 ∧
      r.val < 267 * 2 ^ 54 ⦄ := by
  unfold squareInnerCoeff8
  repeat' first
    | (step with square_inner.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
    | (step with U64.mul_spec as ⟨twice, h_twice⟩
       have h_twice_bound := h_twice.trans_le (Nat.mul_le_mul ‹_› (le_refl _)))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `9` of `square_inner`: its exact value and a bound below `267 * 2 ^ 54`. -/
@[local step]
private theorem squareInnerCoeff9_spec
    (x0_2 x1_2 x2_2 x3_2 x4_2 x5 x6 x7 x8 x9 : U32)
    (hx0_2 : x0_2.val ≤ 2 * (2 ^ 27 - 1)) (hx1_2 : x1_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx2_2 : x2_2.val ≤ 2 * (2 ^ 27 - 1)) (hx3_2 : x3_2.val ≤ 2 * (2 ^ 27 - 1))
    (hx4_2 : x4_2.val ≤ 2 * (2 ^ 27 - 1)) (hx5 : x5.val ≤ 2 ^ 27 - 1)
    (hx6 : x6.val ≤ 2 ^ 27 - 1) (hx7 : x7.val ≤ 2 ^ 27 - 1) (hx8 : x8.val ≤ 2 ^ 27 - 1)
    (hx9 : x9.val ≤ 2 ^ 27 - 1) :
    squareInnerCoeff9 x0_2 x1_2 x2_2 x3_2 x4_2 x5 x6 x7 x8 x9 ⦃ (r : U64) =>
      r.val = x0_2.val * x9.val + x1_2.val * x8.val + x2_2.val * x7.val +
        x3_2.val * x6.val + x4_2.val * x5.val ∧
      r.val < 267 * 2 ^ 54 ⦄ := by
  unfold squareInnerCoeff9
  repeat' first
    | (step with square_inner.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

private theorem index_eq (a : FieldElement2625) (j : Usize) (h_j : j.val < 10) :
    Array.index_usize a j = ok a[j.val]! := by
  obtain ⟨r, h_eq, h_r⟩ := spec_imp_exists (Array.index_usize_spec a j (by scalar_tac))
  have h_len : j.val < a.val.length := by scalar_tac
  rw [h_eq, h_r]
  simp [List.getElem?_eq_getElem h_len]

/-- The ten-slot output array written by `square_inner`. -/
private abbrev outArray (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : U64) : Array U64 10#usize :=
  ((((((((((Array.repeat 10#usize 0#u64).set 0#usize a0).set 1#usize a1).set 2#usize a2).set
    3#usize a3).set 4#usize a4).set 5#usize a5).set 6#usize a6).set 7#usize a7).set
    8#usize a8).set 9#usize a9

private theorem outArray_bound (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : U64) (B : Nat)
    (h0 : a0.val < B) (h1 : a1.val < B) (h2 : a2.val < B) (h3 : a3.val < B)
    (h4 : a4.val < B) (h5 : a5.val < B) (h6 : a6.val < B) (h7 : a7.val < B)
    (h8 : a8.val < B) (h9 : a9.val < B) :
    ∀ i, i < 10 → (outArray a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)[i]!.val < B := by
  intro i hi
  rewrite [← Finset.mem_range] at hi
  fin_cases hi
  · simp_lists; exact h0
  · simp_lists; exact h1
  · simp_lists; exact h2
  · simp_lists; exact h3
  · simp_lists; exact h4
  · simp_lists; exact h5
  · simp_lists; exact h6
  · simp_lists; exact h7
  · simp_lists; exact h8
  · simp_lists; exact h9

private theorem outArray_toNat (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : U64) :
    (outArray a0 a1 a2 a3 a4 a5 a6 a7 a8 a9).uScalarToNatField2625 =
      a0.val + 2 ^ 26 * a1.val + 2 ^ 51 * a2.val + 2 ^ 77 * a3.val + 2 ^ 102 * a4.val +
        2 ^ 128 * a5.val + 2 ^ 153 * a6.val + 2 ^ 179 * a7.val + 2 ^ 204 * a8.val +
        2 ^ 230 * a9.val := by
  simp only [Array.uScalarToNatField2625, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add]
  simp_lists
  norm_num

private theorem toNat_expand (x : FieldElement2625) :
    x.toNat =
      x[0]!.val + 2 ^ 26 * x[1]!.val + 2 ^ 51 * x[2]!.val + 2 ^ 77 * x[3]!.val +
        2 ^ 102 * x[4]!.val + 2 ^ 128 * x[5]!.val + 2 ^ 153 * x[6]!.val +
        2 ^ 179 * x[7]!.val + 2 ^ 204 * x[8]!.val + 2 ^ 230 * x[9]!.val := by
  simp only [toNat_eq, Array.uScalarToNatField2625, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  norm_num

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::square_inner`**

If every limb of `self` is below `2 ^ 27` (enough for the unreduced sum of two reduced field
elements, and keeping every `19 * self[i]` below `2 ^ 32`), the function succeeds and returns ten
coefficients congruent to `self ^ 2` modulo `p`. Each coefficient is below `267 * 2 ^ 54` (the
worst case is limb `0`), which is at most `2 ^ 63 - 2 ^ 38`, so even after the doubling in
`square2` it meets the `2 ^ 64 - 2 ^ 39` precondition of `reduce_spec`. -/
@[step]
theorem square_inner_spec (self : FieldElement2625)
    (h_self : ∀ i, i < 10 → self[i]!.val < 2 ^ 27) :
    square_inner self ⦃ (result : Array U64 10#usize) =>
      result.uScalarToNatField2625 % p = self.toNat ^ 2 % p ∧
      (∀ i, i < 10 → result[i]!.val < 267 * 2 ^ 54) ⦄ := by
  have h0 : self[0]!.val ≤ 2 ^ 27 - 1 := Nat.le_pred_of_lt (h_self 0 (by decide))
  have h1 : self[1]!.val ≤ 2 ^ 27 - 1 := Nat.le_pred_of_lt (h_self 1 (by decide))
  have h2 : self[2]!.val ≤ 2 ^ 27 - 1 := Nat.le_pred_of_lt (h_self 2 (by decide))
  have h3 : self[3]!.val ≤ 2 ^ 27 - 1 := Nat.le_pred_of_lt (h_self 3 (by decide))
  have h4 : self[4]!.val ≤ 2 ^ 27 - 1 := Nat.le_pred_of_lt (h_self 4 (by decide))
  have h5 : self[5]!.val ≤ 2 ^ 27 - 1 := Nat.le_pred_of_lt (h_self 5 (by decide))
  have h6 : self[6]!.val ≤ 2 ^ 27 - 1 := Nat.le_pred_of_lt (h_self 6 (by decide))
  have h7 : self[7]!.val ≤ 2 ^ 27 - 1 := Nat.le_pred_of_lt (h_self 7 (by decide))
  have h8 : self[8]!.val ≤ 2 ^ 27 - 1 := Nat.le_pred_of_lt (h_self 8 (by decide))
  have h9 : self[9]!.val ≤ 2 ^ 27 - 1 := Nat.le_pred_of_lt (h_self 9 (by decide))
  clear h_self
  rewrite [square_inner_decomp]
  simp only [index_eq, Nat.reduceLT, UScalar.ofNatCore_val_eq, bind_tc_ok]
  step*
  simp only [result_post, z9_post, z8_post, z7_post, z6_post, z5_post, z4_post, z3_post,
    z2_post, z1_post]
  constructor
  · rw [outArray_toNat, toNat_expand]
    simp only [*]
    have h19 : (19 : ZMod p) = 2 ^ 255 := by
      have h := congrArg (Nat.cast : ℕ → ZMod p) p_add_19
      rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_ofNat] at h
      exact h
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [h19]
    ring
  · exact outArray_bound _ _ _ _ _ _ _ _ _ _ _
      ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

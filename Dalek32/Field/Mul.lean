/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.Field.Reduce
import Dalek32.Field.mul.M

/-!
# Spec theorem for `mul`

`mul self _rhs` multiplies two `FieldElement2625`s. It precomputes `19 * y[j]` for `j ≥ 1` and
`2 * x[i]` for odd `i`, forms the ten `u64` coefficients `z0, …, z9` of the schoolbook product in
the alternating `2^26/2^25` radix, where the upper half is folded back into the lower limbs scaled
by `19` (using that `2 ^ 255 ≡ 19 [MOD p]`), and finally calls `reduce`. The result therefore
represents `self * _rhs` modulo `p`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 128:4-227:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.SharedAFieldElement2625.Insts
namespace CoreOpsArithMulSharedBFieldElement2625FieldElement2625

open backend.serial.u32.field.MulSharedAFieldElement2625SharedBFieldElement2625FieldElement2625

/- `mul` is split into its ten coefficient blocks; each block is specified on its own so that no
single declaration carries the full symbolic-execution context. The code reads the even limbs
`2, 4, 6, 8` of `self` in the middle of the sum for `z0` and the later blocks reuse them, so
`mulCoeff0` returns the tuple `(x2, x4, x6, x8, z0)`. -/
set_option linter.hashCommand false in
#decompose mul mul_decomp
  letRange 30 23 => mulCoeff0
  letRange 31 19 => mulCoeff1
  letRange 32 19 => mulCoeff2
  letRange 33 19 => mulCoeff3
  letRange 34 19 => mulCoeff4
  letRange 35 19 => mulCoeff5
  letRange 36 19 => mulCoeff6
  letRange 37 19 => mulCoeff7
  letRange 38 19 => mulCoeff8
  letRange 39 19 => mulCoeff9

/-- Coefficient `0` block of `mul`: reads the even limbs `2, 4, 6, 8` of `self`, which it returns
alongside `z0`, and sums the products of limbs and precomputed limb multiples that make up the
`u64` coefficient `z0`. -/
add_decl_doc mulCoeff0

/-- Coefficient `1` block of `mul`: sums the products of limbs and precomputed limb multiples
that make up the `u64` coefficient `z1`. -/
add_decl_doc mulCoeff1

/-- Coefficient `2` block of `mul`: sums the products of limbs and precomputed limb multiples
that make up the `u64` coefficient `z2`. -/
add_decl_doc mulCoeff2

/-- Coefficient `3` block of `mul`: sums the products of limbs and precomputed limb multiples
that make up the `u64` coefficient `z3`. -/
add_decl_doc mulCoeff3

/-- Coefficient `4` block of `mul`: sums the products of limbs and precomputed limb multiples
that make up the `u64` coefficient `z4`. -/
add_decl_doc mulCoeff4

/-- Coefficient `5` block of `mul`: sums the products of limbs and precomputed limb multiples
that make up the `u64` coefficient `z5`. -/
add_decl_doc mulCoeff5

/-- Coefficient `6` block of `mul`: sums the products of limbs and precomputed limb multiples
that make up the `u64` coefficient `z6`. -/
add_decl_doc mulCoeff6

/-- Coefficient `7` block of `mul`: sums the products of limbs and precomputed limb multiples
that make up the `u64` coefficient `z7`. -/
add_decl_doc mulCoeff7

/-- Coefficient `8` block of `mul`: sums the products of limbs and precomputed limb multiples
that make up the `u64` coefficient `z8`. -/
add_decl_doc mulCoeff8

/-- Coefficient `9` block of `mul`: sums the products of limbs and precomputed limb multiples
that make up the `u64` coefficient `z9`. -/
add_decl_doc mulCoeff9

/-- Coefficient `0` of `mul`: the even limbs of `self` it reads, its exact value and the bound
`r < 2403 * 2 ^ 52 = 267 * (3 * 2 ^ 26) ^ 2`, which `z0` attains as the worst case over all ten
coefficients. After `index_usize_eq` resolves the limb reads, each `mul.m` and `U64.add` is stepped
with `mul.m_spec` or `U64.add_spec`, chaining their bounds with `Nat.mul_le_mul` and
`Nat.add_le_add`; `simp only [*]` gives the value and `norm_num` the bound. -/
@[local step]
private theorem mulCoeff0_spec (self : FieldElement2625)
    (y1_19 y2_19 y3_19 y4_19 y5_19 y6_19 y7_19 y8_19 y9_19 x1_2 x3_2 x5_2 x7_2 x9_2 x0 y0 : U32)
    (hy1_19 : y1_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy2_19 : y2_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy3_19 : y3_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy4_19 : y4_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy5_19 : y5_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy6_19 : y6_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy7_19 : y7_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy8_19 : y8_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy9_19 : y9_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hx1_2 : x1_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx3_2 : x3_2.val ≤ 2 * (3 * 2 ^ 26 - 1)) (hx5_2 : x5_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx7_2 : x7_2.val ≤ 2 * (3 * 2 ^ 26 - 1)) (hx9_2 : x9_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx0 : x0.val ≤ 3 * 2 ^ 26 - 1) (hy0 : y0.val ≤ 3 * 2 ^ 26 - 1)
    (hx2 : self[2]!.val ≤ 3 * 2 ^ 26 - 1) (hx4 : self[4]!.val ≤ 3 * 2 ^ 26 - 1)
    (hx6 : self[6]!.val ≤ 3 * 2 ^ 26 - 1) (hx8 : self[8]!.val ≤ 3 * 2 ^ 26 - 1) :
    mulCoeff0 self y1_19 y2_19 y3_19 y4_19 y5_19 y6_19 y7_19 y8_19 y9_19 x1_2 x3_2 x5_2 x7_2 x9_2
      x0 y0 ⦃ (x2 : U32) (x4 : U32) (x6 : U32) (x8 : U32) (r : U64) =>
      x2.val = self[2]!.val ∧ x4.val = self[4]!.val ∧ x6.val = self[6]!.val ∧
      x8.val = self[8]!.val ∧
      r.val = x0.val * y0.val + x1_2.val * y9_19.val + self[2]!.val * y8_19.val +
        x3_2.val * y7_19.val + self[4]!.val * y6_19.val + x5_2.val * y5_19.val +
        self[6]!.val * y4_19.val + x7_2.val * y3_19.val + self[8]!.val * y2_19.val +
        x9_2.val * y1_19.val ∧
      r.val < 2403 * 2 ^ 52 ⦄ := by
  unfold mulCoeff0
  simp only [FieldElement2625.index_usize_eq, Nat.reduceLT, UScalar.ofNatCore_val_eq, bind_tc_ok]
  repeat' first
    | (step with mul.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `1` of `mul`: its exact value and the shared bound `r < 2403 * 2 ^ 52`, proved
like `mulCoeff0_spec` but without the limb reads. -/
@[local step]
private theorem mulCoeff1_spec (y1 y2_19 y3_19 y4_19 y5_19 y6_19 y7_19 y8_19 y9_19 x1 x3 x5 x7 x9
    x0 y0 x2 x4 x6 x8 : U32)
    (hy1 : y1.val ≤ 3 * 2 ^ 26 - 1) (hy2_19 : y2_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy3_19 : y3_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy4_19 : y4_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy5_19 : y5_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy6_19 : y6_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy7_19 : y7_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy8_19 : y8_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy9_19 : y9_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hx1 : x1.val ≤ 3 * 2 ^ 26 - 1)
    (hx3 : x3.val ≤ 3 * 2 ^ 26 - 1) (hx5 : x5.val ≤ 3 * 2 ^ 26 - 1)
    (hx7 : x7.val ≤ 3 * 2 ^ 26 - 1) (hx9 : x9.val ≤ 3 * 2 ^ 26 - 1)
    (hx0 : x0.val ≤ 3 * 2 ^ 26 - 1) (hy0 : y0.val ≤ 3 * 2 ^ 26 - 1)
    (hx2 : x2.val ≤ 3 * 2 ^ 26 - 1) (hx4 : x4.val ≤ 3 * 2 ^ 26 - 1)
    (hx6 : x6.val ≤ 3 * 2 ^ 26 - 1) (hx8 : x8.val ≤ 3 * 2 ^ 26 - 1) :
    mulCoeff1 y1 y2_19 y3_19 y4_19 y5_19 y6_19 y7_19 y8_19 y9_19 x1 x3 x5 x7 x9 x0 y0 x2 x4 x6 x8
      ⦃ (r : U64) =>
      r.val = x0.val * y1.val + x1.val * y0.val + x2.val * y9_19.val + x3.val * y8_19.val +
        x4.val * y7_19.val + x5.val * y6_19.val + x6.val * y5_19.val + x7.val * y4_19.val +
        x8.val * y3_19.val + x9.val * y2_19.val ∧
      r.val < 2403 * 2 ^ 52 ⦄ := by
  unfold mulCoeff1
  repeat' first
    | (step with mul.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `2` of `mul`: its exact value and the shared bound `r < 2403 * 2 ^ 52`, proved
like `mulCoeff0_spec` but without the limb reads. -/
@[local step]
private theorem mulCoeff2_spec (y1 y2 y3_19 y4_19 y5_19 y6_19 y7_19 y8_19 y9_19 x1_2 x3_2 x5_2
    x7_2 x9_2 x0 y0 x2 x4 x6 x8 : U32)
    (hy1 : y1.val ≤ 3 * 2 ^ 26 - 1) (hy2 : y2.val ≤ 3 * 2 ^ 26 - 1)
    (hy3_19 : y3_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy4_19 : y4_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy5_19 : y5_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy6_19 : y6_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy7_19 : y7_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy8_19 : y8_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy9_19 : y9_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hx1_2 : x1_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx3_2 : x3_2.val ≤ 2 * (3 * 2 ^ 26 - 1)) (hx5_2 : x5_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx7_2 : x7_2.val ≤ 2 * (3 * 2 ^ 26 - 1)) (hx9_2 : x9_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx0 : x0.val ≤ 3 * 2 ^ 26 - 1) (hy0 : y0.val ≤ 3 * 2 ^ 26 - 1)
    (hx2 : x2.val ≤ 3 * 2 ^ 26 - 1) (hx4 : x4.val ≤ 3 * 2 ^ 26 - 1)
    (hx6 : x6.val ≤ 3 * 2 ^ 26 - 1) (hx8 : x8.val ≤ 3 * 2 ^ 26 - 1) :
    mulCoeff2 y1 y2 y3_19 y4_19 y5_19 y6_19 y7_19 y8_19 y9_19 x1_2 x3_2 x5_2 x7_2 x9_2 x0 y0 x2
      x4 x6 x8 ⦃ (r : U64) =>
      r.val = x0.val * y2.val + x1_2.val * y1.val + x2.val * y0.val + x3_2.val * y9_19.val +
        x4.val * y8_19.val + x5_2.val * y7_19.val + x6.val * y6_19.val + x7_2.val * y5_19.val +
        x8.val * y4_19.val + x9_2.val * y3_19.val ∧
      r.val < 2403 * 2 ^ 52 ⦄ := by
  unfold mulCoeff2
  repeat' first
    | (step with mul.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `3` of `mul`: its exact value and the shared bound `r < 2403 * 2 ^ 52`, proved
like `mulCoeff0_spec` but without the limb reads. -/
@[local step]
private theorem mulCoeff3_spec (y1 y2 y3 y4_19 y5_19 y6_19 y7_19 y8_19 y9_19 x1 x3 x5 x7 x9 x0 y0
    x2 x4 x6 x8 : U32)
    (hy1 : y1.val ≤ 3 * 2 ^ 26 - 1) (hy2 : y2.val ≤ 3 * 2 ^ 26 - 1)
    (hy3 : y3.val ≤ 3 * 2 ^ 26 - 1) (hy4_19 : y4_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy5_19 : y5_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy6_19 : y6_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy7_19 : y7_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy8_19 : y8_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy9_19 : y9_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hx1 : x1.val ≤ 3 * 2 ^ 26 - 1)
    (hx3 : x3.val ≤ 3 * 2 ^ 26 - 1) (hx5 : x5.val ≤ 3 * 2 ^ 26 - 1)
    (hx7 : x7.val ≤ 3 * 2 ^ 26 - 1) (hx9 : x9.val ≤ 3 * 2 ^ 26 - 1)
    (hx0 : x0.val ≤ 3 * 2 ^ 26 - 1) (hy0 : y0.val ≤ 3 * 2 ^ 26 - 1)
    (hx2 : x2.val ≤ 3 * 2 ^ 26 - 1) (hx4 : x4.val ≤ 3 * 2 ^ 26 - 1)
    (hx6 : x6.val ≤ 3 * 2 ^ 26 - 1) (hx8 : x8.val ≤ 3 * 2 ^ 26 - 1) :
    mulCoeff3 y1 y2 y3 y4_19 y5_19 y6_19 y7_19 y8_19 y9_19 x1 x3 x5 x7 x9 x0 y0 x2 x4 x6 x8
      ⦃ (r : U64) =>
      r.val = x0.val * y3.val + x1.val * y2.val + x2.val * y1.val + x3.val * y0.val +
        x4.val * y9_19.val + x5.val * y8_19.val + x6.val * y7_19.val + x7.val * y6_19.val +
        x8.val * y5_19.val + x9.val * y4_19.val ∧
      r.val < 2403 * 2 ^ 52 ⦄ := by
  unfold mulCoeff3
  repeat' first
    | (step with mul.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `4` of `mul`: its exact value and the shared bound `r < 2403 * 2 ^ 52`, proved
like `mulCoeff0_spec` but without the limb reads. -/
@[local step]
private theorem mulCoeff4_spec (y1 y2 y3 y4 y5_19 y6_19 y7_19 y8_19 y9_19 x1_2 x3_2 x5_2 x7_2
    x9_2 x0 y0 x2 x4 x6 x8 : U32)
    (hy1 : y1.val ≤ 3 * 2 ^ 26 - 1) (hy2 : y2.val ≤ 3 * 2 ^ 26 - 1)
    (hy3 : y3.val ≤ 3 * 2 ^ 26 - 1) (hy4 : y4.val ≤ 3 * 2 ^ 26 - 1)
    (hy5_19 : y5_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy6_19 : y6_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy7_19 : y7_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy8_19 : y8_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy9_19 : y9_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hx1_2 : x1_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx3_2 : x3_2.val ≤ 2 * (3 * 2 ^ 26 - 1)) (hx5_2 : x5_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx7_2 : x7_2.val ≤ 2 * (3 * 2 ^ 26 - 1)) (hx9_2 : x9_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx0 : x0.val ≤ 3 * 2 ^ 26 - 1) (hy0 : y0.val ≤ 3 * 2 ^ 26 - 1)
    (hx2 : x2.val ≤ 3 * 2 ^ 26 - 1) (hx4 : x4.val ≤ 3 * 2 ^ 26 - 1)
    (hx6 : x6.val ≤ 3 * 2 ^ 26 - 1) (hx8 : x8.val ≤ 3 * 2 ^ 26 - 1) :
    mulCoeff4 y1 y2 y3 y4 y5_19 y6_19 y7_19 y8_19 y9_19 x1_2 x3_2 x5_2 x7_2 x9_2 x0 y0 x2 x4 x6
      x8 ⦃ (r : U64) =>
      r.val = x0.val * y4.val + x1_2.val * y3.val + x2.val * y2.val + x3_2.val * y1.val +
        x4.val * y0.val + x5_2.val * y9_19.val + x6.val * y8_19.val + x7_2.val * y7_19.val +
        x8.val * y6_19.val + x9_2.val * y5_19.val ∧
      r.val < 2403 * 2 ^ 52 ⦄ := by
  unfold mulCoeff4
  repeat' first
    | (step with mul.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `5` of `mul`: its exact value and the shared bound `r < 2403 * 2 ^ 52`, proved
like `mulCoeff0_spec` but without the limb reads. -/
@[local step]
private theorem mulCoeff5_spec (y1 y2 y3 y4 y5 y6_19 y7_19 y8_19 y9_19 x1 x3 x5 x7 x9 x0 y0 x2 x4
    x6 x8 : U32)
    (hy1 : y1.val ≤ 3 * 2 ^ 26 - 1) (hy2 : y2.val ≤ 3 * 2 ^ 26 - 1)
    (hy3 : y3.val ≤ 3 * 2 ^ 26 - 1) (hy4 : y4.val ≤ 3 * 2 ^ 26 - 1)
    (hy5 : y5.val ≤ 3 * 2 ^ 26 - 1) (hy6_19 : y6_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy7_19 : y7_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy8_19 : y8_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy9_19 : y9_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hx1 : x1.val ≤ 3 * 2 ^ 26 - 1)
    (hx3 : x3.val ≤ 3 * 2 ^ 26 - 1) (hx5 : x5.val ≤ 3 * 2 ^ 26 - 1)
    (hx7 : x7.val ≤ 3 * 2 ^ 26 - 1) (hx9 : x9.val ≤ 3 * 2 ^ 26 - 1)
    (hx0 : x0.val ≤ 3 * 2 ^ 26 - 1) (hy0 : y0.val ≤ 3 * 2 ^ 26 - 1)
    (hx2 : x2.val ≤ 3 * 2 ^ 26 - 1) (hx4 : x4.val ≤ 3 * 2 ^ 26 - 1)
    (hx6 : x6.val ≤ 3 * 2 ^ 26 - 1) (hx8 : x8.val ≤ 3 * 2 ^ 26 - 1) :
    mulCoeff5 y1 y2 y3 y4 y5 y6_19 y7_19 y8_19 y9_19 x1 x3 x5 x7 x9 x0 y0 x2 x4 x6 x8
      ⦃ (r : U64) =>
      r.val = x0.val * y5.val + x1.val * y4.val + x2.val * y3.val + x3.val * y2.val +
        x4.val * y1.val + x5.val * y0.val + x6.val * y9_19.val + x7.val * y8_19.val +
        x8.val * y7_19.val + x9.val * y6_19.val ∧
      r.val < 2403 * 2 ^ 52 ⦄ := by
  unfold mulCoeff5
  repeat' first
    | (step with mul.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `6` of `mul`: its exact value and the shared bound `r < 2403 * 2 ^ 52`, proved
like `mulCoeff0_spec` but without the limb reads. -/
@[local step]
private theorem mulCoeff6_spec (y1 y2 y3 y4 y5 y6 y7_19 y8_19 y9_19 x1_2 x3_2 x5_2 x7_2 x9_2 x0
    y0 x2 x4 x6 x8 : U32)
    (hy1 : y1.val ≤ 3 * 2 ^ 26 - 1) (hy2 : y2.val ≤ 3 * 2 ^ 26 - 1)
    (hy3 : y3.val ≤ 3 * 2 ^ 26 - 1) (hy4 : y4.val ≤ 3 * 2 ^ 26 - 1)
    (hy5 : y5.val ≤ 3 * 2 ^ 26 - 1) (hy6 : y6.val ≤ 3 * 2 ^ 26 - 1)
    (hy7_19 : y7_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hy8_19 : y8_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy9_19 : y9_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hx1_2 : x1_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx3_2 : x3_2.val ≤ 2 * (3 * 2 ^ 26 - 1)) (hx5_2 : x5_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx7_2 : x7_2.val ≤ 2 * (3 * 2 ^ 26 - 1)) (hx9_2 : x9_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx0 : x0.val ≤ 3 * 2 ^ 26 - 1) (hy0 : y0.val ≤ 3 * 2 ^ 26 - 1)
    (hx2 : x2.val ≤ 3 * 2 ^ 26 - 1) (hx4 : x4.val ≤ 3 * 2 ^ 26 - 1)
    (hx6 : x6.val ≤ 3 * 2 ^ 26 - 1) (hx8 : x8.val ≤ 3 * 2 ^ 26 - 1) :
    mulCoeff6 y1 y2 y3 y4 y5 y6 y7_19 y8_19 y9_19 x1_2 x3_2 x5_2 x7_2 x9_2 x0 y0 x2 x4 x6 x8
      ⦃ (r : U64) =>
      r.val = x0.val * y6.val + x1_2.val * y5.val + x2.val * y4.val + x3_2.val * y3.val +
        x4.val * y2.val + x5_2.val * y1.val + x6.val * y0.val + x7_2.val * y9_19.val +
        x8.val * y8_19.val + x9_2.val * y7_19.val ∧
      r.val < 2403 * 2 ^ 52 ⦄ := by
  unfold mulCoeff6
  repeat' first
    | (step with mul.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `7` of `mul`: its exact value and the shared bound `r < 2403 * 2 ^ 52`, proved
like `mulCoeff0_spec` but without the limb reads. -/
@[local step]
private theorem mulCoeff7_spec (y1 y2 y3 y4 y5 y6 y7 y8_19 y9_19 x1 x3 x5 x7 x9 x0 y0 x2 x4 x6 x8
    : U32)
    (hy1 : y1.val ≤ 3 * 2 ^ 26 - 1) (hy2 : y2.val ≤ 3 * 2 ^ 26 - 1)
    (hy3 : y3.val ≤ 3 * 2 ^ 26 - 1) (hy4 : y4.val ≤ 3 * 2 ^ 26 - 1)
    (hy5 : y5.val ≤ 3 * 2 ^ 26 - 1) (hy6 : y6.val ≤ 3 * 2 ^ 26 - 1)
    (hy7 : y7.val ≤ 3 * 2 ^ 26 - 1) (hy8_19 : y8_19.val ≤ 19 * (3 * 2 ^ 26 - 1))
    (hy9_19 : y9_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hx1 : x1.val ≤ 3 * 2 ^ 26 - 1)
    (hx3 : x3.val ≤ 3 * 2 ^ 26 - 1) (hx5 : x5.val ≤ 3 * 2 ^ 26 - 1)
    (hx7 : x7.val ≤ 3 * 2 ^ 26 - 1) (hx9 : x9.val ≤ 3 * 2 ^ 26 - 1)
    (hx0 : x0.val ≤ 3 * 2 ^ 26 - 1) (hy0 : y0.val ≤ 3 * 2 ^ 26 - 1)
    (hx2 : x2.val ≤ 3 * 2 ^ 26 - 1) (hx4 : x4.val ≤ 3 * 2 ^ 26 - 1)
    (hx6 : x6.val ≤ 3 * 2 ^ 26 - 1) (hx8 : x8.val ≤ 3 * 2 ^ 26 - 1) :
    mulCoeff7 y1 y2 y3 y4 y5 y6 y7 y8_19 y9_19 x1 x3 x5 x7 x9 x0 y0 x2 x4 x6 x8 ⦃ (r : U64) =>
      r.val = x0.val * y7.val + x1.val * y6.val + x2.val * y5.val + x3.val * y4.val +
        x4.val * y3.val + x5.val * y2.val + x6.val * y1.val + x7.val * y0.val +
        x8.val * y9_19.val + x9.val * y8_19.val ∧
      r.val < 2403 * 2 ^ 52 ⦄ := by
  unfold mulCoeff7
  repeat' first
    | (step with mul.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `8` of `mul`: its exact value and the shared bound `r < 2403 * 2 ^ 52`, proved
like `mulCoeff0_spec` but without the limb reads. -/
@[local step]
private theorem mulCoeff8_spec (y1 y2 y3 y4 y5 y6 y7 y8 y9_19 x1_2 x3_2 x5_2 x7_2 x9_2 x0 y0 x2
    x4 x6 x8 : U32)
    (hy1 : y1.val ≤ 3 * 2 ^ 26 - 1) (hy2 : y2.val ≤ 3 * 2 ^ 26 - 1)
    (hy3 : y3.val ≤ 3 * 2 ^ 26 - 1) (hy4 : y4.val ≤ 3 * 2 ^ 26 - 1)
    (hy5 : y5.val ≤ 3 * 2 ^ 26 - 1) (hy6 : y6.val ≤ 3 * 2 ^ 26 - 1)
    (hy7 : y7.val ≤ 3 * 2 ^ 26 - 1) (hy8 : y8.val ≤ 3 * 2 ^ 26 - 1)
    (hy9_19 : y9_19.val ≤ 19 * (3 * 2 ^ 26 - 1)) (hx1_2 : x1_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx3_2 : x3_2.val ≤ 2 * (3 * 2 ^ 26 - 1)) (hx5_2 : x5_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx7_2 : x7_2.val ≤ 2 * (3 * 2 ^ 26 - 1)) (hx9_2 : x9_2.val ≤ 2 * (3 * 2 ^ 26 - 1))
    (hx0 : x0.val ≤ 3 * 2 ^ 26 - 1) (hy0 : y0.val ≤ 3 * 2 ^ 26 - 1)
    (hx2 : x2.val ≤ 3 * 2 ^ 26 - 1) (hx4 : x4.val ≤ 3 * 2 ^ 26 - 1)
    (hx6 : x6.val ≤ 3 * 2 ^ 26 - 1) (hx8 : x8.val ≤ 3 * 2 ^ 26 - 1) :
    mulCoeff8 y1 y2 y3 y4 y5 y6 y7 y8 y9_19 x1_2 x3_2 x5_2 x7_2 x9_2 x0 y0 x2 x4 x6 x8
      ⦃ (r : U64) =>
      r.val = x0.val * y8.val + x1_2.val * y7.val + x2.val * y6.val + x3_2.val * y5.val +
        x4.val * y4.val + x5_2.val * y3.val + x6.val * y2.val + x7_2.val * y1.val +
        x8.val * y0.val + x9_2.val * y9_19.val ∧
      r.val < 2403 * 2 ^ 52 ⦄ := by
  unfold mulCoeff8
  repeat' first
    | (step with mul.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- Coefficient `9` of `mul`: its exact value and the shared bound `r < 2403 * 2 ^ 52`, proved
like `mulCoeff0_spec` but without the limb reads. -/
@[local step]
private theorem mulCoeff9_spec (y1 y2 y3 y4 y5 y6 y7 y8 y9 x1 x3 x5 x7 x9 x0 y0 x2 x4 x6 x8 : U32)
    (hy1 : y1.val ≤ 3 * 2 ^ 26 - 1) (hy2 : y2.val ≤ 3 * 2 ^ 26 - 1)
    (hy3 : y3.val ≤ 3 * 2 ^ 26 - 1) (hy4 : y4.val ≤ 3 * 2 ^ 26 - 1)
    (hy5 : y5.val ≤ 3 * 2 ^ 26 - 1) (hy6 : y6.val ≤ 3 * 2 ^ 26 - 1)
    (hy7 : y7.val ≤ 3 * 2 ^ 26 - 1) (hy8 : y8.val ≤ 3 * 2 ^ 26 - 1)
    (hy9 : y9.val ≤ 3 * 2 ^ 26 - 1) (hx1 : x1.val ≤ 3 * 2 ^ 26 - 1)
    (hx3 : x3.val ≤ 3 * 2 ^ 26 - 1) (hx5 : x5.val ≤ 3 * 2 ^ 26 - 1)
    (hx7 : x7.val ≤ 3 * 2 ^ 26 - 1) (hx9 : x9.val ≤ 3 * 2 ^ 26 - 1)
    (hx0 : x0.val ≤ 3 * 2 ^ 26 - 1) (hy0 : y0.val ≤ 3 * 2 ^ 26 - 1)
    (hx2 : x2.val ≤ 3 * 2 ^ 26 - 1) (hx4 : x4.val ≤ 3 * 2 ^ 26 - 1)
    (hx6 : x6.val ≤ 3 * 2 ^ 26 - 1) (hx8 : x8.val ≤ 3 * 2 ^ 26 - 1) :
    mulCoeff9 y1 y2 y3 y4 y5 y6 y7 y8 y9 x1 x3 x5 x7 x9 x0 y0 x2 x4 x6 x8 ⦃ (r : U64) =>
      r.val = x0.val * y9.val + x1.val * y8.val + x2.val * y7.val + x3.val * y6.val +
        x4.val * y5.val + x5.val * y4.val + x6.val * y3.val + x7.val * y2.val + x8.val * y1.val +
        x9.val * y0.val ∧
      r.val < 2403 * 2 ^ 52 ⦄ := by
  unfold mulCoeff9
  repeat' first
    | (step with mul.m_spec as ⟨product, h_product⟩
       have h_product_bound := h_product.trans_le (Nat.mul_le_mul ‹_› ‹_›))
    | (step with U64.add_spec as ⟨sum, h_sum⟩
       have h_sum_bound := h_sum.trans_le (Nat.add_le_add ‹_› ‹_›))
  exact ⟨by simp only [*], lt_of_le_of_lt ‹_› (by norm_num)⟩

/-- **Spec theorem for**
`<&curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
core::ops::Mul<&FieldElement2625>>::mul`
If every limb of both operands is below `3 * 2 ^ 26` (enough for operands that are sums of up to
three reduced elements), `mul` succeeds and returns a reduced element (every limb below `2 ^ 26`)
representing `self * _rhs` modulo `p`.
The proof is compositional. The limb hypotheses are first restated as the bounds
`≤ 3 * 2 ^ 26 - 1` that the block specs take. `mul_decomp` splits `mul` into the ten coefficient
blocks, `index_usize_eq` resolves the limb reads, and `step*` chains the `u32` precomputations of
`19 * y[j]` and `2 * x[i]` (below `57 * 2 ^ 26 < 2 ^ 32`), the spec theorem of each block and
`reduce_spec`. Every coefficient is below `2403 * 2 ^ 52 < 2 ^ 64 - 2 ^ 39`, so `getElem!_make_le`
with one `omega` per limb discharges the precondition of `reduce`, and the limb bound is the first
postcondition of `reduce_spec`. For the value, its congruence, `uScalarToNatField2625_make` and
`toNat_expand` turn both sides into weighted limb sums, into which the block and precomputation
postconditions are substituted. The goal is then moved to `ZMod p`, where
`(19 : ZMod p) = 2 ^ 255`, derived from `p_add_19`, accounts for the upper half of the schoolbook
product folded back into the lower limbs, and `ring` closes it. -/
@[step]
theorem mul_spec (self _rhs : FieldElement2625)
    (h_self : ∀ i < 10, self[i]!.val < 3 * 2 ^ 26)
    (h_rhs : ∀ i < 10, _rhs[i]!.val < 3 * 2 ^ 26) :
    mul self _rhs ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val < 2 ^ 26) ∧
      result.toNat % p = self.toNat * _rhs.toNat % p ⦄ := by
  have hx0 : self[0]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_self 0 (by decide))
  have hx1 : self[1]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_self 1 (by decide))
  have hx2 : self[2]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_self 2 (by decide))
  have hx3 : self[3]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_self 3 (by decide))
  have hx4 : self[4]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_self 4 (by decide))
  have hx5 : self[5]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_self 5 (by decide))
  have hx6 : self[6]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_self 6 (by decide))
  have hx7 : self[7]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_self 7 (by decide))
  have hx8 : self[8]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_self 8 (by decide))
  have hx9 : self[9]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_self 9 (by decide))
  have hy0 : _rhs[0]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_rhs 0 (by decide))
  have hy1 : _rhs[1]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_rhs 1 (by decide))
  have hy2 : _rhs[2]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_rhs 2 (by decide))
  have hy3 : _rhs[3]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_rhs 3 (by decide))
  have hy4 : _rhs[4]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_rhs 4 (by decide))
  have hy5 : _rhs[5]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_rhs 5 (by decide))
  have hy6 : _rhs[6]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_rhs 6 (by decide))
  have hy7 : _rhs[7]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_rhs 7 (by decide))
  have hy8 : _rhs[8]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_rhs 8 (by decide))
  have hy9 : _rhs[9]!.val ≤ 3 * 2 ^ 26 - 1 := Nat.le_pred_of_lt (h_rhs 9 (by decide))
  clear h_self h_rhs
  rewrite [mul_decomp]
  simp only [FieldElement2625.index_usize_eq, Nat.reduceLT, UScalar.ofNatCore_val_eq, bind_tc_ok]
  step*
  · exact FieldElement2625.getElem!_make_le _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · refine ⟨result_post1, ?_⟩
    rw [result_post2, FieldElement2625.uScalarToNatField2625_make,
      FieldElement2625.toNat_expand self, FieldElement2625.toNat_expand _rhs]
    simp only [i19_post5, z1_post1, z2_post1, z3_post1, z4_post1, z5_post1, z6_post1, z7_post1,
      z8_post1, z9_post1, i19_post1, i19_post2, i19_post3, i19_post4, y1_19_post, y2_19_post,
      y3_19_post, y4_19_post, y5_19_post, y6_19_post, y7_19_post, y8_19_post, y9_19_post,
      x1_2_post, x3_2_post, x5_2_post, x7_2_post, x9_2_post]
    have h19 : (19 : ZMod p) = 2 ^ 255 := by
      have h := congrArg (Nat.cast : ℕ → ZMod p) p_add_19
      rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_ofNat] at h
      exact h
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [h19]
    ring

end CoreOpsArithMulSharedBFieldElement2625FieldElement2625
end Curve25519Dalek.SharedAFieldElement2625.Insts

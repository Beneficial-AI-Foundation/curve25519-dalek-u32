/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Dalek32.Definitions
import Dalek32.Lint.Basic
import Dalek32.Scalar.Index
import Dalek32.Scalar.M
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Specification for `Scalar29.mul_internal`

The Karatsuba implementation computes the exact radix-`2 ^ 29` product. Intermediate
wrapping operations are interpreted in `ZMod (2 ^ 64)`; coefficient bounds then
recover equality in `Nat`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

private theorem index_eq (a : Scalar29) (j : Usize) (h_j : j.val < 9) :
    Insts.CoreOpsIndexIndexUsizeU32.index a j = ok a.val[j.val]! := by
  obtain ⟨result, h_eq, h_result⟩ := spec_imp_exists
    (Insts.CoreOpsIndexIndexUsizeU32.index_spec a j h_j)
  exact h_result ▸ h_eq

private theorem wrapping_add_mod (x y : U64) :
    ((core.num.U64.wrapping_add x y).val : ZMod (2 ^ 64)) =
      (x.val : ZMod (2 ^ 64)) + (y.val : ZMod (2 ^ 64)) := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size, U64.numBits]

private theorem wrapping_sub_mod (x y : U64) :
    ((core.num.U64.wrapping_sub x y).val : ZMod (2 ^ 64)) =
      (x.val : ZMod (2 ^ 64)) - (y.val : ZMod (2 ^ 64)) := by
  have hy : y.val ≤ 2 ^ 64 := Nat.le_of_lt y.hBounds
  simp only [core.num.U64.wrapping_sub_val_eq, UScalar.size, UScalarTy.numBits]
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hy]
  simp [sub_eq_add_neg]

private theorem eq_of_mod (x : U64) (n : Nat) (hn : n < 2 ^ 64)
    (h : (x.val : ZMod (2 ^ 64)) = (n : ZMod (2 ^ 64))) : x.val = n := by
  have hx : x.val < 2 ^ 64 := x.hBounds
  simpa only [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hn] using h

/-- The ordinary schoolbook convolution, before carrying. -/
private def mulCoefficients (a b : Scalar29) : List Nat :=
  [ a.val[0]!.val * b.val[0]!.val,
    a.val[0]!.val * b.val[1]!.val + a.val[1]!.val * b.val[0]!.val,
    a.val[0]!.val * b.val[2]!.val + a.val[1]!.val * b.val[1]!.val +
      a.val[2]!.val * b.val[0]!.val,
    a.val[0]!.val * b.val[3]!.val + a.val[1]!.val * b.val[2]!.val +
      a.val[2]!.val * b.val[1]!.val + a.val[3]!.val * b.val[0]!.val,
    a.val[0]!.val * b.val[4]!.val + a.val[1]!.val * b.val[3]!.val +
      a.val[2]!.val * b.val[2]!.val + a.val[3]!.val * b.val[1]!.val +
      a.val[4]!.val * b.val[0]!.val,
    a.val[0]!.val * b.val[5]!.val + a.val[1]!.val * b.val[4]!.val +
      a.val[2]!.val * b.val[3]!.val + a.val[3]!.val * b.val[2]!.val +
      a.val[4]!.val * b.val[1]!.val + a.val[5]!.val * b.val[0]!.val,
    a.val[0]!.val * b.val[6]!.val + a.val[1]!.val * b.val[5]!.val +
      a.val[2]!.val * b.val[4]!.val + a.val[3]!.val * b.val[3]!.val +
      a.val[4]!.val * b.val[2]!.val + a.val[5]!.val * b.val[1]!.val +
      a.val[6]!.val * b.val[0]!.val,
    a.val[0]!.val * b.val[7]!.val + a.val[1]!.val * b.val[6]!.val +
      a.val[2]!.val * b.val[5]!.val + a.val[3]!.val * b.val[4]!.val +
      a.val[4]!.val * b.val[3]!.val + a.val[5]!.val * b.val[2]!.val +
      a.val[6]!.val * b.val[1]!.val + a.val[7]!.val * b.val[0]!.val,
    a.val[0]!.val * b.val[8]!.val + a.val[1]!.val * b.val[7]!.val +
      a.val[2]!.val * b.val[6]!.val + a.val[3]!.val * b.val[5]!.val +
      a.val[4]!.val * b.val[4]!.val + a.val[5]!.val * b.val[3]!.val +
      a.val[6]!.val * b.val[2]!.val + a.val[7]!.val * b.val[1]!.val +
      a.val[8]!.val * b.val[0]!.val,
    a.val[1]!.val * b.val[8]!.val + a.val[2]!.val * b.val[7]!.val +
      a.val[3]!.val * b.val[6]!.val + a.val[4]!.val * b.val[5]!.val +
      a.val[5]!.val * b.val[4]!.val + a.val[6]!.val * b.val[3]!.val +
      a.val[7]!.val * b.val[2]!.val + a.val[8]!.val * b.val[1]!.val,
    a.val[2]!.val * b.val[8]!.val + a.val[3]!.val * b.val[7]!.val +
      a.val[4]!.val * b.val[6]!.val + a.val[5]!.val * b.val[5]!.val +
      a.val[6]!.val * b.val[4]!.val + a.val[7]!.val * b.val[3]!.val +
      a.val[8]!.val * b.val[2]!.val,
    a.val[3]!.val * b.val[8]!.val + a.val[4]!.val * b.val[7]!.val +
      a.val[5]!.val * b.val[6]!.val + a.val[6]!.val * b.val[5]!.val +
      a.val[7]!.val * b.val[4]!.val + a.val[8]!.val * b.val[3]!.val,
    a.val[4]!.val * b.val[8]!.val + a.val[5]!.val * b.val[7]!.val +
      a.val[6]!.val * b.val[6]!.val + a.val[7]!.val * b.val[5]!.val +
      a.val[8]!.val * b.val[4]!.val,
    a.val[5]!.val * b.val[8]!.val + a.val[6]!.val * b.val[7]!.val +
      a.val[7]!.val * b.val[6]!.val + a.val[8]!.val * b.val[5]!.val,
    a.val[6]!.val * b.val[8]!.val + a.val[7]!.val * b.val[7]!.val +
      a.val[8]!.val * b.val[6]!.val,
    a.val[7]!.val * b.val[8]!.val + a.val[8]!.val * b.val[7]!.val,
    a.val[8]!.val * b.val[8]!.val ]

private theorem mulCoefficients_bound (a b : Scalar29)
    (ha : IsNormalized a) (hb : IsNormalized b) (j : Nat) (hj : j < 17) :
    (mulCoefficients a b)[j]! < 2 ^ 63 := by
  have hp (i k : Nat) (hi : i < 9) (hk : k < 9) :
      a.val[i]!.val * b.val[k]!.val ≤ 2 ^ 58 := by
    have hai := ha i hi
    have hbk := hb k hk
    simp only [limbRadix, Array.getElem!_Nat_eq] at hai hbk
    calc
      _ ≤ 2 ^ 29 * 2 ^ 29 := Nat.mul_le_mul hai.le hbk.le
      _ = 2 ^ 58 := by norm_num
  have h00 := hp 0 0 (by decide) (by decide)
  have h01 := hp 0 1 (by decide) (by decide)
  have h02 := hp 0 2 (by decide) (by decide)
  have h03 := hp 0 3 (by decide) (by decide)
  have h04 := hp 0 4 (by decide) (by decide)
  have h05 := hp 0 5 (by decide) (by decide)
  have h06 := hp 0 6 (by decide) (by decide)
  have h07 := hp 0 7 (by decide) (by decide)
  have h08 := hp 0 8 (by decide) (by decide)
  have h10 := hp 1 0 (by decide) (by decide)
  have h11 := hp 1 1 (by decide) (by decide)
  have h12 := hp 1 2 (by decide) (by decide)
  have h13 := hp 1 3 (by decide) (by decide)
  have h14 := hp 1 4 (by decide) (by decide)
  have h15 := hp 1 5 (by decide) (by decide)
  have h16 := hp 1 6 (by decide) (by decide)
  have h17 := hp 1 7 (by decide) (by decide)
  have h18 := hp 1 8 (by decide) (by decide)
  have h20 := hp 2 0 (by decide) (by decide)
  have h21 := hp 2 1 (by decide) (by decide)
  have h22 := hp 2 2 (by decide) (by decide)
  have h23 := hp 2 3 (by decide) (by decide)
  have h24 := hp 2 4 (by decide) (by decide)
  have h25 := hp 2 5 (by decide) (by decide)
  have h26 := hp 2 6 (by decide) (by decide)
  have h27 := hp 2 7 (by decide) (by decide)
  have h28 := hp 2 8 (by decide) (by decide)
  have h30 := hp 3 0 (by decide) (by decide)
  have h31 := hp 3 1 (by decide) (by decide)
  have h32 := hp 3 2 (by decide) (by decide)
  have h33 := hp 3 3 (by decide) (by decide)
  have h34 := hp 3 4 (by decide) (by decide)
  have h35 := hp 3 5 (by decide) (by decide)
  have h36 := hp 3 6 (by decide) (by decide)
  have h37 := hp 3 7 (by decide) (by decide)
  have h38 := hp 3 8 (by decide) (by decide)
  have h40 := hp 4 0 (by decide) (by decide)
  have h41 := hp 4 1 (by decide) (by decide)
  have h42 := hp 4 2 (by decide) (by decide)
  have h43 := hp 4 3 (by decide) (by decide)
  have h44 := hp 4 4 (by decide) (by decide)
  have h45 := hp 4 5 (by decide) (by decide)
  have h46 := hp 4 6 (by decide) (by decide)
  have h47 := hp 4 7 (by decide) (by decide)
  have h48 := hp 4 8 (by decide) (by decide)
  have h50 := hp 5 0 (by decide) (by decide)
  have h51 := hp 5 1 (by decide) (by decide)
  have h52 := hp 5 2 (by decide) (by decide)
  have h53 := hp 5 3 (by decide) (by decide)
  have h54 := hp 5 4 (by decide) (by decide)
  have h55 := hp 5 5 (by decide) (by decide)
  have h56 := hp 5 6 (by decide) (by decide)
  have h57 := hp 5 7 (by decide) (by decide)
  have h58 := hp 5 8 (by decide) (by decide)
  have h60 := hp 6 0 (by decide) (by decide)
  have h61 := hp 6 1 (by decide) (by decide)
  have h62 := hp 6 2 (by decide) (by decide)
  have h63 := hp 6 3 (by decide) (by decide)
  have h64 := hp 6 4 (by decide) (by decide)
  have h65 := hp 6 5 (by decide) (by decide)
  have h66 := hp 6 6 (by decide) (by decide)
  have h67 := hp 6 7 (by decide) (by decide)
  have h68 := hp 6 8 (by decide) (by decide)
  have h70 := hp 7 0 (by decide) (by decide)
  have h71 := hp 7 1 (by decide) (by decide)
  have h72 := hp 7 2 (by decide) (by decide)
  have h73 := hp 7 3 (by decide) (by decide)
  have h74 := hp 7 4 (by decide) (by decide)
  have h75 := hp 7 5 (by decide) (by decide)
  have h76 := hp 7 6 (by decide) (by decide)
  have h77 := hp 7 7 (by decide) (by decide)
  have h78 := hp 7 8 (by decide) (by decide)
  have h80 := hp 8 0 (by decide) (by decide)
  have h81 := hp 8 1 (by decide) (by decide)
  have h82 := hp 8 2 (by decide) (by decide)
  have h83 := hp 8 3 (by decide) (by decide)
  have h84 := hp 8 4 (by decide) (by decide)
  have h85 := hp 8 5 (by decide) (by decide)
  have h86 := hp 8 6 (by decide) (by decide)
  have h87 := hp 8 7 (by decide) (by decide)
  have h88 := hp 8 8 (by decide) (by decide)
  interval_cases j <;>
    simp only [mulCoefficients, List.getElem!_cons_zero, List.getElem!_cons_succ] <;>
    omega

private theorem mulCoefficients_value (a b : Scalar29) :
    (∑ j ∈ Finset.range 17, 2 ^ (29 * j) * (mulCoefficients a b)[j]!) =
      asNat a * asNat b := by
  simp only [asNat, Array.uScalarToNatRadix, UScalar.ofNatCore_val_eq, pow_mul]
  generalize (2 ^ 29 : Nat) = B
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    mulCoefficients, Array.getElem!_Nat_eq,
    List.getElem!_cons_zero, List.getElem!_cons_succ]
  ring

-- The extracted straight-line program has many nested binds. The final per-index
-- simplification shares a lemma set across all seventeen coefficients.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Symbolically execute the unrolled Karatsuba program and normalize all 17 coefficients.
set_option linter.unusedSimpArgs false in
/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::mul_internal`**

For normalized inputs, returns their exact product as seventeen radix-`2 ^ 29`
coefficients. Every coefficient is below `2 ^ 63`, as required by
`montgomery_reduce_spec`; no bound on the full input product is needed here. -/
@[step]
theorem mul_internal_spec (a b : Scalar29)
    (h_a : IsNormalized a) (h_b : IsNormalized b) :
    mul_internal a b ⦃ (result : Array U64 17#usize) =>
      wideAsNat result = asNat a * asNat b ∧
      (∀ i < 17, result[i]!.val < 2 ^ 63) ⦄ := by
  have h_normal_a := h_a
  have h_normal_b := h_b
  simp only [IsNormalized, limbRadix, Array.getElem!_Nat_eq] at h_a h_b
  have ha0 := h_a 0 (by decide)
  have ha1 := h_a 1 (by decide)
  have ha2 := h_a 2 (by decide)
  have ha3 := h_a 3 (by decide)
  have ha4 := h_a 4 (by decide)
  have ha5 := h_a 5 (by decide)
  have ha6 := h_a 6 (by decide)
  have ha7 := h_a 7 (by decide)
  have ha8 := h_a 8 (by decide)
  have hb0 := h_b 0 (by decide)
  have hb1 := h_b 1 (by decide)
  have hb2 := h_b 2 (by decide)
  have hb3 := h_b 3 (by decide)
  have hb4 := h_b 4 (by decide)
  have hb5 := h_b 5 (by decide)
  have hb6 := h_b 6 (by decide)
  have hb7 := h_b 7 (by decide)
  have hb8 := h_b 8 (by decide)
  -- Reduce fixed array accesses before executing arithmetic operations.
  unfold mul_internal
  simp only [index_eq, UScalar.ofNatCore_val_eq, Nat.reduceLT, bind_tc_ok]
  simp only [Array.update, Array.index_usize, Array.getElem?_Usize_eq,
    Array.make, Array.repeat, UScalar.ofNatCore_val_eq,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.set_cons_zero, List.set_cons_succ, List.replicate_succ,
    List.replicate_zero, bind_tc_ok, lift]
  -- Products of the Karatsuba limb sums fit below 2 ^ 60; checked additions
  -- contain at most five such terms. Wrapping operations remain symbolic.
  repeat' first
    | (step -threadGrindState -grind -assumTac with m_spec as ⟨product, h_product⟩
       have h_product_bound : product.val ≤ 2 ^ 60 := by
         rw [h_product]
         calc
           _ ≤ 2 ^ 30 * 2 ^ 30 := Nat.mul_le_mul (by omega) (by omega)
           _ = 2 ^ 60 := by norm_num)
    | (step -threadGrindState -grind -assumTac with U64.add_spec
         as ⟨sum, h_sum⟩ by
         clear! a b
         simp only [U64.max_eq]
         omega)
    | (step -threadGrindState -grind -assumTac with U32.add_spec as ⟨sum, h_sum⟩ by
         simp only [U32.max_eq]
         omega)
  -- Prove coefficient equality modulo 2 ^ 64, then use the schoolbook bounds
  -- to recover exact natural-number equality.
  generalize hr : (⟨_, _⟩ : Array U64 17#usize) = r
  · change Array U64 17#usize at r
    have h_coeff : ∀ j < 17, r[j]!.val = (mulCoefficients a b)[j]! := by
      intro j hj
      apply eq_of_mod _ _
        ((mulCoefficients_bound a b h_normal_a h_normal_b j hj).trans (by decide))
      rw [← hr]
      interval_cases j <;>
        simp only [Array.getElem!_Nat_eq, List.getElem!_cons_zero,
          List.getElem!_cons_succ, mulCoefficients, wrapping_add_mod, wrapping_sub_mod] <;>
        simp only [*, Nat.cast_add, Nat.cast_mul] <;> ring
    constructor
    · unfold wideAsNat Array.uScalarToNatRadix
      change (∑ j ∈ Finset.range 17, 2 ^ (29 * j) * r[j]!.val) = _
      rw [← mulCoefficients_value a b]
      apply Finset.sum_congr rfl
      intro j hj
      rw [h_coeff j (Finset.mem_range.mp hj)]
    · intro j hj
      rw [h_coeff j hj]
      exact mulCoefficients_bound a b h_normal_a h_normal_b j hj

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

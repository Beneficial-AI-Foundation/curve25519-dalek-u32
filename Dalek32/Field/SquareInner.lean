/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Dalek32.Field.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! # Wide-input field squaring

Verifies the extracted straight-line implementation with the input slack needed
by point doubling. All intermediate machine operations are checked for overflow.
The value identity accounts explicitly for the terms folded by `2^255 = 19 mod p`.
-/
open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[local step]
private theorem square_inner_m_spec (x y : U32) :
    square_inner.m x y ⦃ (result : U64) => result.val = x.val * y.val ⦄ := by
  unfold square_inner.m
  step*

-- The long extracted bind chain exceeds the default simplifier recursion depth.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Symbolic execution and the ten-limb polynomial identity need a larger tactic budget.
@[step]
theorem square_inner_spec (self : FieldElement2625) (h_bounds : SquareInputBounds self) :
    square_inner self ⦃ (z : Array U64 10#usize) =>
      Array.uScalarToNatField2625 z % p = toNat self ^ 2 % p ∧
      (∀ i < 10, z[i]!.val ≤ 2 ^ 64 - 2 ^ 39) ⦄ := by
  unfold square_inner
  -- Record exact values and numerical upper bounds through every machine operation.
  step -threadGrindState -grind as ⟨i, h_i⟩ by scalar_tac
  have b_i : i.val ≤ 134217727 := by
    have hb := h_bounds 0 (by decide)
    simp only [h_i, Array.getElem!_Nat_eq] at hb ⊢
    norm_num at hb ⊢
    omega
  step -threadGrindState -grind with U32.mul_spec as ⟨x0_2, h_x0_2⟩ by
    have hb := Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x0_2 : x0_2.val ≤ 268435454 := by
    rw [h_x0_2]
    exact Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i
  step -threadGrindState -grind as ⟨i1, h_i1⟩ by scalar_tac
  have b_i1 : i1.val ≤ 67633151 := by
    have hb := h_bounds 1 (by decide)
    simp only [h_i1, Array.getElem!_Nat_eq] at hb ⊢
    norm_num at hb ⊢
    omega
  step -threadGrindState -grind with U32.mul_spec as ⟨x1_2, h_x1_2⟩ by
    have hb := Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i1
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x1_2 : x1_2.val ≤ 135266302 := by
    rw [h_x1_2]
    exact Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i1
  step -threadGrindState -grind as ⟨i2, h_i2⟩ by scalar_tac
  have b_i2 : i2.val ≤ 134217727 := by
    have hb := h_bounds 2 (by decide)
    simp only [h_i2, Array.getElem!_Nat_eq] at hb ⊢
    norm_num at hb ⊢
    omega
  step -threadGrindState -grind with U32.mul_spec as ⟨x2_2, h_x2_2⟩ by
    have hb := Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i2
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x2_2 : x2_2.val ≤ 268435454 := by
    rw [h_x2_2]
    exact Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i2
  step -threadGrindState -grind as ⟨i3, h_i3⟩ by scalar_tac
  have b_i3 : i3.val ≤ 67633151 := by
    have hb := h_bounds 3 (by decide)
    simp only [h_i3, Array.getElem!_Nat_eq] at hb ⊢
    norm_num at hb ⊢
    omega
  step -threadGrindState -grind with U32.mul_spec as ⟨x3_2, h_x3_2⟩ by
    have hb := Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i3
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x3_2 : x3_2.val ≤ 135266302 := by
    rw [h_x3_2]
    exact Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i3
  step -threadGrindState -grind as ⟨i4, h_i4⟩ by scalar_tac
  have b_i4 : i4.val ≤ 134217727 := by
    have hb := h_bounds 4 (by decide)
    simp only [h_i4, Array.getElem!_Nat_eq] at hb ⊢
    norm_num at hb ⊢
    omega
  step -threadGrindState -grind with U32.mul_spec as ⟨x4_2, h_x4_2⟩ by
    have hb := Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i4
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x4_2 : x4_2.val ≤ 268435454 := by
    rw [h_x4_2]
    exact Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i4
  step -threadGrindState -grind as ⟨i5, h_i5⟩ by scalar_tac
  have b_i5 : i5.val ≤ 67633151 := by
    have hb := h_bounds 5 (by decide)
    simp only [h_i5, Array.getElem!_Nat_eq] at hb ⊢
    norm_num at hb ⊢
    omega
  step -threadGrindState -grind with U32.mul_spec as ⟨x5_2, h_x5_2⟩ by
    have hb := Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i5
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x5_2 : x5_2.val ≤ 135266302 := by
    rw [h_x5_2]
    exact Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i5
  step -threadGrindState -grind as ⟨i6, h_i6⟩ by scalar_tac
  have b_i6 : i6.val ≤ 134217727 := by
    have hb := h_bounds 6 (by decide)
    simp only [h_i6, Array.getElem!_Nat_eq] at hb ⊢
    norm_num at hb ⊢
    omega
  step -threadGrindState -grind with U32.mul_spec as ⟨x6_2, h_x6_2⟩ by
    have hb := Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i6
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x6_2 : x6_2.val ≤ 268435454 := by
    rw [h_x6_2]
    exact Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i6
  step -threadGrindState -grind as ⟨i7, h_i7⟩ by scalar_tac
  have b_i7 : i7.val ≤ 67633151 := by
    have hb := h_bounds 7 (by decide)
    simp only [h_i7, Array.getElem!_Nat_eq] at hb ⊢
    norm_num at hb ⊢
    omega
  step -threadGrindState -grind with U32.mul_spec as ⟨x7_2, h_x7_2⟩ by
    have hb := Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i7
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x7_2 : x7_2.val ≤ 135266302 := by
    rw [h_x7_2]
    exact Nat.mul_le_mul (by decide : (2 : Nat) ≤ 2) b_i7
  step -threadGrindState -grind with U32.mul_spec as ⟨x5_19, h_x5_19⟩ by
    have hb := Nat.mul_le_mul (by decide : (19 : Nat) ≤ 19) b_i5
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x5_19 : x5_19.val ≤ 1285029869 := by
    rw [h_x5_19]
    exact Nat.mul_le_mul (by decide : (19 : Nat) ≤ 19) b_i5
  step -threadGrindState -grind with U32.mul_spec as ⟨x6_19, h_x6_19⟩ by
    have hb := Nat.mul_le_mul (by decide : (19 : Nat) ≤ 19) b_i6
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x6_19 : x6_19.val ≤ 2550136813 := by
    rw [h_x6_19]
    exact Nat.mul_le_mul (by decide : (19 : Nat) ≤ 19) b_i6
  step -threadGrindState -grind with U32.mul_spec as ⟨x7_19, h_x7_19⟩ by
    have hb := Nat.mul_le_mul (by decide : (19 : Nat) ≤ 19) b_i7
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x7_19 : x7_19.val ≤ 1285029869 := by
    rw [h_x7_19]
    exact Nat.mul_le_mul (by decide : (19 : Nat) ≤ 19) b_i7
  step -threadGrindState -grind as ⟨i8, h_i8⟩ by scalar_tac
  have b_i8 : i8.val ≤ 134217727 := by
    have hb := h_bounds 8 (by decide)
    simp only [h_i8, Array.getElem!_Nat_eq] at hb ⊢
    norm_num at hb ⊢
    omega
  step -threadGrindState -grind with U32.mul_spec as ⟨x8_19, h_x8_19⟩ by
    have hb := Nat.mul_le_mul (by decide : (19 : Nat) ≤ 19) b_i8
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x8_19 : x8_19.val ≤ 2550136813 := by
    rw [h_x8_19]
    exact Nat.mul_le_mul (by decide : (19 : Nat) ≤ 19) b_i8
  step -threadGrindState -grind as ⟨i9, h_i9⟩ by scalar_tac
  have b_i9 : i9.val ≤ 67633151 := by
    have hb := h_bounds 9 (by decide)
    simp only [h_i9, Array.getElem!_Nat_eq] at hb ⊢
    norm_num at hb ⊢
    omega
  step -threadGrindState -grind with U32.mul_spec as ⟨x9_19, h_x9_19⟩ by
    have hb := Nat.mul_le_mul (by decide : (19 : Nat) ≤ 19) b_i9
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_x9_19 : x9_19.val ≤ 1285029869 := by
    rw [h_x9_19]
    exact Nat.mul_le_mul (by decide : (19 : Nat) ≤ 19) b_i9
  step -threadGrindState -grind with square_inner_m_spec as ⟨i10, h_i10⟩
  have b_i10 : i10.val ≤ 18014398241046529 := by
    rw [h_i10]
    exact Nat.mul_le_mul b_i b_i
  step -threadGrindState -grind with square_inner_m_spec as ⟨i11, h_i11⟩
  have b_i11 : i11.val ≤ 684547133159768102 := by
    rw [h_i11]
    exact Nat.mul_le_mul b_x2_2 b_x8_19
  step -threadGrindState -grind with U64.add_spec as ⟨i12, h_i12⟩ by
    have hb := Nat.add_le_add b_i10 b_i11
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i12 : i12.val ≤ 702561531400814631 := by
    rw [h_i12]
    exact Nat.add_le_add b_i10 b_i11
  step -threadGrindState -grind with square_inner_m_spec as ⟨i13, h_i13⟩
  have b_i13 : i13.val ≤ 684547133159768102 := by
    rw [h_i13]
    exact Nat.mul_le_mul b_x4_2 b_x6_19
  step -threadGrindState -grind with U64.add_spec as ⟨i14, h_i14⟩ by
    have hb := Nat.add_le_add b_i12 b_i13
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i14 : i14.val ≤ 1387108664560582733 := by
    rw [h_i14]
    exact Nat.add_le_add b_i12 b_i13
  step -threadGrindState -grind with square_inner_m_spec as ⟨i15, h_i15⟩
  have b_i15 : i15.val ≤ 173821238339174438 := by
    rw [h_i15]
    exact Nat.mul_le_mul b_x1_2 b_x9_19
  step -threadGrindState -grind with square_inner_m_spec as ⟨i16, h_i16⟩
  have b_i16 : i16.val ≤ 173821238339174438 := by
    rw [h_i16]
    exact Nat.mul_le_mul b_x3_2 b_x7_19
  step -threadGrindState -grind with U64.add_spec as ⟨i17, h_i17⟩ by
    have hb := Nat.add_le_add b_i15 b_i16
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i17 : i17.val ≤ 347642476678348876 := by
    rw [h_i17]
    exact Nat.add_le_add b_i15 b_i16
  step -threadGrindState -grind with square_inner_m_spec as ⟨i18, h_i18⟩
  have b_i18 : i18.val ≤ 86910619169587219 := by
    rw [h_i18]
    exact Nat.mul_le_mul b_i5 b_x5_19
  step -threadGrindState -grind with U64.add_spec as ⟨i19, h_i19⟩ by
    have hb := Nat.add_le_add b_i17 b_i18
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i19 : i19.val ≤ 434553095847936095 := by
    rw [h_i19]
    exact Nat.add_le_add b_i17 b_i18
  step -threadGrindState -grind with U64.mul_spec as ⟨i20, h_i20⟩ by
    have hb := Nat.mul_le_mul b_i19 (by decide : (2 : Nat) ≤ 2)
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i20 : i20.val ≤ 869106191695872190 := by
    rw [h_i20]
    exact Nat.mul_le_mul b_i19 (by decide : (2 : Nat) ≤ 2)
  step -threadGrindState -grind with U64.add_spec as ⟨i21, h_i21⟩ by
    have hb := Nat.add_le_add b_i14 b_i20
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i21 : i21.val ≤ 2256214856256454923 := by
    rw [h_i21]
    exact Nat.add_le_add b_i14 b_i20
  step -threadGrindState -grind as ⟨z1, h_z1⟩ by scalar_tac
  step -threadGrindState -grind with square_inner_m_spec as ⟨i22, h_i22⟩
  have b_i22 : i22.val ≤ 18155135594135554 := by
    rw [h_i22]
    exact Nat.mul_le_mul b_x0_2 b_i1
  step -threadGrindState -grind with square_inner_m_spec as ⟨i23, h_i23⟩
  have b_i23 : i23.val ≤ 344947576288575526 := by
    rw [h_i23]
    exact Nat.mul_le_mul b_x3_2 b_x8_19
  step -threadGrindState -grind with U64.add_spec as ⟨i24, h_i24⟩ by
    have hb := Nat.add_le_add b_i22 b_i23
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i24 : i24.val ≤ 363102711882711080 := by
    rw [h_i24]
    exact Nat.add_le_add b_i22 b_i23
  step -threadGrindState -grind with square_inner_m_spec as ⟨i25, h_i25⟩
  have b_i25 : i25.val ≤ 344947576288575526 := by
    rw [h_i25]
    exact Nat.mul_le_mul b_x5_2 b_x6_19
  step -threadGrindState -grind with U64.add_spec as ⟨i26, h_i26⟩ by
    have hb := Nat.add_le_add b_i24 b_i25
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i26 : i26.val ≤ 708050288171286606 := by
    rw [h_i26]
    exact Nat.add_le_add b_i24 b_i25
  step -threadGrindState -grind with square_inner_m_spec as ⟨i27, h_i27⟩
  have b_i27 : i27.val ≤ 172473788144287763 := by
    rw [h_i27]
    exact Nat.mul_le_mul b_i2 b_x9_19
  step -threadGrindState -grind with square_inner_m_spec as ⟨i28, h_i28⟩
  have b_i28 : i28.val ≤ 172473788144287763 := by
    rw [h_i28]
    exact Nat.mul_le_mul b_i4 b_x7_19
  step -threadGrindState -grind with U64.add_spec as ⟨i29, h_i29⟩ by
    have hb := Nat.add_le_add b_i27 b_i28
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i29 : i29.val ≤ 344947576288575526 := by
    rw [h_i29]
    exact Nat.add_le_add b_i27 b_i28
  step -threadGrindState -grind with U64.mul_spec as ⟨i30, h_i30⟩ by
    have hb := Nat.mul_le_mul b_i29 (by decide : (2 : Nat) ≤ 2)
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i30 : i30.val ≤ 689895152577151052 := by
    rw [h_i30]
    exact Nat.mul_le_mul b_i29 (by decide : (2 : Nat) ≤ 2)
  step -threadGrindState -grind with U64.add_spec as ⟨i31, h_i31⟩ by
    have hb := Nat.add_le_add b_i26 b_i30
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i31 : i31.val ≤ 1397945440748437658 := by
    rw [h_i31]
    exact Nat.add_le_add b_i26 b_i30
  step -threadGrindState -grind as ⟨z2, h_z2⟩ by scalar_tac
  step -threadGrindState -grind with square_inner_m_spec as ⟨i32, h_i32⟩
  have b_i32 : i32.val ≤ 36028796482093058 := by
    rw [h_i32]
    exact Nat.mul_le_mul b_x0_2 b_i2
  step -threadGrindState -grind with square_inner_m_spec as ⟨i33, h_i33⟩
  have b_i33 : i33.val ≤ 9148486228377602 := by
    rw [h_i33]
    exact Nat.mul_le_mul b_x1_2 b_i1
  step -threadGrindState -grind with U64.add_spec as ⟨i34, h_i34⟩ by
    have hb := Nat.add_le_add b_i32 b_i33
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i34 : i34.val ≤ 45177282710470660 := by
    rw [h_i34]
    exact Nat.add_le_add b_i32 b_i33
  step -threadGrindState -grind with square_inner_m_spec as ⟨i35, h_i35⟩
  have b_i35 : i35.val ≤ 684547133159768102 := by
    rw [h_i35]
    exact Nat.mul_le_mul b_x4_2 b_x8_19
  step -threadGrindState -grind with U64.add_spec as ⟨i36, h_i36⟩ by
    have hb := Nat.add_le_add b_i34 b_i35
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i36 : i36.val ≤ 729724415870238762 := by
    rw [h_i36]
    exact Nat.add_le_add b_i34 b_i35
  step -threadGrindState -grind with square_inner_m_spec as ⟨i37, h_i37⟩
  have b_i37 : i37.val ≤ 342273566579884051 := by
    rw [h_i37]
    exact Nat.mul_le_mul b_i6 b_x6_19
  step -threadGrindState -grind with U64.add_spec as ⟨i38, h_i38⟩ by
    have hb := Nat.add_le_add b_i36 b_i37
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i38 : i38.val ≤ 1071997982450122813 := by
    rw [h_i38]
    exact Nat.add_le_add b_i36 b_i37
  step -threadGrindState -grind with square_inner_m_spec as ⟨i39, h_i39⟩
  have b_i39 : i39.val ≤ 173821238339174438 := by
    rw [h_i39]
    exact Nat.mul_le_mul b_x3_2 b_x9_19
  step -threadGrindState -grind with square_inner_m_spec as ⟨i40, h_i40⟩
  have b_i40 : i40.val ≤ 173821238339174438 := by
    rw [h_i40]
    exact Nat.mul_le_mul b_x5_2 b_x7_19
  step -threadGrindState -grind with U64.add_spec as ⟨i41, h_i41⟩ by
    have hb := Nat.add_le_add b_i39 b_i40
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i41 : i41.val ≤ 347642476678348876 := by
    rw [h_i41]
    exact Nat.add_le_add b_i39 b_i40
  step -threadGrindState -grind with U64.mul_spec as ⟨i42, h_i42⟩ by
    have hb := Nat.mul_le_mul b_i41 (by decide : (2 : Nat) ≤ 2)
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i42 : i42.val ≤ 695284953356697752 := by
    rw [h_i42]
    exact Nat.mul_le_mul b_i41 (by decide : (2 : Nat) ≤ 2)
  step -threadGrindState -grind with U64.add_spec as ⟨i43, h_i43⟩ by
    have hb := Nat.add_le_add b_i38 b_i42
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i43 : i43.val ≤ 1767282935806820565 := by
    rw [h_i43]
    exact Nat.add_le_add b_i38 b_i42
  step -threadGrindState -grind as ⟨z3, h_z3⟩ by scalar_tac
  step -threadGrindState -grind with square_inner_m_spec as ⟨i44, h_i44⟩
  have b_i44 : i44.val ≤ 18155135594135554 := by
    rw [h_i44]
    exact Nat.mul_le_mul b_x0_2 b_i3
  step -threadGrindState -grind with square_inner_m_spec as ⟨i45, h_i45⟩
  have b_i45 : i45.val ≤ 18155135594135554 := by
    rw [h_i45]
    exact Nat.mul_le_mul b_x1_2 b_i2
  step -threadGrindState -grind with U64.add_spec as ⟨i46, h_i46⟩ by
    have hb := Nat.add_le_add b_i44 b_i45
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i46 : i46.val ≤ 36310271188271108 := by
    rw [h_i46]
    exact Nat.add_le_add b_i44 b_i45
  step -threadGrindState -grind with square_inner_m_spec as ⟨i47, h_i47⟩
  have b_i47 : i47.val ≤ 344947576288575526 := by
    rw [h_i47]
    exact Nat.mul_le_mul b_x5_2 b_x8_19
  step -threadGrindState -grind with U64.add_spec as ⟨i48, h_i48⟩ by
    have hb := Nat.add_le_add b_i46 b_i47
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i48 : i48.val ≤ 381257847476846634 := by
    rw [h_i48]
    exact Nat.add_le_add b_i46 b_i47
  step -threadGrindState -grind with square_inner_m_spec as ⟨i49, h_i49⟩
  have b_i49 : i49.val ≤ 172473788144287763 := by
    rw [h_i49]
    exact Nat.mul_le_mul b_i4 b_x9_19
  step -threadGrindState -grind with square_inner_m_spec as ⟨i50, h_i50⟩
  have b_i50 : i50.val ≤ 172473788144287763 := by
    rw [h_i50]
    exact Nat.mul_le_mul b_i6 b_x7_19
  step -threadGrindState -grind with U64.add_spec as ⟨i51, h_i51⟩ by
    have hb := Nat.add_le_add b_i49 b_i50
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i51 : i51.val ≤ 344947576288575526 := by
    rw [h_i51]
    exact Nat.add_le_add b_i49 b_i50
  step -threadGrindState -grind with U64.mul_spec as ⟨i52, h_i52⟩ by
    have hb := Nat.mul_le_mul b_i51 (by decide : (2 : Nat) ≤ 2)
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i52 : i52.val ≤ 689895152577151052 := by
    rw [h_i52]
    exact Nat.mul_le_mul b_i51 (by decide : (2 : Nat) ≤ 2)
  step -threadGrindState -grind with U64.add_spec as ⟨i53, h_i53⟩ by
    have hb := Nat.add_le_add b_i48 b_i52
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i53 : i53.val ≤ 1071153000053997686 := by
    rw [h_i53]
    exact Nat.add_le_add b_i48 b_i52
  step -threadGrindState -grind as ⟨z4, h_z4⟩ by scalar_tac
  step -threadGrindState -grind with square_inner_m_spec as ⟨i54, h_i54⟩
  have b_i54 : i54.val ≤ 36028796482093058 := by
    rw [h_i54]
    exact Nat.mul_le_mul b_x0_2 b_i4
  step -threadGrindState -grind with square_inner_m_spec as ⟨i55, h_i55⟩
  have b_i55 : i55.val ≤ 18296972456755204 := by
    rw [h_i55]
    exact Nat.mul_le_mul b_x1_2 b_x3_2
  step -threadGrindState -grind with U64.add_spec as ⟨i56, h_i56⟩ by
    have hb := Nat.add_le_add b_i54 b_i55
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i56 : i56.val ≤ 54325768938848262 := by
    rw [h_i56]
    exact Nat.add_le_add b_i54 b_i55
  step -threadGrindState -grind with square_inner_m_spec as ⟨i57, h_i57⟩
  have b_i57 : i57.val ≤ 18014398241046529 := by
    rw [h_i57]
    exact Nat.mul_le_mul b_i2 b_i2
  step -threadGrindState -grind with U64.add_spec as ⟨i58, h_i58⟩ by
    have hb := Nat.add_le_add b_i56 b_i57
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i58 : i58.val ≤ 72340167179894791 := by
    rw [h_i58]
    exact Nat.add_le_add b_i56 b_i57
  step -threadGrindState -grind with square_inner_m_spec as ⟨i59, h_i59⟩
  have b_i59 : i59.val ≤ 684547133159768102 := by
    rw [h_i59]
    exact Nat.mul_le_mul b_x6_2 b_x8_19
  step -threadGrindState -grind with U64.add_spec as ⟨i60, h_i60⟩ by
    have hb := Nat.add_le_add b_i58 b_i59
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i60 : i60.val ≤ 756887300339662893 := by
    rw [h_i60]
    exact Nat.add_le_add b_i58 b_i59
  step -threadGrindState -grind with square_inner_m_spec as ⟨i61, h_i61⟩
  have b_i61 : i61.val ≤ 173821238339174438 := by
    rw [h_i61]
    exact Nat.mul_le_mul b_x5_2 b_x9_19
  step -threadGrindState -grind with square_inner_m_spec as ⟨i62, h_i62⟩
  have b_i62 : i62.val ≤ 86910619169587219 := by
    rw [h_i62]
    exact Nat.mul_le_mul b_i7 b_x7_19
  step -threadGrindState -grind with U64.add_spec as ⟨i63, h_i63⟩ by
    have hb := Nat.add_le_add b_i61 b_i62
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i63 : i63.val ≤ 260731857508761657 := by
    rw [h_i63]
    exact Nat.add_le_add b_i61 b_i62
  step -threadGrindState -grind with U64.mul_spec as ⟨i64, h_i64⟩ by
    have hb := Nat.mul_le_mul b_i63 (by decide : (2 : Nat) ≤ 2)
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i64 : i64.val ≤ 521463715017523314 := by
    rw [h_i64]
    exact Nat.mul_le_mul b_i63 (by decide : (2 : Nat) ≤ 2)
  step -threadGrindState -grind with U64.add_spec as ⟨i65, h_i65⟩ by
    have hb := Nat.add_le_add b_i60 b_i64
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i65 : i65.val ≤ 1278351015357186207 := by
    rw [h_i65]
    exact Nat.add_le_add b_i60 b_i64
  step -threadGrindState -grind as ⟨z5, h_z5⟩ by scalar_tac
  step -threadGrindState -grind with square_inner_m_spec as ⟨i66, h_i66⟩
  have b_i66 : i66.val ≤ 18155135594135554 := by
    rw [h_i66]
    exact Nat.mul_le_mul b_x0_2 b_i5
  step -threadGrindState -grind with square_inner_m_spec as ⟨i67, h_i67⟩
  have b_i67 : i67.val ≤ 18155135594135554 := by
    rw [h_i67]
    exact Nat.mul_le_mul b_x1_2 b_i4
  step -threadGrindState -grind with U64.add_spec as ⟨i68, h_i68⟩ by
    have hb := Nat.add_le_add b_i66 b_i67
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i68 : i68.val ≤ 36310271188271108 := by
    rw [h_i68]
    exact Nat.add_le_add b_i66 b_i67
  step -threadGrindState -grind with square_inner_m_spec as ⟨i69, h_i69⟩
  have b_i69 : i69.val ≤ 18155135594135554 := by
    rw [h_i69]
    exact Nat.mul_le_mul b_x2_2 b_i3
  step -threadGrindState -grind with U64.add_spec as ⟨i70, h_i70⟩ by
    have hb := Nat.add_le_add b_i68 b_i69
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i70 : i70.val ≤ 54465406782406662 := by
    rw [h_i70]
    exact Nat.add_le_add b_i68 b_i69
  step -threadGrindState -grind with square_inner_m_spec as ⟨i71, h_i71⟩
  have b_i71 : i71.val ≤ 344947576288575526 := by
    rw [h_i71]
    exact Nat.mul_le_mul b_x7_2 b_x8_19
  step -threadGrindState -grind with U64.add_spec as ⟨i72, h_i72⟩ by
    have hb := Nat.add_le_add b_i70 b_i71
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i72 : i72.val ≤ 399412983070982188 := by
    rw [h_i72]
    exact Nat.add_le_add b_i70 b_i71
  step -threadGrindState -grind with square_inner_m_spec as ⟨i73, h_i73⟩
  have b_i73 : i73.val ≤ 172473788144287763 := by
    rw [h_i73]
    exact Nat.mul_le_mul b_i6 b_x9_19
  step -threadGrindState -grind with U64.mul_spec as ⟨i74, h_i74⟩ by
    have hb := Nat.mul_le_mul b_i73 (by decide : (2 : Nat) ≤ 2)
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i74 : i74.val ≤ 344947576288575526 := by
    rw [h_i74]
    exact Nat.mul_le_mul b_i73 (by decide : (2 : Nat) ≤ 2)
  step -threadGrindState -grind with U64.add_spec as ⟨i75, h_i75⟩ by
    have hb := Nat.add_le_add b_i72 b_i74
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i75 : i75.val ≤ 744360559359557714 := by
    rw [h_i75]
    exact Nat.add_le_add b_i72 b_i74
  step -threadGrindState -grind as ⟨z6, h_z6⟩ by scalar_tac
  step -threadGrindState -grind with square_inner_m_spec as ⟨i76, h_i76⟩
  have b_i76 : i76.val ≤ 36028796482093058 := by
    rw [h_i76]
    exact Nat.mul_le_mul b_x0_2 b_i6
  step -threadGrindState -grind with square_inner_m_spec as ⟨i77, h_i77⟩
  have b_i77 : i77.val ≤ 18296972456755204 := by
    rw [h_i77]
    exact Nat.mul_le_mul b_x1_2 b_x5_2
  step -threadGrindState -grind with U64.add_spec as ⟨i78, h_i78⟩ by
    have hb := Nat.add_le_add b_i76 b_i77
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i78 : i78.val ≤ 54325768938848262 := by
    rw [h_i78]
    exact Nat.add_le_add b_i76 b_i77
  step -threadGrindState -grind with square_inner_m_spec as ⟨i79, h_i79⟩
  have b_i79 : i79.val ≤ 36028796482093058 := by
    rw [h_i79]
    exact Nat.mul_le_mul b_x2_2 b_i4
  step -threadGrindState -grind with U64.add_spec as ⟨i80, h_i80⟩ by
    have hb := Nat.add_le_add b_i78 b_i79
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i80 : i80.val ≤ 90354565420941320 := by
    rw [h_i80]
    exact Nat.add_le_add b_i78 b_i79
  step -threadGrindState -grind with square_inner_m_spec as ⟨i81, h_i81⟩
  have b_i81 : i81.val ≤ 9148486228377602 := by
    rw [h_i81]
    exact Nat.mul_le_mul b_x3_2 b_i3
  step -threadGrindState -grind with U64.add_spec as ⟨i82, h_i82⟩ by
    have hb := Nat.add_le_add b_i80 b_i81
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i82 : i82.val ≤ 99503051649318922 := by
    rw [h_i82]
    exact Nat.add_le_add b_i80 b_i81
  step -threadGrindState -grind with square_inner_m_spec as ⟨i83, h_i83⟩
  have b_i83 : i83.val ≤ 342273566579884051 := by
    rw [h_i83]
    exact Nat.mul_le_mul b_i8 b_x8_19
  step -threadGrindState -grind with U64.add_spec as ⟨i84, h_i84⟩ by
    have hb := Nat.add_le_add b_i82 b_i83
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i84 : i84.val ≤ 441776618229202973 := by
    rw [h_i84]
    exact Nat.add_le_add b_i82 b_i83
  step -threadGrindState -grind with square_inner_m_spec as ⟨i85, h_i85⟩
  have b_i85 : i85.val ≤ 173821238339174438 := by
    rw [h_i85]
    exact Nat.mul_le_mul b_x7_2 b_x9_19
  step -threadGrindState -grind with U64.mul_spec as ⟨i86, h_i86⟩ by
    have hb := Nat.mul_le_mul b_i85 (by decide : (2 : Nat) ≤ 2)
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i86 : i86.val ≤ 347642476678348876 := by
    rw [h_i86]
    exact Nat.mul_le_mul b_i85 (by decide : (2 : Nat) ≤ 2)
  step -threadGrindState -grind with U64.add_spec as ⟨i87, h_i87⟩ by
    have hb := Nat.add_le_add b_i84 b_i86
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i87 : i87.val ≤ 789419094907551849 := by
    rw [h_i87]
    exact Nat.add_le_add b_i84 b_i86
  step -threadGrindState -grind as ⟨z7, h_z7⟩ by scalar_tac
  step -threadGrindState -grind with square_inner_m_spec as ⟨i88, h_i88⟩
  have b_i88 : i88.val ≤ 18155135594135554 := by
    rw [h_i88]
    exact Nat.mul_le_mul b_x0_2 b_i7
  step -threadGrindState -grind with square_inner_m_spec as ⟨i89, h_i89⟩
  have b_i89 : i89.val ≤ 18155135594135554 := by
    rw [h_i89]
    exact Nat.mul_le_mul b_x1_2 b_i6
  step -threadGrindState -grind with U64.add_spec as ⟨i90, h_i90⟩ by
    have hb := Nat.add_le_add b_i88 b_i89
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i90 : i90.val ≤ 36310271188271108 := by
    rw [h_i90]
    exact Nat.add_le_add b_i88 b_i89
  step -threadGrindState -grind with square_inner_m_spec as ⟨i91, h_i91⟩
  have b_i91 : i91.val ≤ 18155135594135554 := by
    rw [h_i91]
    exact Nat.mul_le_mul b_x2_2 b_i5
  step -threadGrindState -grind with U64.add_spec as ⟨i92, h_i92⟩ by
    have hb := Nat.add_le_add b_i90 b_i91
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i92 : i92.val ≤ 54465406782406662 := by
    rw [h_i92]
    exact Nat.add_le_add b_i90 b_i91
  step -threadGrindState -grind with square_inner_m_spec as ⟨i93, h_i93⟩
  have b_i93 : i93.val ≤ 18155135594135554 := by
    rw [h_i93]
    exact Nat.mul_le_mul b_x3_2 b_i4
  step -threadGrindState -grind with U64.add_spec as ⟨i94, h_i94⟩ by
    have hb := Nat.add_le_add b_i92 b_i93
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i94 : i94.val ≤ 72620542376542216 := by
    rw [h_i94]
    exact Nat.add_le_add b_i92 b_i93
  step -threadGrindState -grind with square_inner_m_spec as ⟨i95, h_i95⟩
  have b_i95 : i95.val ≤ 172473788144287763 := by
    rw [h_i95]
    exact Nat.mul_le_mul b_i8 b_x9_19
  step -threadGrindState -grind with U64.mul_spec as ⟨i96, h_i96⟩ by
    have hb := Nat.mul_le_mul b_i95 (by decide : (2 : Nat) ≤ 2)
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i96 : i96.val ≤ 344947576288575526 := by
    rw [h_i96]
    exact Nat.mul_le_mul b_i95 (by decide : (2 : Nat) ≤ 2)
  step -threadGrindState -grind with U64.add_spec as ⟨i97, h_i97⟩ by
    have hb := Nat.add_le_add b_i94 b_i96
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i97 : i97.val ≤ 417568118665117742 := by
    rw [h_i97]
    exact Nat.add_le_add b_i94 b_i96
  step -threadGrindState -grind as ⟨z8, h_z8⟩ by scalar_tac
  step -threadGrindState -grind with square_inner_m_spec as ⟨i98, h_i98⟩
  have b_i98 : i98.val ≤ 36028796482093058 := by
    rw [h_i98]
    exact Nat.mul_le_mul b_x0_2 b_i8
  step -threadGrindState -grind with square_inner_m_spec as ⟨i99, h_i99⟩
  have b_i99 : i99.val ≤ 18296972456755204 := by
    rw [h_i99]
    exact Nat.mul_le_mul b_x1_2 b_x7_2
  step -threadGrindState -grind with U64.add_spec as ⟨i100, h_i100⟩ by
    have hb := Nat.add_le_add b_i98 b_i99
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i100 : i100.val ≤ 54325768938848262 := by
    rw [h_i100]
    exact Nat.add_le_add b_i98 b_i99
  step -threadGrindState -grind with square_inner_m_spec as ⟨i101, h_i101⟩
  have b_i101 : i101.val ≤ 36028796482093058 := by
    rw [h_i101]
    exact Nat.mul_le_mul b_x2_2 b_i6
  step -threadGrindState -grind with U64.add_spec as ⟨i102, h_i102⟩ by
    have hb := Nat.add_le_add b_i100 b_i101
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i102 : i102.val ≤ 90354565420941320 := by
    rw [h_i102]
    exact Nat.add_le_add b_i100 b_i101
  step -threadGrindState -grind with square_inner_m_spec as ⟨i103, h_i103⟩
  have b_i103 : i103.val ≤ 18296972456755204 := by
    rw [h_i103]
    exact Nat.mul_le_mul b_x3_2 b_x5_2
  step -threadGrindState -grind with U64.add_spec as ⟨i104, h_i104⟩ by
    have hb := Nat.add_le_add b_i102 b_i103
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i104 : i104.val ≤ 108651537877696524 := by
    rw [h_i104]
    exact Nat.add_le_add b_i102 b_i103
  step -threadGrindState -grind with square_inner_m_spec as ⟨i105, h_i105⟩
  have b_i105 : i105.val ≤ 18014398241046529 := by
    rw [h_i105]
    exact Nat.mul_le_mul b_i4 b_i4
  step -threadGrindState -grind with U64.add_spec as ⟨i106, h_i106⟩ by
    have hb := Nat.add_le_add b_i104 b_i105
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i106 : i106.val ≤ 126665936118743053 := by
    rw [h_i106]
    exact Nat.add_le_add b_i104 b_i105
  step -threadGrindState -grind with square_inner_m_spec as ⟨i107, h_i107⟩
  have b_i107 : i107.val ≤ 86910619169587219 := by
    rw [h_i107]
    exact Nat.mul_le_mul b_i9 b_x9_19
  step -threadGrindState -grind with U64.mul_spec as ⟨i108, h_i108⟩ by
    have hb := Nat.mul_le_mul b_i107 (by decide : (2 : Nat) ≤ 2)
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i108 : i108.val ≤ 173821238339174438 := by
    rw [h_i108]
    exact Nat.mul_le_mul b_i107 (by decide : (2 : Nat) ≤ 2)
  step -threadGrindState -grind with U64.add_spec as ⟨i109, h_i109⟩ by
    have hb := Nat.add_le_add b_i106 b_i108
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i109 : i109.val ≤ 300487174457917491 := by
    rw [h_i109]
    exact Nat.add_le_add b_i106 b_i108
  step -threadGrindState -grind as ⟨z9, h_z9⟩ by scalar_tac
  step -threadGrindState -grind with square_inner_m_spec as ⟨i110, h_i110⟩
  have b_i110 : i110.val ≤ 18155135594135554 := by
    rw [h_i110]
    exact Nat.mul_le_mul b_x0_2 b_i9
  step -threadGrindState -grind with square_inner_m_spec as ⟨i111, h_i111⟩
  have b_i111 : i111.val ≤ 18155135594135554 := by
    rw [h_i111]
    exact Nat.mul_le_mul b_x1_2 b_i8
  step -threadGrindState -grind with U64.add_spec as ⟨i112, h_i112⟩ by
    have hb := Nat.add_le_add b_i110 b_i111
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i112 : i112.val ≤ 36310271188271108 := by
    rw [h_i112]
    exact Nat.add_le_add b_i110 b_i111
  step -threadGrindState -grind with square_inner_m_spec as ⟨i113, h_i113⟩
  have b_i113 : i113.val ≤ 18155135594135554 := by
    rw [h_i113]
    exact Nat.mul_le_mul b_x2_2 b_i7
  step -threadGrindState -grind with U64.add_spec as ⟨i114, h_i114⟩ by
    have hb := Nat.add_le_add b_i112 b_i113
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i114 : i114.val ≤ 54465406782406662 := by
    rw [h_i114]
    exact Nat.add_le_add b_i112 b_i113
  step -threadGrindState -grind with square_inner_m_spec as ⟨i115, h_i115⟩
  have b_i115 : i115.val ≤ 18155135594135554 := by
    rw [h_i115]
    exact Nat.mul_le_mul b_x3_2 b_i6
  step -threadGrindState -grind with U64.add_spec as ⟨i116, h_i116⟩ by
    have hb := Nat.add_le_add b_i114 b_i115
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i116 : i116.val ≤ 72620542376542216 := by
    rw [h_i116]
    exact Nat.add_le_add b_i114 b_i115
  step -threadGrindState -grind with square_inner_m_spec as ⟨i117, h_i117⟩
  have b_i117 : i117.val ≤ 18155135594135554 := by
    rw [h_i117]
    exact Nat.mul_le_mul b_x4_2 b_i5
  step -threadGrindState -grind with U64.add_spec as ⟨i118, h_i118⟩ by
    have hb := Nat.add_le_add b_i116 b_i117
    exact hb.trans (by norm_num [U32.max_eq, U64.max_eq])
  have b_i118 : i118.val ≤ 90775677970677770 := by
    rw [h_i118]
    exact Nat.add_le_add b_i116 b_i117
  step -threadGrindState -grind as ⟨result, h_result⟩ by scalar_tac
  constructor
  -- The high-degree terms differ from the folded result by this explicit multiple of p.
  · have h_value : toNat self ^ 2 = Array.uScalarToNatField2625 result + p *
      (2 ^ 2 * self[1]!.val * self[9]!.val +
        2 ^ 1 * self[2]!.val * self[8]!.val +
        2 ^ 27 * self[2]!.val * self[9]!.val +
        2 ^ 2 * self[3]!.val * self[7]!.val +
        2 ^ 27 * self[3]!.val * self[8]!.val +
        2 ^ 53 * self[3]!.val * self[9]!.val +
        2 ^ 1 * self[4]!.val * self[6]!.val +
        2 ^ 27 * self[4]!.val * self[7]!.val +
        2 ^ 52 * self[4]!.val * self[8]!.val +
        2 ^ 78 * self[4]!.val * self[9]!.val +
        2 ^ 1 * self[5]!.val * self[5]!.val +
        2 ^ 27 * self[5]!.val * self[6]!.val +
        2 ^ 53 * self[5]!.val * self[7]!.val +
        2 ^ 78 * self[5]!.val * self[8]!.val +
        2 ^ 104 * self[5]!.val * self[9]!.val +
        2 ^ 51 * self[6]!.val * self[6]!.val +
        2 ^ 78 * self[6]!.val * self[7]!.val +
        2 ^ 103 * self[6]!.val * self[8]!.val +
        2 ^ 129 * self[6]!.val * self[9]!.val +
        2 ^ 103 * self[7]!.val * self[7]!.val +
        2 ^ 129 * self[7]!.val * self[8]!.val +
        2 ^ 155 * self[7]!.val * self[9]!.val +
        2 ^ 153 * self[8]!.val * self[8]!.val +
        2 ^ 180 * self[8]!.val * self[9]!.val +
        2 ^ 205 * self[9]!.val * self[9]!.val) := by
      simp only [h_result, h_z9, h_z8, h_z7, h_z6, h_z5, h_z4, h_z3, h_z2, h_z1, toNat,
        Array.uScalarToNatField2625,
        Finset.sum_range_succ, Finset.sum_range_zero, Array.getElem!_Nat_eq,
        Array.set_val_eq, Array.repeat, UScalar.ofNatCore_val_eq]
      norm_num [p]
      simp only [h_i118, h_i117, h_i116, h_i115, h_i114, h_i113, h_i112, h_i111, h_i110, h_i109,
        h_i108, h_i107, h_i106, h_i105, h_i104, h_i103, h_i102, h_i101, h_i100, h_i99, h_i98, h_i97,
        h_i96, h_i95, h_i94, h_i93, h_i92, h_i91, h_i90, h_i89, h_i88, h_i87, h_i86, h_i85, h_i84,
        h_i83, h_i82, h_i81, h_i80, h_i79, h_i78, h_i77, h_i76, h_i75, h_i74, h_i73, h_i72, h_i71,
        h_i70, h_i69, h_i68, h_i67, h_i66, h_i65, h_i64, h_i63, h_i62, h_i61, h_i60, h_i59, h_i58,
        h_i57, h_i56, h_i55, h_i54, h_i53, h_i52, h_i51, h_i50, h_i49, h_i48, h_i47, h_i46, h_i45,
        h_i44, h_i43, h_i42, h_i41, h_i40, h_i39, h_i38, h_i37, h_i36, h_i35, h_i34, h_i33, h_i32,
        h_i31, h_i30, h_i29, h_i28, h_i27, h_i26, h_i25, h_i24, h_i23, h_i22, h_i21, h_i20, h_i19,
        h_i18, h_i17, h_i16, h_i15, h_i14, h_i13, h_i12, h_i11, h_i10, h_x9_19, h_i9, h_x8_19, h_i8,
        h_x7_19, h_x6_19, h_x5_19, h_x7_2, h_i7, h_x6_2, h_i6, h_x5_2, h_i5, h_x4_2, h_i4, h_x3_2,
        h_i3, h_x2_2, h_i2, h_x1_2, h_i1, h_x0_2, h_i]
      ring
    rw [h_value, Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]
  · intro j hj
    interval_cases j <;>
      simp only [h_result, h_z9, h_z8, h_z7, h_z6, h_z5, h_z4, h_z3, h_z2, h_z1,
        Array.getElem!_Nat_eq, Array.set_val_eq,
        Array.repeat, UScalar.ofNatCore_val_eq] <;>
      norm_num <;> omega

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

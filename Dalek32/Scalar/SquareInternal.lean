/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Definitions
import Dalek32.Lint.Basic
import Dalek32.Scalar.Index
import Dalek32.Scalar.M
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Spec theorem for `square_internal`

Squares nine radix-`2^29` limbs into seventeen coefficients.
Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 292-323.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::square_internal`**

Returns the exact square with coefficients below `2^62`. -/
@[step]
theorem square_internal_spec (a : Scalar29)
    (h_a : ∀ i < 9, a[i]!.val < limbRadix) :
    square_internal a ⦃ (result : Array U64 17#usize) =>
      wideAsNat result = asNat a ^ 2 ∧
      (∀ i < 17, result[i]!.val < 2 ^ 62) ⦄ := by
  simp only [limbRadix] at h_a
  unfold square_internal
  -- Explicit preconditions keep elaboration within the default heartbeat budget.
  step -threadGrindState -grind with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨i, hi⟩ by
    decide
  have hi_bound : i.val ≤ 2 ^ 29 := by
    simpa only [hi, Array.getElem!_Nat_eq] using (h_a 0 (by decide)).le
  step -threadGrindState -grind with U32.mul_spec as ⟨i1, hi1⟩ by
    exact (Nat.mul_le_mul_right 2 hi_bound).trans (by rw [U32.max_eq]; decide)
  have hi1_bound : i1.val ≤ 2 ^ 30 := by omega
  step -threadGrindState -grind with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨i2, hi2⟩ by
    decide
  have hi2_bound : i2.val ≤ 2 ^ 29 := by
    simpa only [hi2, Array.getElem!_Nat_eq] using (h_a 1 (by decide)).le
  step -threadGrindState -grind with U32.mul_spec as ⟨i3, hi3⟩ by
    exact (Nat.mul_le_mul_right 2 hi2_bound).trans (by rw [U32.max_eq]; decide)
  have hi3_bound : i3.val ≤ 2 ^ 30 := by omega
  step -threadGrindState -grind with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨i4, hi4⟩ by
    decide
  have hi4_bound : i4.val ≤ 2 ^ 29 := by
    simpa only [hi4, Array.getElem!_Nat_eq] using (h_a 2 (by decide)).le
  step -threadGrindState -grind with U32.mul_spec as ⟨i5, hi5⟩ by
    exact (Nat.mul_le_mul_right 2 hi4_bound).trans (by rw [U32.max_eq]; decide)
  have hi5_bound : i5.val ≤ 2 ^ 30 := by omega
  step -threadGrindState -grind with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨i6, hi6⟩ by
    decide
  have hi6_bound : i6.val ≤ 2 ^ 29 := by
    simpa only [hi6, Array.getElem!_Nat_eq] using (h_a 3 (by decide)).le
  step -threadGrindState -grind with U32.mul_spec as ⟨i7, hi7⟩ by
    exact (Nat.mul_le_mul_right 2 hi6_bound).trans (by rw [U32.max_eq]; decide)
  have hi7_bound : i7.val ≤ 2 ^ 30 := by omega
  step -threadGrindState -grind with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨i8, hi8⟩ by
    decide
  have hi8_bound : i8.val ≤ 2 ^ 29 := by
    simpa only [hi8, Array.getElem!_Nat_eq] using (h_a 4 (by decide)).le
  step -threadGrindState -grind with U32.mul_spec as ⟨i9, hi9⟩ by
    exact (Nat.mul_le_mul_right 2 hi8_bound).trans (by rw [U32.max_eq]; decide)
  have hi9_bound : i9.val ≤ 2 ^ 30 := by omega
  step -threadGrindState -grind with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨i10, hi10⟩ by
    decide
  have hi10_bound : i10.val ≤ 2 ^ 29 := by
    simpa only [hi10, Array.getElem!_Nat_eq] using (h_a 5 (by decide)).le
  step -threadGrindState -grind with U32.mul_spec as ⟨i11, hi11⟩ by
    exact (Nat.mul_le_mul_right 2 hi10_bound).trans (by rw [U32.max_eq]; decide)
  have hi11_bound : i11.val ≤ 2 ^ 30 := by omega
  step -threadGrindState -grind with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨i12, hi12⟩ by
    decide
  have hi12_bound : i12.val ≤ 2 ^ 29 := by
    simpa only [hi12, Array.getElem!_Nat_eq] using (h_a 6 (by decide)).le
  step -threadGrindState -grind with U32.mul_spec as ⟨i13, hi13⟩ by
    exact (Nat.mul_le_mul_right 2 hi12_bound).trans (by rw [U32.max_eq]; decide)
  have hi13_bound : i13.val ≤ 2 ^ 30 := by omega
  step -threadGrindState -grind with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨i14, hi14⟩ by
    decide
  have hi14_bound : i14.val ≤ 2 ^ 29 := by
    simpa only [hi14, Array.getElem!_Nat_eq] using (h_a 7 (by decide)).le
  step -threadGrindState -grind with U32.mul_spec as ⟨i15, hi15⟩ by
    exact (Nat.mul_le_mul_right 2 hi14_bound).trans (by rw [U32.max_eq]; decide)
  have hi15_bound : i15.val ≤ 2 ^ 30 := by omega
  -- Coefficient 0.
  step with m_spec_bounded _ _ hi_bound hi_bound as ⟨i16, hi16, hi16_mul_bound⟩
  have hi16_bound : i16.val < 2 ^ 62 :=
    lt_of_le_of_lt hi16_mul_bound (by decide)
  clear hi16_mul_bound
  step -threadGrindState -grind with Array.index_usize_spec as ⟨i17, hi17⟩ by
    change 0 < (8 : Nat)
    decide
  simp only [Array.make, List.getElem_cons_zero] at hi17
  simp only [hi17]
  clear hi17 i17
  -- Coefficient 1.
  step with m_spec_bounded _ _ hi1_bound hi2_bound as ⟨i18, hi18, hi18_mul_bound⟩
  have hi18_bound : i18.val < 2 ^ 62 :=
    lt_of_le_of_lt hi18_mul_bound (by decide)
  simp only [hi1] at hi18
  clear hi18_mul_bound
  -- Coefficient 2.
  step with m_spec_bounded _ _ hi1_bound hi4_bound as ⟨i19, hi19, hi19_mul_bound⟩
  step with m_spec_bounded _ _ hi2_bound hi2_bound as ⟨i20, hi20, hi20_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i21, hi21⟩ by
    exact (Nat.add_le_add hi19_mul_bound hi20_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi21_add_bound := Nat.add_le_add hi19_mul_bound hi20_mul_bound
  rw [← hi21] at hi21_add_bound
  have hi21_bound : i21.val < 2 ^ 62 :=
    lt_of_le_of_lt hi21_add_bound (by decide)
  clear hi21_add_bound
  simp only [hi20, hi19, hi1] at hi21
  clear hi19_mul_bound hi20_mul_bound hi20 hi19 i20 i19
  -- Coefficient 3.
  step with m_spec_bounded _ _ hi1_bound hi6_bound as ⟨i22, hi22, hi22_mul_bound⟩
  step -threadGrindState -grind with Array.index_usize_spec as ⟨i23, hi23⟩ by
    change 1 < (8 : Nat)
    decide
  simp only [Array.make, List.getElem_cons_zero,
    List.getElem_cons_succ] at hi23
  simp only [hi23]
  clear hi23 i23
  step with m_spec_bounded _ _ hi3_bound hi4_bound as ⟨i24, hi24, hi24_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i25, hi25⟩ by
    exact (Nat.add_le_add hi22_mul_bound hi24_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi25_add_bound := Nat.add_le_add hi22_mul_bound hi24_mul_bound
  rw [← hi25] at hi25_add_bound
  have hi25_bound : i25.val < 2 ^ 62 :=
    lt_of_le_of_lt hi25_add_bound (by decide)
  clear hi25_add_bound
  simp only [hi24, hi22, hi3, hi1] at hi25
  clear hi22_mul_bound hi24_mul_bound hi24 hi22 i24 i22
  -- Coefficient 4.
  step with m_spec_bounded _ _ hi1_bound hi8_bound as ⟨i26, hi26, hi26_mul_bound⟩
  step with m_spec_bounded _ _ hi3_bound hi6_bound as ⟨i27, hi27, hi27_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i28, hi28⟩ by
    exact (Nat.add_le_add hi26_mul_bound hi27_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi28_add_bound := Nat.add_le_add hi26_mul_bound hi27_mul_bound
  rw [← hi28] at hi28_add_bound
  step with m_spec_bounded _ _ hi4_bound hi4_bound as ⟨i29, hi29, hi29_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i30, hi30⟩ by
    exact (Nat.add_le_add hi28_add_bound hi29_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi30_add_bound := Nat.add_le_add hi28_add_bound hi29_mul_bound
  rw [← hi30] at hi30_add_bound
  have hi30_bound : i30.val < 2 ^ 62 :=
    lt_of_le_of_lt hi30_add_bound (by decide)
  clear hi30_add_bound hi28_add_bound
  simp only [hi29, hi28, hi27, hi26, hi3, hi1] at hi30
  clear hi26_mul_bound hi27_mul_bound hi29_mul_bound hi29 hi28 hi27 hi26 i29 i28 i27 i26
  -- Coefficient 5.
  step with m_spec_bounded _ _ hi1_bound hi10_bound as ⟨i31, hi31, hi31_mul_bound⟩
  step with m_spec_bounded _ _ hi3_bound hi8_bound as ⟨i32, hi32, hi32_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i33, hi33⟩ by
    exact (Nat.add_le_add hi31_mul_bound hi32_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi33_add_bound := Nat.add_le_add hi31_mul_bound hi32_mul_bound
  rw [← hi33] at hi33_add_bound
  step -threadGrindState -grind with Array.index_usize_spec as ⟨i34, hi34⟩ by
    change 2 < (8 : Nat)
    decide
  simp only [Array.make, List.getElem_cons_zero,
    List.getElem_cons_succ] at hi34
  simp only [hi34]
  clear hi34 i34
  step with m_spec_bounded _ _ hi5_bound hi6_bound as ⟨i35, hi35, hi35_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i36, hi36⟩ by
    exact (Nat.add_le_add hi33_add_bound hi35_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi36_add_bound := Nat.add_le_add hi33_add_bound hi35_mul_bound
  rw [← hi36] at hi36_add_bound
  have hi36_bound : i36.val < 2 ^ 62 :=
    lt_of_le_of_lt hi36_add_bound (by decide)
  clear hi36_add_bound hi33_add_bound
  simp only [hi35, hi33, hi32, hi31, hi5, hi3, hi1] at hi36
  clear hi31_mul_bound hi32_mul_bound hi35_mul_bound hi35 hi33 hi32 hi31 i35 i33 i32 i31
  -- Coefficient 6.
  step with m_spec_bounded _ _ hi1_bound hi12_bound as ⟨i37, hi37, hi37_mul_bound⟩
  step with m_spec_bounded _ _ hi3_bound hi10_bound as ⟨i38, hi38, hi38_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i39, hi39⟩ by
    exact (Nat.add_le_add hi37_mul_bound hi38_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi39_add_bound := Nat.add_le_add hi37_mul_bound hi38_mul_bound
  rw [← hi39] at hi39_add_bound
  step with m_spec_bounded _ _ hi5_bound hi8_bound as ⟨i40, hi40, hi40_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i41, hi41⟩ by
    exact (Nat.add_le_add hi39_add_bound hi40_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi41_add_bound := Nat.add_le_add hi39_add_bound hi40_mul_bound
  rw [← hi41] at hi41_add_bound
  step with m_spec_bounded _ _ hi6_bound hi6_bound as ⟨i42, hi42, hi42_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i43, hi43⟩ by
    exact (Nat.add_le_add hi41_add_bound hi42_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi43_add_bound := Nat.add_le_add hi41_add_bound hi42_mul_bound
  rw [← hi43] at hi43_add_bound
  have hi43_bound : i43.val < 2 ^ 62 :=
    lt_of_le_of_lt hi43_add_bound (by decide)
  clear hi43_add_bound hi41_add_bound hi39_add_bound
  simp only [hi42, hi41, hi40, hi39, hi38, hi37, hi5, hi3, hi1] at hi43
  clear hi37_mul_bound hi38_mul_bound hi40_mul_bound hi42_mul_bound hi42 hi41 hi40 hi39 hi38 hi37
  clear i42 i41 i40 i39 i38 i37
  -- Coefficient 7.
  step with m_spec_bounded _ _ hi1_bound hi14_bound as ⟨i44, hi44, hi44_mul_bound⟩
  step with m_spec_bounded _ _ hi3_bound hi12_bound as ⟨i45, hi45, hi45_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i46, hi46⟩ by
    exact (Nat.add_le_add hi44_mul_bound hi45_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi46_add_bound := Nat.add_le_add hi44_mul_bound hi45_mul_bound
  rw [← hi46] at hi46_add_bound
  step with m_spec_bounded _ _ hi5_bound hi10_bound as ⟨i47, hi47, hi47_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i48, hi48⟩ by
    exact (Nat.add_le_add hi46_add_bound hi47_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi48_add_bound := Nat.add_le_add hi46_add_bound hi47_mul_bound
  rw [← hi48] at hi48_add_bound
  step -threadGrindState -grind with Array.index_usize_spec as ⟨i49, hi49⟩ by
    change 3 < (8 : Nat)
    decide
  simp only [Array.make, List.getElem_cons_zero,
    List.getElem_cons_succ] at hi49
  simp only [hi49]
  clear hi49 i49
  step with m_spec_bounded _ _ hi7_bound hi8_bound as ⟨i50, hi50, hi50_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i51, hi51⟩ by
    exact (Nat.add_le_add hi48_add_bound hi50_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi51_add_bound := Nat.add_le_add hi48_add_bound hi50_mul_bound
  rw [← hi51] at hi51_add_bound
  have hi51_bound : i51.val < 2 ^ 62 :=
    lt_of_le_of_lt hi51_add_bound (by decide)
  clear hi51_add_bound hi48_add_bound hi46_add_bound
  simp only [hi50, hi48, hi47, hi46, hi45, hi44, hi7, hi5, hi3, hi1] at hi51
  clear hi44_mul_bound hi45_mul_bound hi47_mul_bound hi50_mul_bound hi50 hi48 hi47 hi46 hi45 hi44
  clear i50 i48 i47 i46 i45 i44
  step -threadGrindState -grind with Insts.CoreOpsIndexIndexUsizeU32.index_spec as ⟨i52, hi52⟩ by
    decide
  have hi52_bound : i52.val ≤ 2 ^ 29 := by
    simpa only [hi52, Array.getElem!_Nat_eq] using (h_a 8 (by decide)).le
  -- Coefficient 8.
  step with m_spec_bounded _ _ hi1_bound hi52_bound as ⟨i53, hi53, hi53_mul_bound⟩
  step with m_spec_bounded _ _ hi3_bound hi14_bound as ⟨i54, hi54, hi54_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i55, hi55⟩ by
    exact (Nat.add_le_add hi53_mul_bound hi54_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi55_add_bound := Nat.add_le_add hi53_mul_bound hi54_mul_bound
  rw [← hi55] at hi55_add_bound
  step with m_spec_bounded _ _ hi5_bound hi12_bound as ⟨i56, hi56, hi56_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i57, hi57⟩ by
    exact (Nat.add_le_add hi55_add_bound hi56_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi57_add_bound := Nat.add_le_add hi55_add_bound hi56_mul_bound
  rw [← hi57] at hi57_add_bound
  step with m_spec_bounded _ _ hi7_bound hi10_bound as ⟨i58, hi58, hi58_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i59, hi59⟩ by
    exact (Nat.add_le_add hi57_add_bound hi58_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi59_add_bound := Nat.add_le_add hi57_add_bound hi58_mul_bound
  rw [← hi59] at hi59_add_bound
  step with m_spec_bounded _ _ hi8_bound hi8_bound as ⟨i60, hi60, hi60_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i61, hi61⟩ by
    exact (Nat.add_le_add hi59_add_bound hi60_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi61_add_bound := Nat.add_le_add hi59_add_bound hi60_mul_bound
  rw [← hi61] at hi61_add_bound
  have hi61_bound : i61.val < 2 ^ 62 :=
    lt_of_le_of_lt hi61_add_bound (by decide)
  clear hi61_add_bound hi59_add_bound hi57_add_bound hi55_add_bound
  simp only [hi60, hi59, hi58, hi57, hi56, hi55, hi54, hi53, hi7, hi5, hi3, hi1] at hi61
  clear hi53_mul_bound hi54_mul_bound hi56_mul_bound hi58_mul_bound hi60_mul_bound hi60 hi59 hi58
  clear hi57 hi56 hi55 hi54 hi53 i60 i59 i58 i57 i56 i55 i54 i53
  -- Coefficient 9.
  step with m_spec_bounded _ _ hi3_bound hi52_bound as ⟨i62, hi62, hi62_mul_bound⟩
  step with m_spec_bounded _ _ hi5_bound hi14_bound as ⟨i63, hi63, hi63_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i64, hi64⟩ by
    exact (Nat.add_le_add hi62_mul_bound hi63_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi64_add_bound := Nat.add_le_add hi62_mul_bound hi63_mul_bound
  rw [← hi64] at hi64_add_bound
  step with m_spec_bounded _ _ hi7_bound hi12_bound as ⟨i65, hi65, hi65_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i66, hi66⟩ by
    exact (Nat.add_le_add hi64_add_bound hi65_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi66_add_bound := Nat.add_le_add hi64_add_bound hi65_mul_bound
  rw [← hi66] at hi66_add_bound
  step -threadGrindState -grind with Array.index_usize_spec as ⟨i67, hi67⟩ by
    change 4 < (8 : Nat)
    decide
  simp only [Array.make, List.getElem_cons_zero,
    List.getElem_cons_succ] at hi67
  simp only [hi67]
  clear hi67 i67
  step with m_spec_bounded _ _ hi9_bound hi10_bound as ⟨i68, hi68, hi68_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i69, hi69⟩ by
    exact (Nat.add_le_add hi66_add_bound hi68_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi69_add_bound := Nat.add_le_add hi66_add_bound hi68_mul_bound
  rw [← hi69] at hi69_add_bound
  have hi69_bound : i69.val < 2 ^ 62 :=
    lt_of_le_of_lt hi69_add_bound (by decide)
  clear hi69_add_bound hi66_add_bound hi64_add_bound
  simp only [hi68, hi66, hi65, hi64, hi63, hi62, hi9, hi7, hi5, hi3] at hi69
  clear hi62_mul_bound hi63_mul_bound hi65_mul_bound hi68_mul_bound hi68 hi66 hi65 hi64 hi63 hi62
  clear i68 i66 i65 i64 i63 i62
  -- Coefficient 10.
  step with m_spec_bounded _ _ hi5_bound hi52_bound as ⟨i70, hi70, hi70_mul_bound⟩
  step with m_spec_bounded _ _ hi7_bound hi14_bound as ⟨i71, hi71, hi71_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i72, hi72⟩ by
    exact (Nat.add_le_add hi70_mul_bound hi71_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi72_add_bound := Nat.add_le_add hi70_mul_bound hi71_mul_bound
  rw [← hi72] at hi72_add_bound
  step with m_spec_bounded _ _ hi9_bound hi12_bound as ⟨i73, hi73, hi73_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i74, hi74⟩ by
    exact (Nat.add_le_add hi72_add_bound hi73_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi74_add_bound := Nat.add_le_add hi72_add_bound hi73_mul_bound
  rw [← hi74] at hi74_add_bound
  step with m_spec_bounded _ _ hi10_bound hi10_bound as ⟨i75, hi75, hi75_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i76, hi76⟩ by
    exact (Nat.add_le_add hi74_add_bound hi75_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi76_add_bound := Nat.add_le_add hi74_add_bound hi75_mul_bound
  rw [← hi76] at hi76_add_bound
  have hi76_bound : i76.val < 2 ^ 62 :=
    lt_of_le_of_lt hi76_add_bound (by decide)
  clear hi76_add_bound hi74_add_bound hi72_add_bound
  simp only [hi75, hi74, hi73, hi72, hi71, hi70, hi9, hi7, hi5] at hi76
  clear hi70_mul_bound hi71_mul_bound hi73_mul_bound hi75_mul_bound hi75 hi74 hi73 hi72 hi71 hi70
  clear i75 i74 i73 i72 i71 i70
  -- Coefficient 11.
  step with m_spec_bounded _ _ hi7_bound hi52_bound as ⟨i77, hi77, hi77_mul_bound⟩
  step with m_spec_bounded _ _ hi9_bound hi14_bound as ⟨i78, hi78, hi78_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i79, hi79⟩ by
    exact (Nat.add_le_add hi77_mul_bound hi78_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi79_add_bound := Nat.add_le_add hi77_mul_bound hi78_mul_bound
  rw [← hi79] at hi79_add_bound
  step -threadGrindState -grind with Array.index_usize_spec as ⟨i80, hi80⟩ by
    change 5 < (8 : Nat)
    decide
  simp only [Array.make, List.getElem_cons_zero,
    List.getElem_cons_succ] at hi80
  simp only [hi80]
  clear hi80 i80
  step with m_spec_bounded _ _ hi11_bound hi12_bound as ⟨i81, hi81, hi81_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i82, hi82⟩ by
    exact (Nat.add_le_add hi79_add_bound hi81_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi82_add_bound := Nat.add_le_add hi79_add_bound hi81_mul_bound
  rw [← hi82] at hi82_add_bound
  have hi82_bound : i82.val < 2 ^ 62 :=
    lt_of_le_of_lt hi82_add_bound (by decide)
  clear hi82_add_bound hi79_add_bound
  simp only [hi81, hi79, hi78, hi77, hi11, hi9, hi7] at hi82
  clear hi77_mul_bound hi78_mul_bound hi81_mul_bound hi81 hi79 hi78 hi77 i81 i79 i78 i77
  -- Coefficient 12.
  step with m_spec_bounded _ _ hi9_bound hi52_bound as ⟨i83, hi83, hi83_mul_bound⟩
  step with m_spec_bounded _ _ hi11_bound hi14_bound as ⟨i84, hi84, hi84_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i85, hi85⟩ by
    exact (Nat.add_le_add hi83_mul_bound hi84_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi85_add_bound := Nat.add_le_add hi83_mul_bound hi84_mul_bound
  rw [← hi85] at hi85_add_bound
  step with m_spec_bounded _ _ hi12_bound hi12_bound as ⟨i86, hi86, hi86_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i87, hi87⟩ by
    exact (Nat.add_le_add hi85_add_bound hi86_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi87_add_bound := Nat.add_le_add hi85_add_bound hi86_mul_bound
  rw [← hi87] at hi87_add_bound
  have hi87_bound : i87.val < 2 ^ 62 :=
    lt_of_le_of_lt hi87_add_bound (by decide)
  clear hi87_add_bound hi85_add_bound
  simp only [hi86, hi85, hi84, hi83, hi11, hi9] at hi87
  clear hi83_mul_bound hi84_mul_bound hi86_mul_bound hi86 hi85 hi84 hi83 i86 i85 i84 i83
  -- Coefficient 13.
  step with m_spec_bounded _ _ hi11_bound hi52_bound as ⟨i88, hi88, hi88_mul_bound⟩
  step -threadGrindState -grind with Array.index_usize_spec as ⟨i89, hi89⟩ by
    change 6 < (8 : Nat)
    decide
  simp only [Array.make, List.getElem_cons_zero,
    List.getElem_cons_succ] at hi89
  simp only [hi89]
  clear hi89 i89
  step with m_spec_bounded _ _ hi13_bound hi14_bound as ⟨i90, hi90, hi90_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i91, hi91⟩ by
    exact (Nat.add_le_add hi88_mul_bound hi90_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi91_add_bound := Nat.add_le_add hi88_mul_bound hi90_mul_bound
  rw [← hi91] at hi91_add_bound
  have hi91_bound : i91.val < 2 ^ 62 :=
    lt_of_le_of_lt hi91_add_bound (by decide)
  clear hi91_add_bound
  simp only [hi90, hi88, hi13, hi11] at hi91
  clear hi88_mul_bound hi90_mul_bound hi90 hi88 i90 i88
  -- Coefficient 14.
  step with m_spec_bounded _ _ hi13_bound hi52_bound as ⟨i92, hi92, hi92_mul_bound⟩
  step with m_spec_bounded _ _ hi14_bound hi14_bound as ⟨i93, hi93, hi93_mul_bound⟩
  step -threadGrindState -grind with U64.add_spec as ⟨i94, hi94⟩ by
    exact (Nat.add_le_add hi92_mul_bound hi93_mul_bound).trans (by rw [U64.max_eq]; decide)
  have hi94_add_bound := Nat.add_le_add hi92_mul_bound hi93_mul_bound
  rw [← hi94] at hi94_add_bound
  have hi94_bound : i94.val < 2 ^ 62 :=
    lt_of_le_of_lt hi94_add_bound (by decide)
  clear hi94_add_bound
  simp only [hi93, hi92, hi13] at hi94
  clear hi92_mul_bound hi93_mul_bound hi93 hi92 i93 i92
  step -threadGrindState -grind with Array.index_usize_spec as ⟨i95, hi95⟩ by
    change 7 < (8 : Nat)
    decide
  simp only [Array.make, List.getElem_cons_zero,
    List.getElem_cons_succ] at hi95
  simp only [hi95]
  clear hi95 i95
  -- Coefficient 15.
  step with m_spec_bounded _ _ hi15_bound hi52_bound as ⟨i96, hi96, hi96_mul_bound⟩
  have hi96_bound : i96.val < 2 ^ 62 :=
    lt_of_le_of_lt hi96_mul_bound (by decide)
  simp only [hi15] at hi96
  clear hi96_mul_bound
  -- Coefficient 16.
  step with m_spec_bounded _ _ hi52_bound hi52_bound as ⟨i97, hi97, hi97_mul_bound⟩
  have hi97_bound : i97.val < 2 ^ 62 :=
    lt_of_le_of_lt hi97_mul_bound (by decide)
  clear hi97_mul_bound
  clear hi1_bound hi3_bound hi5_bound hi7_bound hi9_bound hi11_bound hi13_bound hi15_bound hi1 hi3
  clear hi5 hi7 hi9 hi11 hi13 hi15 i1 i3 i5 i7 i9 i11 i13 i15
  constructor
  · simp only [wideAsNat, asNat, Array.uScalarToNatRadix,
      UScalar.ofNatCore_val_eq, pow_mul]
    generalize (2 ^ 29 : Nat) = B
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
      List.getElem!_cons_succ]
    rw [hi16, hi18, hi21, hi25, hi30, hi36, hi43, hi51, hi61, hi69, hi76, hi82, hi87, hi91, hi94,
      hi96, hi97]
    rw [← hi, ← hi2, ← hi4, ← hi6, ← hi8, ← hi10, ← hi12, ← hi14, ← hi52]
    ring
  · intro j hj
    interval_cases j <;>
      simp only [Array.getElem!_Nat_eq, Array.make, List.getElem!_cons_zero,
        List.getElem!_cons_succ] <;> assumption

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

import translated.Funs
import proofs.P
import proofs.backend.serial.u32.field.Limbs
open Aeneas Aeneas.Std
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# ############################-/
/-*Spec theorem for `MINUS_ONE`*-/
/-# ############################-/


@[step]
theorem MINUS_ONE_spec :
    MINUS_ONE ⦃ (result : FieldElement2625) => result.val = p - 1 ⦄ := by
  unfold MINUS_ONE from_limbs
  simp only [WP.spec_ok]
  /- `MINUS_ONE` is the literal limb vector for `2^255 - 20`: limb 0 is `2^26 - 20` and every
  other limb is saturated.  Expand the weighted sum and evaluate the limbs. -/
  rw [FieldElement2625.val_eq_limbsVal, limbsVal_eq_flat]
  simp only [Array.make, Array.getElem!_Nat_eq, List.getElem!_cons_zero, List.getElem!_cons_succ,
    UScalar.ofNatCore_val_eq, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  /- `p` stays abstract: `p + 19 = 2^255` is the only fact needed to place the sum at `p - 1`. -/
  have h := p_add_19
  agrind


theorem MINUS_ONE_spec_v0 :
    MINUS_ONE ⦃ (result : FieldElement2625) => FE2625_as_Nat result = p - 1 ⦄ := by
  unfold MINUS_ONE p
  rfl

theorem MINUS_ONE_spec_v1 :
    MINUS_ONE ⦃ (result : FieldElement2625) => FieldElement2625_as_Nat result = p - 1 ⦄ := by
  unfold MINUS_ONE from_limbs
  simp only [WP.spec_ok]
  /- `FieldElement2625_as_Nat` reads the limbs through `map`, not by index, so on a literal
  array the split and both `Nat.ofDigits` folds just compute — no `getElem!` to unwrap. -/
  simp only [FieldElement2625_as_Nat, Array_UScalar_to_Nat_radix, Array.splitEvenOdd,
    Array.make, List.splitEvenOdd, List.map_cons, List.map_nil, Nat.ofDigits, Nat.cast_id,
    mul_zero, add_zero, UScalar.ofNatCore_val_eq, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  /- `p` stays abstract: `p + 19 = 2^255` is the only fact needed to place the sum at `p - 1`. -/
  have h := p_add_19
  agrind


/-- Same statement again, keeping the limbs and weights in power-of-two form rather than
letting them collapse to literals: every limb of `MINUS_ONE` is `2^25 - 1` or `2^26 - 1`,
except limb 0 which is `2^26 - 20`. -/
theorem MINUS_ONE_spec_v2 :
    MINUS_ONE ⦃ (result : FieldElement2625) => FieldElement2625_as_Nat result = p - 1 ⦄ := by
  unfold MINUS_ONE from_limbs
  simp only [WP.spec_ok]
  /- No `Nat.reducePow`/`reduceMul`/`reduceAdd` here, so the weights stay as `2^51` and `2^26`. -/
  simp only [FieldElement2625_as_Nat, Array_UScalar_to_Nat_radix, Array.splitEvenOdd,
    Array.make, List.splitEvenOdd, List.map_cons, List.map_nil, Nat.ofDigits, Nat.cast_id,
    mul_zero, add_zero, UScalar.ofNatCore_val_eq]
  /- Three rewrites cover all ten limbs: `2^26 - 1` occurs four times, `2^25 - 1` five times. -/
  rw [show (67108844 : ℕ) = 2 ^ 26 - 20 by norm_num,
      show (67108863 : ℕ) = 2 ^ 26 - 1 by norm_num,
      show (33554431 : ℕ) = 2 ^ 25 - 1 by norm_num]
  rw [← Nat.add_right_cancel (m := 20) (k := p - 1)]
  have h := p_add_19
  agrind


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

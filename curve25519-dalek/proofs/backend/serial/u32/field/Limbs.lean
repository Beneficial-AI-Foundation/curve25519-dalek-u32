import translated.Types
import proofs.ForMathlib
import proofs.ForAeneas
import proofs.P

open Aeneas Aeneas.Std

/-!
# The radix-2^25.5 limb representation of the u32 backend

A field element is represented as ten limbs: limb `i` carries weight `2^limbWeight i`, and even/odd
limbs hold 26/25 bits respectively.

This file defines the representation and proves the the facts all of `reduce`'s value reasoning
rests on: a carry between adjacent limbs preserves the represented value exactly (`limbsVal_carry`),
and the `×19` fold-in changes it by exactly `c·p` (`limbsVal_foldin`).
-/

namespace curve25519_dalek.backend.serial.u32.field

open Finset

/-- Bit width of limb `i`: even-indexed limbs hold 26 bits, odd-indexed 25. -/
def limbBits (i : Nat) : Nat := if i % 2 = 0 then 26 else 25

/- Bit width of limb: even-indexed limbs hold 26 bits, odd-indexed 25. -/
@[simp, scalar_tac_simps, grind =, agrind =]
theorem limbBits_eq (i : Nat) : limbBits i = if i % 2 = 0 then 26 else 25 := rfl

/-- Weight exponent of limb `i`: the total bit width of the limbs below it. -/
def limbWeight (i : Nat) : Nat := ∑ j ∈ range i, limbBits j

/-- Consecutive weights differ by exactly the bit width of the limb between them. -/
theorem limbWeight_succ (i : Nat) : limbWeight (i + 1) = limbWeight i + limbBits i :=
  sum_range_succ _ _

/-- Closed form of the weights: `(51·i + 1) / 2` is `⌈51·i/2⌉ = ⌈25.5·i⌉`. -/
theorem limbWeight_eq (i : Nat) : limbWeight i = (51 * i + 1) / 2 := by
  induction i with
  | zero => rfl
  | succ n ih => rw [limbWeight_succ, ih, limbBits_eq]; grind

/-- Value of a 10-limb scalar array in the alternating 26/25-bit radix. -/
def limbsVal {ty : UScalarTy} (z : Array (UScalar ty) 10#usize) : Nat :=
  ∑ i ∈ range 10, z[i]!.val * 2 ^ limbWeight i

/-- Expanded form of `limbsVal`. -/
theorem limbsVal_eq_flat {ty : UScalarTy} (z : Array (UScalar ty) 10#usize) :
    limbsVal z =
      z[0]!.val
      + z[1]!.val * 2 ^ 26
      + z[2]!.val * 2 ^ 51
      + z[3]!.val * 2 ^ 77
      + z[4]!.val * 2 ^ 102
      + z[5]!.val * 2 ^ 128
      + z[6]!.val * 2 ^ 153
      + z[7]!.val * 2 ^ 179
      + z[8]!.val * 2 ^ 204
      + z[9]!.val * 2 ^ 230 := by
  simp [limbsVal, sum_range_succ, limbWeight, limbBits]

/-- Two limb arrays with pointwise-equal limb values have equal `limbsVal`. -/
theorem limbsVal_congr {ty ty' : UScalarTy} {x : Array (UScalar ty) 10#usize}
    {y : Array (UScalar ty') 10#usize} (h : ∀ j, j < 10 → x[j]!.val = y[j]!.val) :
    limbsVal x = limbsVal y := by
  unfold limbsVal
  exact sum_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

/-- Value of a 10-limb scalar array in the alternating 26/25-bit radix. -/
def FieldElement2625.val (x : FieldElement2625) : ℕ := limbsVal x

@[simp]
theorem FieldElement2625.val_eq_limbsVal (x : FieldElement2625) :
    FieldElement2625.val x = limbsVal x := rfl

/-- A carry at position `k` preserves the represented value. -/
theorem limbsVal_carry (z z' : Array U64 10#usize) (k : Nat) (hk : k < 9)
    (hmask : z'[k]!.val = z[k]!.val % 2 ^ limbBits k)
    (hcarry : z'[k + 1]!.val = z[k + 1]!.val + z[k]!.val / 2 ^ limbBits k)
    (hrest : ∀ j, j < 10 → j ≠ k → j ≠ k + 1 → z'[j]!.val = z[j]!.val) :
    limbsVal z' = limbsVal z := by
  unfold limbsVal
  have h := sum_eq_sum_add_of_two_points (s := range 10)
    (f := fun j => z'[j]!.val * 2 ^ limbWeight j)
    (g := fun j => z[j]!.val * 2 ^ limbWeight j)
    (k := k) (l := k + 1) (d := 0)
    (mem_range.mpr (by agrind)) (mem_range.mpr (by agrind))
    (by agrind)
    (fun j hj hjk hjl => by rw [hrest j (mem_range.mp hj) hjk hjl])
    (by rw [hmask, hcarry, limbWeight_succ, add_zero]; exact Nat.carry_step ..)
  simpa using h

/-- The two-limb contribution identity behind the fold-in: the overflow `c = z9 / 2^25` leaves
weight 230 + 25 = 255 and re-enters at weight 0 as `19·c`. The difference is `c·(2^255 - 19). -/
private theorem foldin_pair (z0 z9 : ℕ) :
    z0 * 2 ^ 0 + z9 * 2 ^ 230
      = (z0 + 19 * (z9 / 2 ^ 25)) * 2 ^ 0 + z9 % 2 ^ 25 * 2 ^ 230 + z9 / 2 ^ 25 * p := by
  calc
    _ = z0 + (z9 % 2 ^ 25 + 2 ^ 25 * (z9 / 2 ^ 25)) * 2 ^ 230 := by rw [Nat.mod_add_div]; ring
    _ = z0 + z9 % 2 ^ 25 * 2 ^ 230 + z9 / 2 ^ 25 * 2 ^ 255 := by ring
    _ = z0 + z9 % 2 ^ 25 * 2 ^ 230 + z9 / 2 ^ 25 * (p + 19) := by rw [p_add_19]
    _ = _ := by ring

/-- The `×19` fold-in changes the represented value by exactly `c·p`, where `c = z[9] / 2^25` is the
overflow of limb 9. -/
theorem limbsVal_foldin (z z' : Array U64 10#usize)
    (h0 : z'[0]!.val = z[0]!.val + 19 * (z[9]!.val / 2 ^ 25)) (h9 : z'[9]!.val = z[9]!.val % 2 ^ 25)
    (hrest : ∀ j, j < 10 → j ≠ 0 → j ≠ 9 → z'[j]!.val = z[j]!.val) :
    limbsVal z = limbsVal z' + (z[9]!.val / 2 ^ 25) * p := by
  unfold limbsVal
  refine sum_eq_sum_add_of_two_points (k := 0) (l := 9) _
    (mem_range.mpr (by norm_num)) (mem_range.mpr (by norm_num))
    (by norm_num)
    (fun j hj hj0 hj9 => by rw [hrest j (mem_range.mp hj) hj0 hj9]) ?_
  rw [h0, h9, show limbWeight 0 = 0 by decide, show limbWeight 9 = 230 by decide]
  exact foldin_pair z[0]!.val z[9]!.val

end curve25519_dalek.backend.serial.u32.field

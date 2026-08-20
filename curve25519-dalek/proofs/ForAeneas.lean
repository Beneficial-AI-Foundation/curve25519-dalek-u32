import Aeneas
import Mathlib.Data.Nat.Digits.Defs

/-!
# Aeneas.Std extensions, candidates for upstreaming

-/

open Aeneas.Std

/-- Bitwise AND with a low-bits mask `m = 2^n - 1` reduces the value modulo `2^n`. -/
theorem Aeneas.Std.UScalar.val_and_mask {ty : UScalarTy} (x m : UScalar ty) (n : Nat)
    (hm : m.val = 2 ^ n - 1) : (x &&& m).val = x.val % 2 ^ n := by
  rw [UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]


/-*This theorem needs a better description*-/
/-Provided that m ≤ n, bitwise AND of n consecutive 1-s and the sum of an m-bit vector
and any bit-vector left shifted by m is the same as the m-bit vector plus
the bitwise AND of n consecutive 1-s and the bit-vector shifted left by m.-/
theorem Aeneas.Std.UScalar.add_shiftLeft_and_mask_of_lt {ty : UScalarTy}
    (x y mask : UScalar ty) (m n : Nat) (hx : x.val < 2 ^ m)
    (hexp : m ≤ n) (hmask : mask.val = 2 ^ n - 1) :
    (x.val + y.val <<< m) &&& mask.val = x.val + (y.val <<< m &&& mask.val) := by
  rw [hmask, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
  Nat.shiftLeft_eq]
  have hsplit : 2 ^ n = 2 ^ (n - m) * 2 ^ m := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hexp]
  rw [hsplit]
  have hlt : x.val + y.val * 2 ^ m % 2 ^ n < 2 ^ n := by
      rw [hsplit, Nat.mul_mod_mul_right]
      calc x.val + y.val % 2 ^ (n - m) * 2 ^ m
          < 2 ^ m + y.val % 2 ^ (n - m) * 2 ^ m := Nat.add_lt_add_right hx _
        _ = (y.val % 2 ^ (n - m) + 1) * 2 ^ m := by ring
        _ ≤ 2 ^ (n - m) * 2 ^ m :=
          Nat.mul_le_mul_right _ (Nat.mod_lt y.val (by exact Nat.two_pow_pos _))
  rewrite [← hsplit]
  have ha : x.val < 2 ^ n := by
    exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hexp)
  rw [Nat.add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hlt]


/-- Function that turns an `Array (UScalar ty) Usize` into a `Nat` using
`2^ty.numBits` as weights. -/
def Aeneas.Std.Array_UScalar_to_Nat {ty : UScalarTy} {n : Usize}
  (a : Array (UScalar ty) n) : Nat :=
  Nat.ofDigits (2 ^ ty.numBits) (a.val.map UScalar.val)

/-Examples for demonstration:-/
#eval Aeneas.Std.Array_UScalar_to_Nat (Array.make 32#usize [65#u8,1#u8,0#u8,0#u8,
0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,
0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8])

#eval (Aeneas.Std.Array_UScalar_to_Nat (Array.make 2#usize [65#u64,1#u64]) - 2^64)

/-*Experiment to write FieldElement2625_to_Nat in a compact form*-/
/-Split an Array into two arrays, one containing the even, the other the odd indices.-/

universe u

/-- Split a list into the elements at even indices and those at odd indices, each
keeping their original relative order. -/
def List.splitEvenOdd {α : Type u} : List α → List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: t =>
    let (e, o) := List.splitEvenOdd t
    (a :: e, b :: o)

@[simp]
theorem List.length_splitEvenOdd_fst {α : Type u} (l : List α) :
    (List.splitEvenOdd l).1.length = (l.length + 1) / 2 := by
  induction l using List.splitEvenOdd.induct
  · simp only [List.splitEvenOdd, List.length_nil]
  · simp only [List.splitEvenOdd, List.length_cons, List.length_nil]
  · rename_i a b t ih
    simp only [List.splitEvenOdd, List.length_cons, ih]
    agrind

@[simp]
theorem List.length_splitEvenOdd_snd {α : Type u} (l : List α) :
    (List.splitEvenOdd l).2.length = l.length / 2 := by
  induction l using List.splitEvenOdd.induct
  · simp only [List.splitEvenOdd, List.length_nil]
  · simp only [List.splitEvenOdd, List.length_cons, List.length_nil]
  · rename_i a b t ih
    simp only [List.splitEvenOdd, List.length_cons, ih]
    agrind

/-- Split an array into the sub-array of even-indexed elements and the sub-array of
odd-indexed elements. The output lengths `ne = ⌈n/2⌉` and `no = ⌊n/2⌋` are supplied by
the caller, since they cannot be inferred from the return type; for a concrete `n` the
two side conditions are discharged automatically. -/
def Aeneas.Std.Array.splitEvenOdd {α : Type u} {n : Usize} (a : Array α n) (ne no : Usize)
    (hne : ne.val = (n.val + 1) / 2 := by scalar_tac)
    (hno : no.val = n.val / 2 := by scalar_tac) :
    Array α ne × Array α no :=
  (⟨(List.splitEvenOdd a.val).1, by
      rw [List.length_splitEvenOdd_fst, a.property]; exact hne.symm⟩,
   ⟨(List.splitEvenOdd a.val).2, by
      rw [List.length_splitEvenOdd_snd, a.property]; exact hno.symm⟩)

/-Examples for demonstration:-/
#eval (Array.splitEvenOdd (Array.make 5#usize [0#u8,1#u8,2#u8,3#u8,4#u8]) 3#usize 2#usize).1.val
#eval (Array.splitEvenOdd (Array.make 5#usize [0#u8,1#u8,2#u8,3#u8,4#u8]) 3#usize 2#usize).2.val

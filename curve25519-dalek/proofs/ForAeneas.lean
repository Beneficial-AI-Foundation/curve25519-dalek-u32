import Aeneas

/-!
# Aeneas.Std extensions, candidates for upstreaming

-/

open Aeneas.Std

def Aeneas.Std.Array.map {α β : Type} {n : Usize} (f : α → β) (a : Array α n) :
    Array β n :=
  ⟨a.val.map f, by simp⟩

@[simp, simp_lists]
theorem Aeneas.Std.Array.val_map {α β : Type} {n : Usize} (f : α → β) (a : Array α n) :
    (a.map f).val = a.val.map f := rfl

/-- Bitwise AND with a low-bits mask `m = 2^n - 1` reduces the value modulo `2^n`. -/
theorem Aeneas.Std.UScalar.val_and_mask {ty : UScalarTy} (x m : UScalar ty) (n : Nat)
    (hm : m.val = 2 ^ n - 1) : (x &&& m).val = x.val % 2 ^ n := by
  rw [UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]

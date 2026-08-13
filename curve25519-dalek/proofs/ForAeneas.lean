import Aeneas

/-!
# Aeneas.Std extensions, candidates for upstreaming

-/

open Aeneas.Std

/-- Bitwise AND with a low-bits mask `m = 2^n - 1` reduces the value modulo `2^n`. -/
theorem Aeneas.Std.UScalar.val_and_mask {ty : UScalarTy} (x m : UScalar ty) (n : Nat)
    (hm : m.val = 2 ^ n - 1) : (x &&& m).val = x.val % 2 ^ n := by
  rw [UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]

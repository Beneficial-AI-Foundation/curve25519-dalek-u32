/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary

/-!
# Spec theorem for `from_bytes.load4_at`

`from_bytes.load4_at` takes a `Slice Std.U8` as `b` and an index `i` of type `Usize` and creates
a `Result Std.U64` output. It grabs the four consecutive `U8` values `b[i]`, `b[i+1]`, `b[i+2]` and
`b[i+3]` and combines them into a `32-bit` long number, by shifting `b[i+1]` with `8`, `b[i+2]` with
`16` and `b[i+3]` with `24` digits first and then adding all four values together.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 411:8-416:9
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP Finset
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::from_bytes::load4_at`
Assuming that the largest index used `i+3` isn't out of range, the theorem states that the result's
Nat value equals to the Nat values of the four consecutive terms of `b` combined with weights `1`,
`2^8`, `2^16` and `2^24` respectively. This follows from the properties of what bitshift to the left
and bitwise OR on disjoint ranges mean for the corresponding Nat values.
A trivial upper bound, that follows from the first statement, is also proved for the result as it
will be useful later. -/
@[step]
theorem from_bytes.load4_at_spec (b : Slice U8) (i : Usize)
    (hi : i.val + 4 ≤ b.length) :
    from_bytes.load4_at b i ⦃ (r : U64) =>
      r.val = b[i.val]!.val + 2 ^ 8 * b[i.val + 1]!.val +
      2 ^ 16 * b[i.val + 2]! + 2 ^ 24 * b[i.val + 3]!.val ∧
      /- Redundant: it follows from the other conjunct. -/
      r.val < 2 ^ 32 ⦄ := by
  unfold from_bytes.load4_at
  step*
  refine (and_iff_left_of_imp (fun h => ?_)).mpr ?_
  --Showing that the first statement implies the second
  · rw [h]; scalar_tac
  --Proving the first statement
  · iterate 2
      rewrite [UScalar.val_or]
      conv in _ ||| _ => simp only [*]
      conv => rhs; simp only [*]
    rewrite [UScalar.val_or]
    simp (disch := scalar_tac) only [*, U8.cast_U64_val_eq, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    nth_rewrite 3 4 [Nat.or_two_pow_eq_add_of_lt (by scalar_tac)]
    nth_rewrite 2 3 [Nat.or_two_pow_eq_add_of_lt (by scalar_tac)]
    rewrite [Nat.or_two_pow_eq_add_of_lt (by scalar_tac)]
    grind


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

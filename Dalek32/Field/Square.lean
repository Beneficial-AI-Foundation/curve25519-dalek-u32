/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.Field.SquareInner
import Dalek32.Field.Reduce

/-!
# Spec theorem for `square`

`square self` computes `self ^ 2` as a `FieldElement2625`. It first runs the squaring kernel
`square_inner`, which returns ten unreduced `u64` coefficients congruent to `self ^ 2` modulo `p`,
and then `reduce` carries these coefficients back into the alternating `2^26/2^25` radix.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 595:4-597:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625


/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::square`
If every limb of `self` is below `2 ^ 27 + 2 ^ 25` (enough for the sum of two reduced field
elements), the result is reduced (every limb below `2 ^ 26`) and represents `self ^ 2` modulo `p`.
After unfolding `square`, a first `step` applies `square_inner_spec`, giving coefficients `a`
with `a.uScalarToNatField2625 % p = self.toNat ^ 2 % p` and `a[i] < 6675 * 2 ^ 50`. Since
`6675 * 2 ^ 50 ≤ 2 ^ 64 - 2 ^ 39`, `step with reduce_spec` then applies to `a`. Its uniform limb
bound is the bound here, and its congruence chained with that of `square_inner_spec` by
`Eq.trans` gives the value. -/
@[step]
theorem square_spec (self : FieldElement2625)
    (h_self : ∀ i < 10, self[i]!.val < 2 ^ 27 + 2 ^ 25) :
    square self ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val < 2 ^ 26) ∧
      result.toNat % p = self.toNat ^ 2 % p ⦄ := by
  unfold square
  step as ⟨a, h_mod, h_bound⟩
  step with reduce_spec as ⟨result, h_res, h_res_mod, _⟩
  exact ⟨h_res, h_res_mod.trans h_mod⟩


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

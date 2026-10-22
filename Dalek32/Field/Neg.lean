/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.Field.Negate

/-!
# Spec theorem for `neg`

`neg self` copies `self` and negates it in place; in the extracted code it simply calls
`FieldElement2625::negate`, so it inherits the specification of `negate`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 232:4-236:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.SharedAFieldElement2625.Insts.CoreOpsArithNegFieldElement2625

-- Note: as for negate_spec, a looser bound (self[i] < 8 * 2^26, roughly) would also hold.
/-- **Spec theorem for**
`<&curve25519_dalek::backend::serial::u32::field::FieldElement2625 as core::ops::Neg>::neg`
If every limb of `self` is below `3 * 2 ^ 26` (enough for a sum of up to two reduced elements),
`neg` succeeds and returns a reduced element (every limb below `2 ^ 26`) `r` with
`r + self ≡ 0 [MOD p]`.
The proof unfolds `neg`, whose body is exactly `FieldElement2625.negate self`, and `step*` applies
`FieldElement2625.negate_spec`, whose precondition is the hypothesis here and whose postcondition
is the statement. -/
@[step]
theorem neg_spec (self : FieldElement2625)
    (h_self : ∀ i < 10, self[i]!.val < 3 * 2 ^ 26) :
    neg self ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val < 2 ^ 26) ∧
      (result.toNat + self.toNat) % p = 0 ⦄ := by
  unfold neg
  step*

end Curve25519Dalek.SharedAFieldElement2625.Insts.CoreOpsArithNegFieldElement2625

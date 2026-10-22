/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.Field.SubAssign

/-!
# Spec theorem for `sub`

`sub self _rhs` copies `self` and subtracts `_rhs` from it in place; in the extracted code it
simply calls `<FieldElement2625 as SubAssign<&FieldElement2625>>::sub_assign`, so it inherits the
specification of `sub_assign`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 110:4-114:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.SharedAFieldElement2625.Insts
namespace CoreOpsArithSubSharedBFieldElement2625FieldElement2625

-- Note: as for sub_assign_spec, a looser bound (_rhs[i] < 8 * 2^26, roughly) would also hold.
/-- **Spec theorem for**
`<&curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
core::ops::Sub<&FieldElement2625>>::sub`
If every limb of both operands is below `3 * 2 ^ 26` (enough for operands that are sums of up to
two reduced elements), `sub` succeeds and returns a reduced element (every limb below `2 ^ 26`) `r`
with `r + _rhs ≡ self [MOD p]`.
The proof unfolds `sub`, whose body is exactly `sub_assign self _rhs`, and `step*` applies
`FieldElement2625.Insts.CoreOpsArithSubAssignSharedBFieldElement2625.sub_assign_spec`, whose
preconditions are the hypotheses here and whose postcondition is the statement. -/
@[step]
theorem sub_spec (self _rhs : FieldElement2625)
    (h_self : ∀ i < 10, self[i]!.val < 3 * 2 ^ 26)
    (h_rhs : ∀ i < 10, _rhs[i]!.val < 3 * 2 ^ 26) :
    sub self _rhs ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val < 2 ^ 26) ∧
      (result.toNat + _rhs.toNat) % p = self.toNat % p ⦄ := by
  unfold sub
  step*

end CoreOpsArithSubSharedBFieldElement2625FieldElement2625
end Curve25519Dalek.SharedAFieldElement2625.Insts

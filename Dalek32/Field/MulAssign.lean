/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.Field.Mul

/-!
# Spec theorem for `mul_assign`

`mul_assign self _rhs` overwrites `self` with `&self * _rhs`; in the extracted code it simply calls
`<&FieldElement2625 as Mul<&FieldElement2625>>::mul` and returns its result, so it inherits the
specification of `mul`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 118:4-121:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts
namespace CoreOpsArithMulAssignSharedBFieldElement2625

/-- **Spec theorem for**
`<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
core::ops::MulAssign<&FieldElement2625>>::mul_assign`
If every limb of both operands is below `3 * 2 ^ 26`, `mul_assign` succeeds and returns a reduced
element (every limb below `2 ^ 26`) representing `self * _rhs` modulo `p`.
The proof unfolds `mul_assign`, whose body is `mul self _rhs` followed by `ok`, and `step*` applies
`SharedAFieldElement2625.Insts.CoreOpsArithMulSharedBFieldElement2625FieldElement2625.mul_spec`,
whose preconditions are the hypotheses here and whose postcondition is the statement. -/
@[step]
theorem mul_assign_spec (self _rhs : FieldElement2625)
    (h_self : ∀ i < 10, self[i]!.val < 3 * 2 ^ 26)
    (h_rhs : ∀ i < 10, _rhs[i]!.val < 3 * 2 ^ 26) :
    mul_assign self _rhs ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val < 2 ^ 26) ∧
      result.toNat % p = self.toNat * _rhs.toNat % p ⦄ := by
  unfold mul_assign
  step*

end CoreOpsArithMulAssignSharedBFieldElement2625
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts

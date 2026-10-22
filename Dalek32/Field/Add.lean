/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.Field.AddAssign

/-!
# Spec theorem for `add`

`&self + &rhs` copies `self` and adds `rhs` to the copy with `+=`, i.e. it adds the ten `u32` limbs
pairwise without carrying or reduction. If every limb sum fits in a `u32`, no addition overflows
and the represented value of the result is the exact sum of those of the operands.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 79:4-83:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.SharedAFieldElement2625
namespace Insts.CoreOpsArithAddSharedBFieldElement2625FieldElement2625

open backend.serial.u32.field

/-- **Spec theorem for**
`<&curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
core::ops::Add<&FieldElement2625>>::add`

If every limb sum `self[i] + _rhs[i]` fits in a `u32`, the result has as limbs the exact limb sums
and represents `self.toNat + _rhs.toNat` (no reduction modulo `p` takes place). The Rust copy
`let mut output = *self` is erased by the extraction, so `add self _rhs` unfolds to
`add_assign self _rhs`, and `step*` closes the goal with `add_assign_spec`, whose precondition is
`h_sum`. -/
@[step]
theorem add_spec (self _rhs : FieldElement2625)
    (h_sum : ∀ i < 10, self[i]!.val + _rhs[i]!.val ≤ U32.max) :
    add self _rhs ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val = self[i]!.val + _rhs[i]!.val) ∧
      result.toNat = self.toNat + _rhs.toNat ⦄ := by
  unfold add
  step*

end Insts.CoreOpsArithAddSharedBFieldElement2625FieldElement2625
end Curve25519Dalek.SharedAFieldElement2625

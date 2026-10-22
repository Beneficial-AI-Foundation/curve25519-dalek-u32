/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.Subtle.ConditionalSelectU32

/-!
# Spec theorem for `conditional_select`

`conditional_select a b choice` builds a new `FieldElement2625` limb by limb, selecting each limb
with the constant-time `u32::conditional_select`. For a valid choice (`0` or `1`) the result is `a`
for `0` and `b` for `1`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 240:4-257:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625
namespace Insts.SubtleConditionallySelectable

/-- **Spec theorem for**
`<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
subtle::ConditionallySelectable>::conditional_select`

For a valid choice `choice ∈ {0, 1}` the result is `b` if `choice = 1` and `a` otherwise.
The body reads limb `k` of `a` and `b` for `k = 0, …, 9` and selects between them with
`u32::conditional_select`. One `step*` runs through it, using the spec of `Array.index_usize` and
`U32.Insts.SubtleConditionallySelectable.conditional_select_spec` (with `h_choice`), and
`subst_vars` writes the result as `Array.make` of the ten selected limbs. After `split_ifs` on
`choice = 1#u8`, both cases are closed by list extensionality (`Subtype.ext`, `List.ext_getElem`)
and a case split on the index: each of the ten limbs by `rfl`, larger indices by `omega`. -/
@[step]
theorem conditional_select_spec (a b : FieldElement2625) (choice : subtle.Choice)
    (h_choice : choice = 0#u8 ∨ choice = 1#u8) :
    conditional_select a b choice ⦃ (result : FieldElement2625) =>
      result = if choice = 1#u8 then b else a ⦄ := by
  unfold conditional_select
  step*
  subst_vars
  split_ifs <;> apply Subtype.ext <;> apply List.ext_getElem (by simp) <;> intro n h1 _ <;>
    simp only [Array.make, List.length_cons, List.length_nil] at h1 <;>
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> first | rfl | omega

end Insts.SubtleConditionallySelectable
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

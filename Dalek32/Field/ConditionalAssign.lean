/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import translated.Funs
import Dalek32.Definitions
import Dalek32.Auxiliary
import Dalek32.External.Axioms

/-!
# Spec theorem for `conditional_assign`

`conditional_assign self other choice` updates `self` in place, limb by limb, with the constant-time
`u32::conditional_assign`. For a valid choice (`0` or `1`) the result is `other` for `1` and the
unchanged `self` for `0`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 259:4-270:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625
namespace Insts.SubtleConditionallySelectable

/-- For a valid choice, the `u32` conditional assignment returns the selected value. This is the
spec axiom `conditional_assign_spec` turned into an equation by `spec_imp_exists`, so that the
whole body of `conditional_assign_spec` below can be rewritten by `simp` instead of stepped. -/
private theorem u32_conditional_assign_eq (x y : U32) (choice : subtle.Choice)
    (h_choice : choice = 0#u8 ∨ choice = 1#u8) :
    U32.Insts.SubtleConditionallySelectable.conditional_assign x y choice =
      ok (if choice = 1#u8 then y else x) := by
  obtain ⟨r, h_eq, h_r⟩ :=
    spec_imp_exists (U32.Insts.SubtleConditionallySelectable.conditional_assign_spec x y choice
      h_choice)
  rw [h_eq, h_r]

/-- **Spec theorem for**
`<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
subtle::ConditionallySelectable>::conditional_assign`

For a valid choice `choice ∈ {0, 1}` the result is `other` if `choice = 1` and `self` otherwise.
The proof rewrites the whole body with equations instead of stepping through it: first every
`u32` conditional assignment with `u32_conditional_assign_eq`, then, after a case split on
`choice = 1#u8`, one `simp only` resolves the in-bounds limb accesses with `index_mut_usize_eq`
and `index_usize_eq`, the `if` with `hc`, and the binds with `bind_tc_ok`, leaving the result as
the chain of `set`s on `self` (`Array.set_val_getElem_self` drops writes of a limb's own value).
The remaining goal is closed by list extensionality (`Subtype.ext`, `List.ext_getElem`) and a case
split on the index: each of the ten limbs by `simp`, larger indices by `omega`. -/
@[step]
theorem conditional_assign_spec (self other : FieldElement2625) (choice : subtle.Choice)
    (h_choice : choice = 0#u8 ∨ choice = 1#u8) :
    conditional_assign self other choice ⦃ (result : FieldElement2625) =>
      result = if choice = 1#u8 then other else self ⦄ := by
  unfold conditional_assign
  simp only [u32_conditional_assign_eq _ _ _ h_choice]
  by_cases hc : choice = 1#u8 <;>
    simp only [UScalar.ofNatCore_val_eq, Nat.ofNat_pos, index_mut_usize_eq,
      Array.getElem!_Nat_eq, List.Vector.length_val, getElem!_pos, index_usize_eq, hc,
      ↓reduceIte, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one, bind_tc_ok, uncurry_apply_pair,
      Array.set_val_getElem_self, spec_ok]
  apply Subtype.ext
  apply List.ext_getElem (by simp)
  intro n h1 _
  simp only [Std.Array.set_val_eq, List.length_set, Array.length_eq,
    UScalar.ofNatCore_val_eq] at h1 ⊢
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> first | omega | simp

end Insts.SubtleConditionallySelectable
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

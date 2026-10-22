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
# Spec theorem for `conditional_swap`

`conditional_swap a b choice` swaps two `FieldElement2625`s in place, limb by limb, with the
constant-time `u32::conditional_swap`. For a valid choice (`0` or `1`) the pair is swapped for `1`
and left unchanged for `0`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 272:4-283:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625
namespace Insts.SubtleConditionallySelectable

/-- For a valid choice, the `u32` conditional swap returns the swapped or the unchanged pair. This
is the spec axiom `conditional_swap_spec` turned into an equation by `spec_imp_exists`, so that the
whole body of `conditional_swap_spec` below can be rewritten by `simp` instead of stepped. -/
private theorem u32_conditional_swap_eq (x y : U32) (choice : subtle.Choice)
    (h_choice : choice = 0#u8 ∨ choice = 1#u8) :
    U32.Insts.SubtleConditionallySelectable.conditional_swap x y choice =
      ok (if choice = 1#u8 then (y, x) else (x, y)) := by
  obtain ⟨⟨r1, r2⟩, h_eq, h_r⟩ :=
    spec_imp_exists (U32.Insts.SubtleConditionallySelectable.conditional_swap_spec x y choice
      h_choice)
  rw [h_eq, ← h_r]

/-- **Spec theorem for**
`<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as
subtle::ConditionallySelectable>::conditional_swap`

For a valid choice `choice ∈ {0, 1}` the returned pair is `(b, a)` if `choice = 1` and `(a, b)`
otherwise. The proof rewrites the whole body with equations instead of stepping through it: first
every `u32` conditional swap with `u32_conditional_swap_eq`, then, after a case split on
`choice = 1#u8`, one `simp only` resolves the in-bounds limb accesses with `index_mut_usize_eq`,
the `if` with `hc` and the binds with `bind_tc_ok`. It also reads limbs past writes at other
indices (`List.getElem_set_ne`) and splits the pair equality with `Prod.mk.injEq`. Each of the
two remaining array equalities is closed by list extensionality (`Subtype.ext`, `List.ext_getElem`)
and a case split on the index: each of the ten limbs by `simp`, larger indices by `omega`. -/
@[step]
theorem conditional_swap_spec (a b : FieldElement2625) (choice : subtle.Choice)
    (h_choice : choice = 0#u8 ∨ choice = 1#u8) :
    conditional_swap a b choice ⦃ (r1 : FieldElement2625) (r2 : FieldElement2625) =>
      (r1, r2) = if choice = 1#u8 then (b, a) else (a, b) ⦄ := by
  unfold conditional_swap
  simp only [u32_conditional_swap_eq _ _ _ h_choice]
  by_cases hc : choice = 1#u8 <;>
    simp only [UScalar.ofNatCore_val_eq, Nat.ofNat_pos, index_mut_usize_eq,
      Array.getElem!_Nat_eq, List.Vector.length_val, getElem!_pos, hc, ↓reduceIte,
      Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one, bind_tc_ok, uncurry_apply_pair,
      Array.set_val_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true, List.getElem_set_ne,
      OfNat.one_ne_ofNat, zero_ne_one, OfNat.zero_ne_ofNat, Array.set_val_getElem_self,
      Prod.mk.injEq,
      spec_ok, uncurry'_pair, and_self]
  refine ⟨?_, ?_⟩ <;> apply Subtype.ext <;> apply List.ext_getElem (by simp) <;>
    intro n h1 _ <;> simp only [Std.Array.set_val_eq, List.length_set, Array.length_eq,
      UScalar.ofNatCore_val_eq] at h1 ⊢ <;>
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> first | omega | simp

end Insts.SubtleConditionallySelectable
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

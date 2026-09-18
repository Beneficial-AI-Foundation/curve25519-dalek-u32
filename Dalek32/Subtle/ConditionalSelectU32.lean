/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Lint.Basic
import translated.FunsExternal

/-!
# `u32::conditional_select`

Valid-choice specification.
Source: "subtle-2.6.1/src/lib.rs", lines 513-518.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace U32.Insts.SubtleConditionallySelectable

/-- **Spec theorem for `<u32 as subtle::ConditionallySelectable>::conditional_select`**

Selects `b` for 1 and `a` for 0. -/
@[step]
theorem conditional_select_spec (a b : U32) (choice : subtle.Choice)
    (h_choice : choice = 0#u8 ∨ choice = 1#u8) :
    conditional_select a b choice ⦃ (result : U32) =>
      result = if choice = 1#u8 then b else a ⦄ := by
  rcases h_choice with h | h
  · simp [conditional_select, h]
  · simp only [conditional_select, h, UScalar.ofNatCore_val_eq, BitVec.reduceNeg,
      ↓reduceIte, spec_ok]
    apply U32.bv_eq_imp_eq
    change a.bv ^^^ (BitVec.allOnes 32 &&& (a.bv ^^^ b.bv)) = b.bv
    simp only [BitVec.allOnes_and, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end U32.Insts.SubtleConditionallySelectable

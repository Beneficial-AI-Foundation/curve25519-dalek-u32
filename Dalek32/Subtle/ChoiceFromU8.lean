/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Lint.Basic
import translated.FunsExternal

/-!
# `Choice::from`

Preserves input bytes 0 and 1.
Source: "subtle-2.6.1/src/lib.rs", lines 238-244.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace subtle.Choice.Insts.CoreConvertFromU8

/-- **Spec theorem for `<subtle::Choice as core::convert::From<u8>>::from`**

Preserves 0 or 1. -/
@[step]
theorem from_spec (input : U8) (h_input : input = 0#u8 ∨ input = 1#u8) :
    «from» input ⦃ (choice : subtle.Choice) =>
      choice.val = input ⦄ := by
  simp [«from», h_input]

end subtle.Choice.Insts.CoreConvertFromU8

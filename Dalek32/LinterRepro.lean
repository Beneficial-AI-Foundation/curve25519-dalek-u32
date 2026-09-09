/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import translated.Funs

/-!
# Temporary specification-indentation reproducer: do not merge

The four-space postcondition below is intentional. The copyright header is valid.
The control script adds only the linter import, then fixes only the indentation.
No linter is disabled, and the theorem and proof are unchanged across the three cases.
-/

open Aeneas Aeneas.Std

namespace Dalek32.LinterRepro

/-- A trivial computation used only by this disposable reproducer. -/
def echo (x : U32) : Result U32 := Result.ok x

/-- The deliberately misindented specification is mathematically correct. -/
@[step]
theorem echo_spec (x : U32) :
    echo x ⦃ (result : U32) =>
    result = x ⦄ := by
  rfl

end Dalek32.LinterRepro

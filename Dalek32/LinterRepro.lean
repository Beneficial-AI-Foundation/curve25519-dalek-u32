/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import translated.Funs

/-!
# Temporary syntax-linter reproducer: do not merge

The missing `(c)` in the copyright header and the four-space postcondition below are
intentional. The proof is valid. The control script changes only the linter import,
then fixes those two style defects. No linter is disabled.
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

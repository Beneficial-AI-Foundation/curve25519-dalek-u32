/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
import Dalek32.Scalar.Math
import translated.Funs

/-!
# Spec theorem for `curve25519_dalek::backend::serial::u32::constants::LFACTOR`

This constant satisfies `L * LFACTOR ≡ -1 (mod 2^29)`.

Source: "curve25519-dalek/src/backend/serial/u32/constants.rs", lines 104:0-104:43
-/

open Aeneas Aeneas.Std
open Curve25519Dalek.backend.serial.u32.scalar

namespace Curve25519Dalek.backend.serial.u32.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u32::constants::LFACTOR`**
The scalar order times `LFACTOR` is `-1` modulo `2^29`, and `LFACTOR` fits in one
radix-`2^29` limb. -/
theorem LFACTOR_spec :
    (Scalar29.order * LFACTOR.val + 1) % (2 ^ 29) = 0 ∧
    LFACTOR.val < 2 ^ 29 := by
  unfold LFACTOR Scalar29.order
  decide

end Curve25519Dalek.backend.serial.u32.constants

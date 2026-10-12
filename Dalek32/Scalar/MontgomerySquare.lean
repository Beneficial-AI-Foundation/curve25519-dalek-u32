/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dana Mukusheva
-/
import Dalek32.Auxiliary
import Dalek32.Lint.Basic
import Dalek32.Scalar.MontgomeryReduce
import Dalek32.Scalar.SquareInternal

/-!
# `montgomery_square`

Montgomery squaring: square, then Montgomery-reduce.
Source: "curve25519-dalek/src/backend/serial/u32/scalar.rs", lines 394-396.

## Correspondence with the `u64` backend spec

`montgomery_square_spec` mirrors `Scalar52.montgomery_square_spec` in curve25519-dalek-lean-verify
("Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomerySquare.lean"):

| `u32` (this file)                               | `u64` (`Scalar52`)          |
|-------------------------------------------------|-----------------------------|
| `order`                                         | `L`                         |
| `montgomeryRadix` (`2^261`)                     | `R` (`2^260`)               |
| `asNat`                                         | `Scalar52_as_Nat`           |
| `IsNormalized a` (9 limbs, each `< 2^29`)       | `∀ i < 5, m[i]! < 2^62`     |
| `asNat a ^ 2`                                   | `m * m`                     |
| `asNat a ^ 2 < montgomeryRadix * order`         | `m * m < R * L`             |
| `a ^ 2 % order = (r * montgomeryRadix) % order` | `(m * m) % L = (w * R) % L` |
| `IsNormalized result`                           | `∀ i < 5, w[i]! < 2^52`     |

The postconditions say the same thing: `a ^ 2` is congruent to the result times the Montgomery
radix modulo the order, the result is normalized, and it is canonical (`< order`).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u32::scalar::Scalar29::montgomery_square`**

• No panic (always returns successfully) when every limb of `a` is `< 2^29` and
  `asNat a ^ 2 < montgomeryRadix * order`
• The result satisfies the Montgomery squaring property:
  `a ^ 2 ≡ result * R (mod order)`, where `R = montgomeryRadix = 2^261`
• The result is normalized (every limb `< 2^29`) and canonical (`asNat result < order`) -/
@[step]
theorem montgomery_square_spec (a : Scalar29) (h_a : IsNormalized a)
    (h_range : asNat a ^ 2 < montgomeryRadix * order) :
    montgomery_square a ⦃ (result : Scalar29) =>
      asNat a ^ 2 % order = (asNat result * montgomeryRadix) % order ∧
      IsNormalized result ∧
      asNat result < order ⦄ := by
  unfold montgomery_square
  step*
  exact h_a

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29

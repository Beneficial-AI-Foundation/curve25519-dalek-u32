/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Dalek32.Field.Pow2KLoop

/-!
# Fixed top-level specification for `FieldElement2625.pow2k`

Following the u64 `pow2k_spec` contract, specify positive iteration counts, bounded
input limbs, the modular power, and tighter output limbs. The u32 representation
uses alternating 26/25-bit limbs: inputs allow one excess bit, while outputs allow
an additional `2^18` only on odd limbs. These output bounds imply the input bounds,
so the contract supports repeated calls.

The statement is fixed for the recursive verification experiment in issue #99.
The proof composes verified squaring with a terminating repeated-squaring loop.
Source: `curve25519-dalek/src/backend/serial/u32/field.rs`, lines 320-327.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- **Spec theorem for**
`curve25519_dalek::backend::serial::u32::field::FieldElement2625::pow2k`

For `k > 0`, returns `self^(2^k)` modulo `p` with limb bounds that permit further
squaring. The result need not be the canonical representative below `p`. -/
@[step]
theorem pow2k_spec (self : FieldElement2625) (k : U32)
    (h_k : 0 < k.val)
    (h_bounds : ∀ i < 10, self[i]!.val < 2 ^ (27 - i % 2)) :
    pow2k self k ⦃ (result : FieldElement2625) =>
      toNat result % p = (toNat self) ^ (2 ^ k.val) % p ∧
      (∀ i < 10, result[i]!.val < 2 ^ (26 - i % 2) + i % 2 * 2 ^ 18) ⦄ := by
  unfold pow2k
  step
  apply spec_bind (square_spec self (pow2kBounds_squareInputBounds h_bounds))
  intro z hz
  apply spec_mono (pow2k_loop_spec { start := 1#u32, «end» := k } z hz.2)
  intro result hr
  refine ⟨hr.1.trans ?_, hr.2⟩
  change toNat z ^ (2 ^ (k.val - 1)) % p = toNat self ^ (2 ^ k.val) % p
  have hk : k.val - 1 + 1 = k.val := by omega
  simpa only [hk] using square_pow_mod (toNat self) (toNat z) (k.val - 1) hz.1

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

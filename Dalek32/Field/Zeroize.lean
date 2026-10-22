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
# Spec theorem for `zeroize`

`zeroize self` overwrites the ten `u32` limbs of a `FieldElement2625` with zeros by delegating to
the `zeroize` implementation of `[u32; 10]`, which volatile-writes `u32::default() = 0` into every
element. The resulting field element therefore represents `0`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 64:4-66:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625
namespace Insts.ZeroizeZeroize

/-- **Spec theorem for**
`<curve25519_dalek::backend::serial::u32::field::FieldElement2625 as zeroize::Zeroize>::zeroize`

There is no precondition. Every limb of the result is `0`, hence the represented value is `0`.
`zeroize self` is a single call to the external array `zeroize`, whose result is returned
unchanged, so one `step` with the axiom `Array.Insts.ZeroizeZeroize.zeroize_spec` gives the limb
equalities, which are the first conjunct. For the second, `toNat_eq` and
`Array.uScalarToNatField2625` unfold `result.toNat` to the weighted limb sum, and
`Finset.sum_eq_zero` closes it as every summand is a weight times a zero limb (`Nat.mul_zero`). -/
@[step]
theorem zeroize_spec (self : FieldElement2625) :
    zeroize self ⦃ (result : FieldElement2625) =>
      (∀ i < 10, result[i]!.val = 0) ∧
      result.toNat = 0 ⦄ := by
  unfold zeroize
  step as ⟨a, h_a⟩
  refine ⟨h_a, ?_⟩
  rw [toNat_eq, Array.uScalarToNatField2625]
  exact Finset.sum_eq_zero fun i hi => by
    rw [h_a i (Finset.mem_range.mp hi), Nat.mul_zero]

end Insts.ZeroizeZeroize
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

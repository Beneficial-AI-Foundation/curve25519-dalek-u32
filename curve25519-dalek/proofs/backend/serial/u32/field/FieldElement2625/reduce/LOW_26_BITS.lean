import translated.Funs
open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# ##############################-/
/-*Spec theorem for `LOW_26_BITS`*-/
/-# ##############################-/


@[step]
theorem reduce.LOW_26_BITS_spec :
    reduce.LOW_26_BITS ⦃ (result : U64) => result.bv.toNat = 2^26-1 ⦄ := by
  unfold reduce.LOW_26_BITS
  rfl


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

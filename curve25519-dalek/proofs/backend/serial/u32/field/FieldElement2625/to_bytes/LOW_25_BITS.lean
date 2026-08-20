import translated.Funs
open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# ##############################-/
/-*Spec theorem for `LOW_25_BITS`*-/
/-# ##############################-/


@[step]
theorem to_bytes.LOW_25_BITS_spec :
    to_bytes.LOW_25_BITS ⦃ (result : U32) => result.bv.toNat = 2^25-1 ⦄ := by
  unfold to_bytes.LOW_25_BITS
  rfl


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

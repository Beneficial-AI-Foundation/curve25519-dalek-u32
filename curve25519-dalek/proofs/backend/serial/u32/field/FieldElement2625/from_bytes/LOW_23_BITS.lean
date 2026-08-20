import translated.Funs
open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# ##############################-/
/-*Spec theorem for `LOW_23_BITS`*-/
/-# ##############################-/


@[step]
theorem from_bytes.LOW_23_BITS_spec :
    from_bytes.LOW_23_BITS ⦃ (result : U64) => result.bv.toNat = 2^23-1 ⦄ := by
  unfold from_bytes.LOW_23_BITS
  rfl


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

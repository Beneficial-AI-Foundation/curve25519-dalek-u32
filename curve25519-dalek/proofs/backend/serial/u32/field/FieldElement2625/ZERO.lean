import translated.Funs
import proofs.backend.serial.u32.field.Limbs
open Aeneas Aeneas.Std
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# #######################-/
/-*Spec theorem for `ZERO`*-/
/-# #######################-/

@[step]
theorem ZERO_spec :
    ZERO ⦃ (result : FieldElement2625) => FE2625_as_Nat result = 0 ⦄ := by
  unfold ZERO
  rfl

theorem ZERO_spec_v1 :
    ZERO ⦃ (result : FieldElement2625) => result.val = 0 ⦄ := by
  unfold ZERO from_limbs
  rfl

end curve25519_dalek.backend.serial.u32.field.FieldElement2625

import translated.Funs
open Aeneas Aeneas.Std
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# #######################-/
/-*Spec theorem for `ZERO`*-/
/-# #######################-/

@[step]
theorem ZERO_spec :
    ZERO ⦃ (result : FieldElement2625) => FieldElement2625_to_Nat result = 0 ⦄ := by
  unfold ZERO from_limbs
  step*
  unfold Array.repeat FieldElement2625_to_Nat
  rfl


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

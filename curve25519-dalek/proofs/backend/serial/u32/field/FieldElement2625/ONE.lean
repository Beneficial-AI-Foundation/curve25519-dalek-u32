import translated.Funs
import proofs.backend.serial.u32.field.Limbs
open Aeneas Aeneas.Std
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# #######################-/
/-*Spec theorem for `ONE`*-/
/-# #######################-/


@[step]
theorem ONE_spec :
    ONE ⦃ (result : FieldElement2625) => FE2625_as_Nat result = 1 ⦄ := by
  unfold ONE
  rfl


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

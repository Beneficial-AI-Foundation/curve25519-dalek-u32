import translated.Funs
open Aeneas Aeneas.Std
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# #######################-/
/-*Spec theorem for `ONE`*-/
/-# #######################-/


@[step]
theorem ONE_spec :
    ONE ⦃ (result : FieldElement2625) => FieldElement2625_to_Nat result = 1 ⦄ := by
  unfold ONE from_limbs
  step*
  unfold Array.make FieldElement2625_to_Nat
  rfl


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

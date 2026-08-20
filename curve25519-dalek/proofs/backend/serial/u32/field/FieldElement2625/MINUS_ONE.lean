import translated.Funs
import proofs.P
open Aeneas Aeneas.Std
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# ############################-/
/-*Spec theorem for `MINUS_ONE`*-/
/-# ############################-/


@[step]
theorem MINUS_ONE_spec :
    MINUS_ONE ⦃ (result : FieldElement2625) => FieldElement2625_to_Nat result = p - 1 ⦄ := by
  unfold MINUS_ONE from_limbs
  step*
  unfold FieldElement2625_to_Nat Array.make
  simp [p_in_decimal]


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

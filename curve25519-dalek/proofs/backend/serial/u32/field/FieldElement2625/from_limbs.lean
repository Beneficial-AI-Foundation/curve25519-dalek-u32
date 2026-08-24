import translated.Funs
open Aeneas Aeneas.Std
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-# #############################-/
/-*Spec theorem for `from_limbs`*-/
/-# #############################-/


theorem from_limbs_spec (l : Array Std.U32 10#usize) :
    from_limbs l ⦃ (result : Array Std.U32 10#usize) => result = l ⦄ := by
  unfold from_limbs
  rfl


end curve25519_dalek.backend.serial.u32.field.FieldElement2625

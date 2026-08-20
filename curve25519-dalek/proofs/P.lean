import Mathlib.Tactic.NormNum

/-!
# The field prime `p = 2^255 - 19`

Characterization API: later proofs use only these lemmas below, never the literal value. `p` is made
irreducible immediately after to avoid accidental unfolding.
-/

namespace curve25519_dalek

/-- The prime of the field `ℤ / (2^255 - 19)`. -/
def p : ℕ := 2 ^ 255 - 19

/-Helper theorem to avoid resolving p in decimal format.-/
theorem p_in_decimal :
(p = 57896044618658097711785492504343953926634992332820282019728792003956564819949) := by simp [p]

theorem p_add_19 : p + 19 = 2 ^ 255 := by norm_num [p]

theorem p_pos : 0 < p := by norm_num [p]

theorem two_pow_254_lt_p : 2 ^ 254 < p := by norm_num [p]

theorem p_lt_two_pow_255 : p < 2 ^ 255 := by norm_num [p]

attribute [irreducible] p

end curve25519_dalek

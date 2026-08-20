import translated.Funs
import proofs.ForMathlib
import proofs.backend.serial.u32.field.FieldElement2625.from_bytes.load3_at
import proofs.backend.serial.u32.field.FieldElement2625.from_bytes.load4_at
import proofs.backend.serial.u32.field.FieldElement2625.from_bytes.LOW_23_BITS
open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u32.field.FieldElement2625


/-# #############################-/
/-*Spec theorem for `from_bytes`*-/
/-# #############################-/

/-Let's denote elements of data by d[i], which are of type U8.
h[0] =  load4_at(data,  0); *h[0]=d[0]+2^8·d[1]+2^16·d[2]+2^24·d[3]*
h[1] =  load3_at(data,  4) << 6; *h[1]=2^6·(d[4]+2^8·d[5]+2^16·d[6])*
h[2] =  load3_at(data,  7) << 5; *h[2]=2^5·(d[7]+2^8·d[8]+2^16·d[9])*
h[3] =  load3_at(data, 10) << 3; *h[3]=2^3·(d[10]+2^8·d[11]+2^16·d[12])*
h[4] =  load3_at(data, 13) << 2; *h[4]=2^2·(d[13]+2^8·d[14]+2^16·d[15])*
h[5] =  load4_at(data, 16); *h[5]=d[16]+2^8·d[17]+2^16·d[18]+2^24·d[19]*
h[6] =  load3_at(data, 20) << 7; *h[6]=2^7·(d[20]+2^8·d[21]+2^16·d[22])*
h[7] =  load3_at(data, 23) << 5; *h[7]=2^5·(d[23]+2^8·d[24]+2^16·d[25])*
h[8] =  load3_at(data, 26) << 4; *h[8]=2^4·(d[26]+2^8·d[27]+2^16·d[28])*
h[9] = (load3_at(data, 29) & LOW_23_BITS) << 2; *h[9]=2^2·(d[29]+2^8·d[30]+2^16·d[31] mod 2^23)*

Therefore
*h[0]=d[0]+2^8·d[1]+2^16·d[2]+2^24·d[3]*
*2^26·h[1]=2^32·(d[4]+2^8·d[5]+2^16·d[6])*
*2^51·h[2]=2^56·(d[7]+2^8·d[8]+2^16·d[9])*
*2^77·h[3]=2^80·(d[10]+2^8·d[11]+2^16·d[12])*
*2^102·h[4]=2^104·(d[13]+2^8·d[14]+2^16·d[15])*
*2^128·h[5]=2^128·(d[16]+2^8·d[17]+2^16·d[18]+2^24·d[19])*
*2^153·h[6]=2^160·(d[20]+2^8·d[21]+2^16·d[22])*
*2^179·h[7]=2^184·(d[23]+2^8·d[24]+2^16·d[25])*
*2^204·h[8]=2^208·(d[26]+2^8·d[27]+2^16·d[28])*
*2^230·h[9]=2^232·(d[29]+2^8·d[30]+2^16·d[31] mod 2^23)*

The last step is why there is the *warning* in the original Rust comment.
The function `from_bytes` preserves the Nat representation only if the input is < 2^255.

Example for when the bound doesn't hold: converting 2^255 into a FieldElement2625.
Without the masking the result would be a field element with Nat representation = 19,
but instead it gives 0.-/
def try_1 : Option Nat :=
  let result := from_bytes (Array.make 32#usize [0#u8,0#u8,0#u8,0#u8,0#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,128#u8])
  match result with
  | Result.ok x => some (FieldElement2625_to_Nat x)
  | _ => none

#eval try_1

/-When `input < 2^255` the Nat representation of the result is correct,
even when `input > p`.
Example from original comment: convert 2^255-18 into a FieldElement2625 by applying from_bytes.
The result as a field element has Nat representation 1.-/
def try_2 : Nat :=
  let result := from_bytes (Array.make 32#usize [238#u8,255#u8,255#u8,255#u8,
  255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,
  255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,
  255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,127#u8])
  match result with
  | Result.ok x => FieldElement2625_to_Nat x
  | _ => 0

#eval try_2
#eval try_2 % (2^255-19)

/-Helper function to convert Array U8 32#usize to Nat:-/
def ArrayU8_to_Nat (a : Array U8 32#usize) : Nat :=
  a[0]!.val +
  2^8 * a[1]!.val + 2^16 * a[2]!.val + 2^24 * a[3]!.val +
  2^32 * a[4]!.val + 2^40 * a[5]!.val + 2^48 * a[6]!.val +
  2^56 * a[7]!.val + 2^64 * a[8]!.val + 2^72 * a[9]!.val +
  2^80 * a[10]!.val + 2^88 * a[11]!.val + 2^96 * a[12]!.val +
  2^104 * a[13]!.val + 2^112 * a[14]!.val + 2^120 * a[15]!.val +
  2^128 * a[16]!.val + 2^136 * a[17]!.val + 2^144 * a[18]!.val +
  2^152 * a[19]!.val + 2^160 * a[20]!.val + 2^168 * a[21]!.val +
  2^176 * a[22]!.val + 2^184 * a[23]!.val + 2^192 * a[24]!.val +
  2^200 * a[25]!.val + 2^208 * a[26]!.val + 2^216 * a[27]!.val +
  2^224 * a[28]!.val + 2^232 * a[29]!.val + 2^240 * a[30]!.val +
  2^248 * a[31]!.val
#exit
/-- Helper lemma stating that if all 10 elements of a 10-long array are
bounded by 2^32 and we update an element by a value `x` of the form
`x = y <<< m % U64.size` where `y < 2 ^ n` and `n + m ≤ 32`
then each term of the resulting array is still bounded by 2 ^ 32: -/
private theorem set_bound {a a' : Array U64 10#usize} {x y : U64} {k : Usize} {n m : Nat}
(heq : (a' = a.set k x)) (ha : ∀ j, j < 10 → a[j]!.val < 2 ^ 32)
(hx : x.val = y.val <<< m % U64.size) (hy : y.val < 2 ^ n) (hexp : n + m ≤ 32) :
    ∀ j, j < 10 → a'[j]!.val < 2^32 :=
  by
  intro j hj; subst a'; by_cases j = k.val
  --The non-trivial case when a'[j] is a[j] replaced by x:
  case pos =>
    simp_lists
    rewrite [hx, Nat.shiftLeft_eq]
    have hmul := Nat.mul_lt_mul_of_pos_right (k := 2 ^ m) hy (by exact Nat.two_pow_pos m)
    rewrite [← Nat.pow_add] at hmul
    rewrite [U64.size_def, U64.numBits_eq, Nat.mod_eq_of_lt (by
    --Closing the intermediate goal coming from rewriting the mod:
      exact Nat.lt_of_lt_of_le (k := 2 ^ 64) hmul (by
        exact Nat.pow_le_pow_of_le (by decide) (by exact Nat.le_trans (k := 64) hexp (by decide))
        )
      )]
    exact Nat.lt_of_lt_of_le (k := 2 ^ 32) hmul (by exact Nat.pow_le_pow_of_le (by decide) hexp )
  --The simple case when a'[j] = a[j]:
  case neg =>
    have h := ha j hj; simp_lists at h ⊢; exact h

/-- Helper lemma that states that if one updates a limb from `0` to `x` in
an `Array U64 10#usize` representation of a `FieldElement2625` then
the Nat value of the element increases by `x times the limb's weight`: -/
private theorem set_zero_to_x {a a' : Array U64 10#usize} {k : Usize} {x : U64} {n : Nat}
(heq : (a' = a.set k x)) (hindex : k.val < 10) (hzero : a[k.val]!.val = 0)
(hold_sum : ArrayU64_to_Nat a = n) :
    ArrayU64_to_Nat a' = n + (↑x) * 2 ^ (26 * ((k.val + 1) / 2) + 25 * (k.val / 2)) :=
  by
  rewrite [heq, ← hold_sum]
  unfold ArrayU64_to_Nat
  rcases hk : k.val with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k.val
  iterate 10
    · rewrite [hk] at hzero; rewrite [hzero]; simp_lists; scalar_tac
  exact absurd hk (by scalar_tac)



theorem from_bytes_spec (data : Array U8 32#usize) :
    from_bytes data ⦃ (result : FieldElement2625) =>
      FieldElement2625_to_Nat result % p = ((ArrayU8_to_Nat data) % 2^255) % p ⦄ := by
  unfold from_bytes
  step*
  /-# Proving that from_bytes.load3_at has the bound for index 29:-/
  case hi =>
    rewrite [s9_post]; simp
  /-# Proving the precondition bound from reduce:-/
  case hz =>
  --Introduce and prove the bound i18 < 2 ^ 23:
    have i18_post : ↑i18 < (2 ^ 23 : Nat) := by
      rewrite [U64.bv_toNat] at i17_post
      rewrite [i18_post1]
      have i17_post1 := Nat.lt_of_le_sub_one (by decide) (Nat.le_of_eq i17_post)
      exact Nat.lt_of_le_of_lt (Nat.and_le_right) i17_post1
    --Helper step stating that each element of a constant 0 array is < 2^32:
    have hinit_bound : ∀ j, j < 10 → (Array.repeat 10#usize 0#u64)[j]!.val < 2^32 := by
      simp_lists [Array.repeat_val]; decide
    /-Introducing hypotheses for the two cases, where no bit-shift happens,
    to be able to use the helper lemma set_bound:-/
    have i_post : ↑i = ↑i <<< 0 % U64.size := by
      rewrite [Nat.shiftLeft_zero, U64.val_mod_size_eq]; rfl
    have i9_post : ↑i9 = ↑i9 <<< 0 % U64.size := by
      rewrite [Nat.shiftLeft_zero, U64.val_mod_size_eq]; rfl
    --Renaming the initial hypothesis to fit the general pattern:
    rename' hinit_bound => b_old
    --Rolling forward the bounds on the arrays:
    iterate 10
      --Step forward and establish the bound on the next array:
      have b_next := set_bound ‹_› b_old (by assumption) (by assumption) (by decide)
      --Clean-up:
      clear b_old
      --Rename to be able to iterate the process:
      rename' b_next => b_old
    intro j hj
    have hb_old := b_old j hj
    apply_rewrite [Nat.le_of_lt] at hb_old
    exact Nat.le_trans hb_old (by decide)
  /-# Proving that the result represents the same field element as data % 2^255:-/
  rewrite [result_post2]
  unfold ArrayU8_to_Nat
  --experimenting
  have hinit_to_Nat : ArrayU64_to_Nat (Array.repeat 10#usize 0#u64) = 0 := by
    rfl
  iterate 10
    have hnext_to_Nat := set_zero_to_x (by assumption) (by decide) (by simp [*]) hinit_to_Nat
    simp [-Nat.reducePow] at hnext_to_Nat
    clear hinit_to_Nat
    rename' hnext_to_Nat => hinit_to_Nat
  rewrite [hinit_to_Nat]
  clear hinit_to_Nat
  --Introduce and prove the bound i18 < 2 ^ 23:
  have i18_post : ↑i18 < (2 ^ 23 : Nat) := by
    rewrite [U64.bv_toNat] at i17_post
    rewrite [i18_post1]
    have i17_post1 := Nat.lt_of_le_sub_one (by decide) (Nat.le_of_eq i17_post)
    exact Nat.lt_of_le_of_lt (Nat.and_le_right) i17_post1
  iterate 8
    have hmod_kill := (by assumption : _ = _ <<< _ % U64.size)
    rewrite [hmod_kill, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (b := U64.size) (by
      rewrite [U64.size_def, U64.numBits_eq]
      exact Nat.lt_trans (k := 2 ^ 64)
        (Nat.mul_lt_mul_of_pos_right (k := 2 ^ _) (by assumption) (by decide))
        (by decide) )]
    clear hmod_kill
    clear (by assumption : _ = _ <<< _ % U64.size) --kind of a risky move...
  rewrite [i18_post1, UScalar.val_and, ← U64.bv_toNat i17, i17_post, Nat.and_two_pow_sub_one_eq_mod]
  simp [Nat.mul_assoc, ← Nat.mul_mod_mul_right, -Nat.reducePow, ← Nat.pow_add, -p_in_decimal]
  have hadd_mod_disj_bits : ∀ a b m n : Nat, (a < 2 ^ m) → (m ≤ n) →
    a + b * 2 ^ m % 2 ^ n = (a + b * 2 ^ m) % 2 ^ n := by
    intro a b m n ha hexp
    rewrite [← Nat.mod_eq_of_lt (a := a) (b := 2 ^ n) (by
      exact Nat.lt_of_lt_of_le (k := 2 ^ n) ha (by
        exact Nat.pow_le_pow_right (by decide) hexp) )]
    rewrite [Nat.mod_add_mod, Nat.mod_add_mod_eq]
    simp
    nth_rewrite 2 [ ← Nat.pow_sub_mul_pow 2 hexp, Nat.mul_comm]
    rewrite [Nat.mul_comm, Nat.mul_mod_mul_left]
    rewrite [Nat.mod_eq_of_lt (a := a) (b := 2 ^ n) (by
      exact Nat.lt_of_lt_of_le (k := 2 ^ n) ha (by
        exact Nat.pow_le_pow_right (by decide) (hexp)) )]
    have hlt_shiftLeft_mod_two_pow : 2 ^ m * (b % 2 ^ (n - m)) ≤ 2 ^ n - 2 ^ m := by
      nth_rewrite 2 [← Nat.one_mul (2 ^ m)]
      rewrite [← Nat.pow_sub_mul_pow 2 hexp, ← Nat.mul_sub_right_distrib, Nat.mul_comm]
      exact Nat.mul_le_mul_right (k := 2 ^ m) (by
        exact Nat.le_sub_one_of_lt (by
          exact Nat.mod_lt b (by exact Nat.two_pow_pos (n - m))))
    rewrite [Nat.add_comm, ← Nat.sub_add_cancel (n := 2 ^ n) (m := 2 ^ m) (by exact Nat.pow_le_pow_right (by decide) hexp)]
    exact Nat.add_lt_add_of_le_of_lt hlt_shiftLeft_mod_two_pow ha
  rewrite [hadd_mod_disj_bits _ _ _ _ (by scalar_tac) (by decide)]
  simp [*, -Nat.reducePow, -p_in_decimal]
  agrind



end curve25519_dalek.backend.serial.u32.field.FieldElement2625

/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
import Dalek32.Lint.Basic
import translated.Funs

/-!
# Spec axioms for external functions

The functions below are still opaque `axiom`s in `translated/FunsExternal.lean` (no Lean model).
Instead of modelling them, we assume their specifications here. Each axiom is stated so that the
real Rust behaviour satisfies it, so this file is the complete list of trusted external
assumptions used by the `u32/field.rs` proofs.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace U32.Insts.SubtleConditionallySelectable

-- docs: https://docs.rs/subtle/2.6.1/subtle/trait.ConditionallySelectable.html#method.conditional_assign
-- src:  https://docs.rs/subtle/2.6.1/src/subtle/lib.rs.html#521-527
/-- **Spec axiom for `<u32 as subtle::ConditionallySelectable>::conditional_assign`**

`subtle-2.6.1/src/lib.rs`, lines 521-527: `*self ^= mask & (*self ^ *other)` with
`mask = -(choice as u32)`. For a valid choice this keeps `a` for `0` and returns `b` for `1`. -/
@[step]
axiom conditional_assign_spec (a b : U32) (choice : subtle.Choice)
    (h_choice : choice = 0#u8 ∨ choice = 1#u8) :
    conditional_assign a b choice ⦃ (result : U32) =>
      result = if choice = 1#u8 then b else a ⦄

-- docs: https://docs.rs/subtle/2.6.1/subtle/trait.ConditionallySelectable.html#method.conditional_swap
-- src:  https://docs.rs/subtle/2.6.1/src/subtle/lib.rs.html#529-535
/-- **Spec axiom for `<u32 as subtle::ConditionallySelectable>::conditional_swap`**

`subtle-2.6.1/src/lib.rs`, lines 529-535: `t = mask & (*a ^ *b); *a ^= t; *b ^= t` with
`mask = -(choice as u32)`. For a valid choice this swaps the pair for `1` and keeps it for `0`. -/
@[step]
axiom conditional_swap_spec (a b : U32) (choice : subtle.Choice)
    (h_choice : choice = 0#u8 ∨ choice = 1#u8) :
    conditional_swap a b choice ⦃ (r1 : U32) (r2 : U32) =>
      (r1, r2) = if choice = 1#u8 then (b, a) else (a, b) ⦄

end U32.Insts.SubtleConditionallySelectable


namespace Array.Insts.ZeroizeZeroize

-- docs: https://docs.rs/zeroize/1.8.2/zeroize/trait.Zeroize.html
--       https://docs.rs/zeroize/1.8.2/zeroize/trait.DefaultIsZeroes.html
-- src:  https://docs.rs/zeroize/1.8.2/src/zeroize/lib.rs.html#373-377
--       https://docs.rs/zeroize/1.8.2/src/zeroize/lib.rs.html#297-312
-- Possible generalization: U32 -> UScalar ty for any {ty : UScalarTy}, taking the element's
-- DefaultIsZeroes instance as a parameter plus a hypothesis that its default is 0#ty
-- (without that hypothesis the axiom would be unsound for other instances).
/-- **Spec axiom for `<[u32; N] as zeroize::Zeroize>::zeroize`**

`zeroize-1.8.2/src/lib.rs`, lines 373-377 and 297-312: the array impl zeroizes every element, and
for `u32` (a `DefaultIsZeroes` type) the blanket impl volatile-writes `u32::default() = 0`. Stated
only for the instance that `FieldElement2625::zeroize` passes. -/
@[step]
axiom zeroize_spec {N : Usize} (a : Array U32 N) :
    zeroize (Curve25519Dalek.zeroize.Zeroize.Blanket
      Curve25519Dalek.U32.Insts.ZeroizeDefaultIsZeroes) a ⦃ (result : Array U32 N) =>
      ∀ i < N.val, result[i]!.val = 0 ⦄

end Array.Insts.ZeroizeZeroize


namespace MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut

-- docs: https://doc.rust-lang.org/core/primitive.array.html#impl-IntoIterator-for-%26mut+%5BT;+N%5D
--       https://doc.rust-lang.org/core/primitive.slice.html#method.iter_mut
/-- **Spec axiom for `<&mut [T; N] as IntoIterator>::into_iter`**

`core/src/array/mod.rs`, line 376: `self.iter_mut()`, i.e. a mutable iterator over the array's
elements starting at index `0`. Mirrors Aeneas' `Slice.iter_mut`: the iterator holds the array's
elements, and the backward function reads the (updated) elements back out of the iterator. The
length guard keeps the axiom satisfiable by a total model (the backward function only has to be
faithful on iterators of the right length). -/
@[step]
axiom into_iter_spec {T : Type} {N : Usize} (a : Array T N) :
    into_iter a ⦃ (it : core.slice.iter.IterMut T)
      (back : core.slice.iter.IterMut T → Array T N) =>
      it.slice.val = a.val ∧ it.i = 0 ∧
      ∀ it' : core.slice.iter.IterMut T, it'.slice.val.length = N.val →
        (back it').val = it'.slice.val ⦄

end MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut

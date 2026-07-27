# Standard-library models required (provisional)

**Status: PROVISIONAL / moving target.** Snapshot from Aeneas `b059c34a`, the
**un-worked-around** crate, extracted without `--start-from-pub`. The definitive
set only settles after a clean translation (see notes.md). An earlier broader
snapshot (`678ffd3b` + `--start-from-pub`) surfaced ~100; this narrower run
surfaces 44 stdlib externals. Source: `curve25519-dalek/translated/FunsExternal_Template.lean`.

Total: **44** stdlib (`core` 40, `alloc` 3, `std` 0). No `std` (crate is `no_std`).

## How "called in" was determined

Call sites found by grepping the Rust source for each idiom and resolving the
enclosing `fn` (test-only sites, which Charon does not extract, are omitted).
Two kinds:

- **Specific** — a distinctive call mapping to a few functions (listed below).
- **Pervasive** — the desugaring of `for` loops / iterator chains / slice
  indexing, used across essentially every function that iterates or indexes;
  not enumerated per-site.

---

## alloc::vec (3)
- `Vec::is_empty` — **specific**: `VartimePrecomputedStraus::is_empty`
  ([backend.rs:150](../curve25519-dalek/src/backend.rs#L150)),
  `VartimeEdwardsPrecomputation::is_empty` ([edwards.rs:1079](../curve25519-dalek/src/edwards.rs#L1079)),
  `VartimeRistrettoPrecomputation::is_empty` ([ristretto.rs:1039](../curve25519-dalek/src/ristretto.rs#L1039)),
  `precomputed_straus::…::is_empty`.
- `IntoIterator for &Vec` :: `into_iter` — **pervasive** (`for x in &vec`).
- `IntoIterator for &mut Vec` :: `into_iter` — **pervasive** (`for x in &mut vec`).

## core::array (1)
- `from_fn` — **specific**: `EdwardsPoint::compress_batch<const N>`
  ([edwards.rs:635](../curve25519-dalek/src/edwards.rs#L635), L638).

## core::borrow (1)
- `Borrow<T>::borrow` — **specific (spread across the scalar-mul + accumulator code)**:
  `optional_multiscalar_mul` / `multiscalar_mul` / `optional_mixed_multiscalar_mul`
  in `backend/serial/scalar_mul/{pippenger,straus,precomputed_straus}.rs`;
  `Scalar::{sum,product}` ([scalar.rs:462](../curve25519-dalek/src/scalar.rs#L462), L474);
  `EdwardsPoint::sum` / `RistrettoPoint::sum`; trait defaults in
  [traits.rs:259](../curve25519-dalek/src/traits.rs#L259), L376.

## core::fmt (1)
- `Debug for str::fmt` — **specific-ish**: string formatting in a panic/assert
  message (e.g. `.expect("…")` / `assert!` with a `str`). No arithmetic site.

## core::iter (16) — all **pervasive** (for-loops & iterator adapter chains)
- `Map`: `next`, `fold`, `size_hint`, `next_back`
- `Rev`: `fold`, `size_hint`
- `Skip`: `next`, `fold`, `size_hint`
- `Zip`: `fold`, `size_hint`
- `Range`: `size_hint`
- `Empty`: `next`, `size_hint`, + `iter::empty` — the `Empty`/`empty` ones trace to
  `Trait::vartime_multiscalar_mul` default ([traits.rs:334](../curve25519-dalek/src/traits.rs#L334)).
- by-ref `&mut I`: `size_hint`

## core::num (1)
- `usize::div_ceil` — **specific**: `Scalar::to_radix_2w_size_hint` /
  `Scalar::as_radix_2w` ([scalar.rs:1072](../curve25519-dalek/src/scalar.rs#L1072), L1074, L1121);
  `expand_msg_xmd` ([field.rs:467](../curve25519-dalek/src/field.rs#L467), `digest` feature).

## core::option (5)
- `Option::map` — **pervasive** (`.map()` on point/scalar options, esp. in multiscalar mul).
- `PartialEq for Option::eq` — **pervasive** (`Option == Option`).
- `FromIterator for Option::from_iter`, `Try::branch`, `FromResidual::from_residual`
  — **specific**: the `.collect::<Option<Vec<_>>>()?` in `optional_multiscalar_mul` /
  `optional_mixed_multiscalar_mul` (serial + vector `scalar_mul/{pippenger,straus,precomputed_straus}.rs`,
  e.g. [pippenger.rs:104](../curve25519-dalek/src/backend/serial/scalar_mul/pippenger.rs#L104)).

## core::result (1)
- `Result::map` — **pervasive** (`.map()` on Results).

## core::slice (15)
- `SliceIndex<RangeFull>`: `get`, `get_mut`, `get_unchecked`, `get_unchecked_mut`,
  `index`, `index_mut` — **pervasive** (slice indexing / `.get()`).
- `Iter`: `fold`, `size_hint`, `next_back` — **pervasive** (`.iter()` chains).
- `IterMut`: `fold`, `size_hint`, `next_back` — **pervasive** (`.iter_mut()` chains).
- `Chunks`: `next`, `size_hint`; `[T]::chunks` — **specific**: `read_le_u64_into`
  ([scalar.rs:1389](../curve25519-dalek/src/scalar.rs#L1389)).

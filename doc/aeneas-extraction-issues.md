# Aeneas extraction issues for `curve25519-dalek`

Status of the Charon → Aeneas pipeline on this crate (v5.0.0-rc.1, edition 2024):

- **Charon**: extracts cleanly (exit 0) with the serial u64 backend forced
  (`--cfg curve25519_dalek_backend="serial" --cfg curve25519_dalek_bits="64"`) and
  `--start-from-pub`. No Charon errors or warnings.
- **Aeneas** (`678ffd3b`): fails on a set of functions. These are **not** version
  regressions — the newer source uses iterator/closure/borrow constructs that expose
  distinct Aeneas issues. Each is to be fixed upstream in Aeneas.

How this was produced:
```
charon cargo --preset=aeneas --start-from-pub -- --no-default-features --features alloc,zeroize
aeneas -backend lean -split-files -print-error-emitters -print-error-diagnostics \
       -max-error-spans -1 -dest curve25519-dalek -subdir translated curve25519_dalek.llbc
```
`Aeneas src` below is the compiler source location that emits the error
(`-print-error-emitters`). `Rust src` is the construct that triggers it.

---

## A. `bool ^ bool` → "Invalid inputs for binop"

- **Aeneas src**: `interp/InterpExpressions.ml:1155`
- **Rust src**: `montgomery.rs:195:29-195:49` in `MontgomeryPoint::mul_bits_be`
  ```rust
  let choice: u8 = (prev_bit ^ cur_bit) as u8;   // prev_bit, cur_bit: bool
  ```
- **Issue**: Aeneas's binop evaluator rejects `^` (BitXor) applied to two `bool`
  operands (and/or the subsequent `bool as u8` cast). Minimal, isolated.

---

## B. Borrows flowing through iterator-closures → "Internal error" (`InterpBorrowsCore.ml:1498`)

All share the same emitter; the common shape is an iterator adaptor chain whose
closure borrows slice elements, often combined with `collect::<Vec<_>>()`.

- `field.rs:265:60-265:67` — `FieldElement51::internal_invert_batch`
  ```rust
  for (input, scratch) in inputs.iter_mut().rev().zip(scratch.iter_mut().rev()) { ... }
  ```
- `scalar.rs:845:60-845:67` — `Scalar::invert_batch_internal`
  ```rust
  for (input, scratch) in inputs.iter_mut().rev().zip(scratch.iter().rev()) { ... }
  ```
- `edwards.rs:595:4-612:5` — `EdwardsPoint::to_montgomery_batch`
  ```rust
  let mut denominators = eds.iter().map(|p| &p.Z - &p.Y).collect::<Vec<_>>();
  for (ed, d) in eds.iter().zip(denominators.iter()) { let u = &(&ed.Z + &ed.Y) * d; ... }
  ```
- `edwards.rs:634:4-647:5` — `EdwardsPoint::compress_batch_alloc`
  ```rust
  inputs.iter().zip(&zs).map(|(input, recip)| { ... AffinePoint{x,y}.compress() }).collect()
  ```
- `backend/serial/scalar_mul/pippenger.rs:160` — `Pippenger::optional_multiscalar_mul`
  ```rust
  Some(columns.fold(hi_column, |total, p| total.mul_by_pow_2(w as u32) + p))
  ```

**Issue**: `InterpBorrowsCore.ml:1498` is reached when a mutable/shared borrow is
threaded through `zip`/`rev`/`map`/`fold` adaptor closures. Likely a single
borrow-core gap; `iter_mut().rev().zip(...)` is the smallest reproducer.

---

## C. Reversed-range loop with early break → "Region ids" / "Could not match the contexts"

- **Aeneas src**: `interp/InterpUtils.ml:877` ("Region ids should not be visited
  directly; the visitor should catch cases that contain region ids earlier") and
  `interp/InterpJoin.ml:1515` ("Could not match the contexts").
- **Rust src**: `backend/serial/scalar_mul/vartime_double_base.rs:33-38`
  ```rust
  let mut i: usize = 255;
  for j in (0..256).rev() { i = j; if a_naf[i] != 0 || b_naf[i] != 0 { break; } }
  ```
- **Issue**: the loop-join fixpoint hits region ids it expects to have been caught
  earlier. 5 of the "Region ids" errors carry no Rust span — they originate in the
  join/fixpoint and accompany the loops in the affected functions.

---

## D. `impl DoubleEndedIterator` returned from a `Range::map` closure → "Internal error"

- **Aeneas src**: `interp/InterpProjectors.ml:544` and `interp/InterpUtils.ml:151`
- **Rust src**: `scalar.rs:874-881` — `Scalar::bits_le`
  ```rust
  pub(crate) fn bits_le(&self) -> impl DoubleEndedIterator<Item = bool> + '_ {
      (0..256).map(|i| ((self.bytes[i >> 3] >> (i & 7)) & 1u8) == 1)
  }
  ```
- **Issue**: projector/internal error on a function returning an opaque
  `impl DoubleEndedIterator + '_` built from `(0..N).map(closure)` capturing `&self`.

---

## E. `into_iter().map(Ctor::from).collect()` → "Unimplemented" (`RegionsHierarchy.ml:193`)

- **Aeneas src**: `llbc/RegionsHierarchy.ml:193`
- **Rust src**: `ristretto.rs:605:12-605:60` — `RistrettoPoint::double_and_compress_batch`
  ```rust
  let states: Vec<BatchCompressState> =
      points.into_iter().map(BatchCompressState::from).collect();
  let mut invs: Vec<FieldElement> = states.iter().map(|state| state.efgh()).collect();
  ```
- **Issue**: regions-hierarchy computation is unimplemented for this `map(...).collect()`
  shape (closure over a locally-defined struct with `IntoIterator` bound).

---

## F. Single-field tuple-struct name clashes (DEFERRED — to mend later)

- **Aeneas src**: `extract/ExtractBase.ml:269` (clash) / `:303` (register).
  Aeneas points to its `tests/src/rename_attribute.rs` rename mechanism as the fix.
- **Rust src**: `edwards.rs:175` `CompressedEdwardsY`, `ristretto.rs:223`
  `CompressedRistretto`, `ristretto.rs:496` `RistrettoPoint` — all
  `pub struct X(pub [u8; 32])` / single-field tuple structs.
- **Issue**: the type becomes a Lean type alias (`def edwards.CompressedEdwardsY :=
  Array Std.U8 32`) while the tuple-struct constructor is registered under the same
  name → "generated code will be incorrect". Not investigated further per instruction.

---

## G. Cascades (not independent bugs)

`Could not find: trait_impl_id: N` (`extract/ExtractBase.ml:484`) at
`ristretto.rs:568` (×6), `precomputed_straus.rs:33-128`, `ristretto.rs:1007-1049`,
`edwards.rs:1041-1076` are downstream of the failures above (the failed
closures'/impls' ids can't be resolved at extraction time).

---

## Summary of distinct upstream issues

| # | Symptom | Aeneas emitter | Trigger |
|---|---------|----------------|---------|
| A | Invalid inputs for binop | InterpExpressions.ml:1155 | `bool ^ bool` (+ `as u8`) |
| B | Internal error | InterpBorrowsCore.ml:1498 | borrows through `zip`/`rev`/`map`/`fold` closures |
| C | Region ids / Could not match contexts | InterpUtils.ml:877, InterpJoin.ml:1515 | `for _ in (0..N).rev() { … break }` |
| D | Internal error | InterpProjectors.ml:544 | return `impl DoubleEndedIterator` from `Range::map` |
| E | Unimplemented | RegionsHierarchy.ml:193 | `into_iter().map(Ctor::from).collect()` |
| F | Name clash (deferred) | ExtractBase.ml:269/303 | single-field tuple structs |

---
name: coq-compcert-path
description: Records the filesystem path where CompCert Coq library files are installed. Use when searching for CompCert definitions, lemmas, or types (e.g. `PTree`, `PMap`, `Maps.PTree.get`, `Maps.PTree.set`). Maps.v is the most commonly used module.
---

# CompCert library path

CompCert's Coq source files are available on GitHub. The local opam install does not include the `.v` source files.

## Usage

When looking up a definition, lemma, or notation from CompCert's `lib/` (e.g. `Maps`, `Coqlib`, `Integers`, `Floats`), search the upstream source on GitHub (the local install does not include the `.v` source files).

Key modules in `lib/`:

- `Maps.v` (**most used**) — `PTree` (positive-keyed maps), `PMap`, `ZMap`, `IMap`; key lemmas: `PTree.get`, `PTree.set`, `PTree.gss`, `PTree.gso`, `PTree.elements`, `PTree.fold`
- `Coqlib.v` — general-purpose lemmas on arithmetic, lists, and well-founded relations
- `Integers.v` — machine-integer types (`Int`, `Int64`, `Ptrofs`) and arithmetic
- `Floats.v` — floating-point types and operations
- `Lattice.v` — semi-lattice and lattice structures used in dataflow analyses
- `Iteration.v` — bounded iteration and fixpoint computation
- `Ordered.v` — ordered type signatures
- `Decidableplus.v` — decidability helpers
- `Axioms.v` — admitted axioms (functional extensionality, etc.)
- `UnionFind.v` — union-find data structure
- `Heaps.v` — priority-queue / heap structure
- `Zbits.v` — bit-level operations on integers
- `Intv.v` — integer interval arithmetic
- `IntvSets.v` — sets of integer intervals
- `Postorder.v` — postorder traversal of control-flow graphs
- `Parmov.v` — parallel move algorithm

Browse on GitHub: https://github.com/AbsInt/CompCert/tree/master/lib

To view a specific file:
```
https://github.com/AbsInt/CompCert/blob/master/lib/FILENAME.v
```

For `Maps.v` directly: https://github.com/AbsInt/CompCert/blob/master/lib/Maps.v

---
name: coq-certicoq-path
description: Records the filesystem path where CertiCoq Coq library files are installed. Use when searching for CertiCoq source definitions, lemmas, or types (e.g. `get_list`, `set_lists`, `wf_env`, `preord_env_P`).
---

# CertiCoq library path

CertiCoq's Coq files are installed at:

```
~/.opam/default/lib/coq/user-contrib/CertiCoq
```

## Usage

**Step 1 — Check if the library is installed locally.** When looking up a definition, lemma, or notation from CertiCoq (e.g. in `LambdaANF`, `Libraries`, or other sub-packages), first search under the local path:

```bash
grep -rn "SYMBOL" ~/.opam/default/lib/coq/user-contrib/CertiCoq --include="*.v"
```

Key sub-directories:

- `LambdaANF/` — ANF language definitions, `bstep`, `wf_env`, `get_list`, `set_lists`, `preord_env_P`, `Ensembles_util`, `map_util`, etc.
- `Libraries/` — utility libraries including `maps_util`.

**Step 2 — Fall back to GitHub if not installed locally.** If the local path does not exist or the symbol is not found, search the upstream source on GitHub:

- Browse: https://github.com/CertiRocq/certirocq/tree/coq8.19/theories/
- Key directories on GitHub:
  - `theories/LambdaANF/` — core ANF language and semantics
  - `theories/common/` — shared utilities
  - `theories/Compiler/` — compiler passes
  - `theories/Codegen/` — code generation
  - `theories/Glue/` — glue code generation

To search a specific file on GitHub, navigate to:
```
https://github.com/CertiRocq/certirocq/blob/coq8.19/theories/LambdaANF/FILENAME.v
```
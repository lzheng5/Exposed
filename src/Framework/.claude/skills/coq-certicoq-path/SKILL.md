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

When looking up a definition, lemma, or notation from CertiCoq (e.g. in `LambdaANF`, `Libraries`, or other sub-packages), search under this path:

```bash
grep -rn "SYMBOL" ~/.opam/default/lib/coq/user-contrib/CertiCoq --include="*.v"
```

Key sub-directories:

- `LambdaANF/` — ANF language definitions, `bstep`, `wf_env`, `get_list`, `set_lists`, `preord_env_P`, `Ensembles_util`, `map_util`, etc.
- `Libraries/` — utility libraries including `maps_util`.
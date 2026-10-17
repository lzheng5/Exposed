# CFAAnnotate: Notes on the Implementation

Response to `prompt.md` (Compositional 0CFA).

```
            Label                 CFAAnnotate
LambdaANF ---------> LabeledANF ---------------> LambdaWeb
```

Everything is fully proven: no admits, and no new axioms beyond the model
parameters (`Exposed`, `w0`, `l0`, plus the new `w_int` and its "not exposed" fact).

## Files

- `Base.v`: the two webs. `w_ext` is the existing unique exposed web `w0`
  from `LambdaWeb/UniqueExposed.v`; `w_int` is a new, non-exposed web.
- `Annotate.v`: the TrivialAnnotate functor framework
  (`AnnotateUtil`/`VAnn`/`AnnotateV`/`AnnotateTop`/`AnnotateVVTop`) ported to a
  LabeledANF source. The top-level objects (`V`, `E`, `R`, `G`, `trans_correct`)
  and the top-level fun/letapp compat lemmas come from its `AnnotateTop`.
- `CFA.v`: the analysis and its correctness proof.
  - **Abstract values**: `AVlab l` (a value introduced at the function or
    constructor site `l` of this unit) or `AVext` (a value from the context).
  - **Analysis result**: value sets per variable, return sets per function site,
    site info, and an "escapes" flag per label.
  - **Spec (`check`)**: a declarative constraint system, in the style of
    `SemAnnotate/ValueSetAnalysis.v`. Every elimination site must share a web
    with all values that can reach it; anything passed to or returned through
    `w_ext` must itself escape.
  - **Translation (`annotate`)**: a plain fixpoint mapping each label to `w_ext`
    if it escapes and `w_int` otherwise.
  - **Logical relation**: indexed by abstract value. Escaping values are related
    exactly by the top-level `AnnotateTop.V`; internal ones by a step-indexed
    relation built from the analysis. Runtime labels are never consulted, so
    values from other units may carry any label.
- `Comp.v`: composes Label with CFAAnnotate using `Cross`.

## Main Theorems

- `CFA.top`: `check_top A R e -> T.trans_correct e (annotate A e)`.
- `CFA.trivial_check_top`: every program has an acceptable analysis (the
  "everything escapes" one), so the spec is always satisfiable; in that case the
  result is the all-`w_ext` annotation.
- `Comp.preserves_linking`: `trans_correct_top e1 e1' -> trans_correct_top e2 e2' ->
  trans_correct_top (link f x e1 e2) (link f w_ext x e1' e2')`, with no side
  conditions on free variables.
- `Comp.top_preserves_linking`: separately labeled, analyzed and annotated units
  can be linked.
- `Comp.adequacy`: if the source program terminates, the annotated program
  terminates with a related result.

## Limitations and Choices

- **No solver**: there is no 0CFA solver yet. Any analysis result satisfying
  `check` works; writing and verifying a solver is a separate task.
- **Precision loss**: an escaping function, even one defined in this unit, is
  treated as unknown at its call sites, and its results count as `AVext`.
- **Copied framework**: `Annotate.v` is a copy rather than a generalization of
  TrivialAnnotate's functor over the source language, because generalizing would
  mean changing every existing client of that functor. That refactor is possible
  if real reuse is preferred.
- **Style**: the new proofs follow the project's naming skills; the ported
  `Annotate.v` keeps the original file's bare `intros`.
- **Stale skill path**: the `coq-certicoq-path` skill points at `~/.opam/default`,
  but CertiCoq is installed under `~/.opam/4.14.0/lib/coq/user-contrib/CertiCoq`.

* Compositional 0CFA

Design an CFAAnnotate component in the current pipeline, from
LambdaANF to LambdaWeb. The existing pipeline relies on either an
arity-based analysis or known-function analysis (See ArityAnnotate and
Comp).

This CFAAnnotate component should first perform unique labeling (see
CFAAnnotate/LabeledANF.v and CFAAnnotate/Label.v), producing a labeled ANF
term, then assign proper web ids based on a simple value set (0CFA)
analysis result.

To simplify the problem, we assume there are only two
web ids, `w_int`, and `w_ext`, where `w_ext` is exposed (See
LambdaWeb/Exposed.v). All imported or exported values should be assigned
`w_ext`. All internal program components, such as a locally defined
function or a temporary constructor, should be assigned as `w_int`.

Please keep in mind that we have an intermediate language, the
labeled ANF.

```
            Label                 CFAAnnotate
LambdaANF ---------> LabaledANF ---------------> LambdaWeb
```

Derive the proper top-level linking preservation theorem for the described
pipeline. Please try to reuse the existing Annotate functor framework for the
top-level semantics objects.

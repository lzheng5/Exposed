---
name: coq-pose-proof
description: Prefer `pose proof ... as Name` over `assert (Name := ...)` when introducing intermediate facts from existing hypotheses in Coq proofs. Apply whenever writing or editing Gallina proofs.
---

# Coq: prefer `pose proof` over `assert :=` for introducing intermediate facts

When forwarding an existing hypothesis (or applying a lemma to existing hypotheses) to derive a named intermediate fact in a Coq proof, **use `pose proof EXPR as Hname` rather than `assert (Hname := EXPR)`**. The `assert :=` form is deprecated style in this codebase.

## Rule

- **Deprecated:** `assert (Hname := EXPR).`
- **Preferred:** `pose proof EXPR as Hname.`

## Examples

**Bad:**
```coq
assert (Hza := H _ Hz).
assert (Hzb := HFVb _ Hz).
```

**Good:**
```coq
pose proof (H _ Hz) as Hza.
pose proof (HFVb _ Hz) as Hzb.
```

## When this applies

- Forwarding an existing hypothesis by applying it to arguments.
- Specializing a universally-quantified lemma to specific values.
- Any case where you would write `assert (Hname := some_term)` — the term already has the right type and there is no proof obligation to discharge.

## When this does NOT apply

When the assertion has an explicit type and a proof obligation that must be discharged (with `by ...` or a sub-proof), `assert` is still the right tactic. The deprecation specifically targets the `:= EXPR` form where no proof obligation arises.

**Still use `assert` here:**
```coq
assert (Hwf : wf_env ρ) by (eapply wf_env_set; eauto).
assert (Hlen : length xs = length vs).
{ erewrite ...; eauto. }
```

## Why

`pose proof EXPR as Hname` more directly expresses the operation (extending the context with a named term of known type), reads more naturally, and stays consistent with the rest of the codebase.
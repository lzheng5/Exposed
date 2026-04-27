---
name: coq-assert
description: Enforce concise, readable proof scripts by using the `by` tactical for short-form assertions.
---

## Description
When introducing an auxiliary lemma or assertion within a proof, avoid opening a new nested block if the proof of that assertion can be expressed in a single line. This reduces "tactic drift" and keeps the primary proof flow focused.

## Usage Rules
*   **One-Liner Rule**: If the proof of an assertion is a single tactic or a simple chain (using `;`), you **must** use the inline `by` syntax.
*   **Forced Closure**: Using `by` ensures the sub-proof is complete; if the tactic doesn't solve the assertion, Coq will throw an error immediately, which is better for debugging.
*   **Naming**: Always name the hypothesis (e.g., `H : P`) to prevent anonymous hypotheses from cluttering the context.

## Examples

### Bad (Verbose)
```coq
assert (H : x = y).
{ apply symmetry. apply Hxy. }
```

### Good (Concise)
```coq
assert (H : x = y) by (apply symmetry; apply Hxy).
```

---

## Trigger Conditions
*   When generating a proof script and a small intermediate fact is needed.
*   When refactoring existing `assert` blocks that only contain 1-2 tactics.

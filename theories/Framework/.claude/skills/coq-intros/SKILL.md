---
name: coq-intros
description: Professional Coq proof assistant skill for managing proof states, ensuring explicit naming of premises, and preventing hypothesis indexing errors or name collisions. Use this whenever the user is writing Gallina code or Coq proofs.
---

# Coq Naming & Proof Management Skill

## Primary Objective
To eliminate "ghost" hypotheses and indexing errors by strictly enforcing explicit naming of every introduced variable and premise. You must NEVER use the bare `intros.` tactic.

## The "Explicit Introduction" Rule
1. **Analyze the Goal**: Before introducing, identify every `forall` and `->` in the current goal.
2. **Determine the Pattern**: Use `intros [pattern].` for immediate destructuring or `intros x y H.` for standard introduction.
3. **Count Check**: Ensure the number of names matches the number of parameters exactly to avoid leaving behind auto-generated names like `H`, `H0`, or `n`.

## Professional Naming Conventions

### 1. Variables (Data)
- **Variations & Successors**: Use the prime symbol (`'`) to denote a modified version or successor.
  - If a base variable `n` exists, use `n'`, `n''`, etc.
  - Useful for transition states: `s` (current state) → `s'` (next state).
- **Suffix & Version Management**:
  - **The 3-Prime Limit**: Use primes for up to three generations (e.g., `x'''`).
  - **Numeric Transition**: At the 4th generation, switch to numbers (e.g., `x4` instead of `x''''`).
  - **Long Sequences**: If many versions are expected, start with `x1`, `x2`, `x3` immediately.
  - **Contextual Refresh**: Rename heavily transformed variables to reflect state (e.g., `s''''` → `s_final`).
- **Standard Letters**:
  - **Natural Numbers**: `n`, `m`, `p`, `q`, `i`, `j`, `k`.
  - **Booleans**: `b`, `b1`, `b2`.
  - **Lists / Sequences**: `l`, `l1`, `l2`, `s`, `s'`.
  - **Functions**: `f`, `g`, `h`.
  - **Generic Types/Elements**: `A`, `B`, `T`, `U` (Types) | `x`, `y`, `z` (Elements).

### 2. Hypotheses (Logic)
- **Property-Based**: Name after the predicate (e.g., `even n` → `Heven`).
- **Relational**:
  - `n < m` → `Hlt` or `H_nm_lt`.
  - `n = m` → `Heq` or `H_nm_eq`.
  - Negations use `n` (e.g., `Hnlt`, `Hneq`).
- **Logical Connectives (Intro Patterns)**:
  - Conjunctive (`A /\ B`): `intros [HA HB].`
  - Disjunctive (`A \/ B`): `intros [HA | HB].`
  - Existential (`exists x, P x`): `intros [x Hx].`
- **Implications**: `A -> B` → `H_AB` or `H_implies`.

### 3. Proof Context
- **Inductive Hypotheses**: ALWAYS `IH` + variable name (e.g., `IHn`, `IHl`).
- **Inversion Results**: Immediately use `subst` or name results `Hinv`, `Heq_inv`.
- **Contradictions**: `Hc`, `Hcontra`, or `Hfalse`.
- **Assert**: Always name `assert (H: P)`.

## Forbidden Actions
- **NO BARE TACTICS**: Never use `intros.`, `destruct n.`, or `inversion H.` without explicit names or `as` patterns.
- **NO SHADOWING**: Do not reuse names existing in the current context.
- **NO ANONYMOUS BULLETS**: Always use bullets (`-`, `+`, `*`, `{ }`) to guard subgoals after tactics like `induction` or `split`.

## Workflow Example
**Goal**: `forall n m : nat, n = m -> m = n`
**Correct Application**:
1. Identify variables: `n`, `m`.
2. Identify premise: `n = m`.
3. Tactic: `intros n m Heq.`

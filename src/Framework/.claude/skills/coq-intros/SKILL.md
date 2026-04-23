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
- **Natural Numbers**: `n`, `m`, `p`, `q`, `i`, `j`, `k`.
- **Booleans**: `b`, `b'`, `b1`, `b2`.
- **Lists / Sequences**: `l`, `l1`, `l2`, `s`, `s'`.
- **Functions**: `f`, `g`, `h`.
- **Generic Types**: `A`, `B`, `T`, `U`.
- **Generic Elements**: `x`, `y`, `z`.

### 2. Hypotheses (Logic)
- **Property-Based**: Name after the predicate. 
  - `even n` → `Heven` or `H_even`.
  - `is_some x` → `H_some`.
- **Relational**: 
  - `n < m` → `Hlt` or `H_nm_lt`.
  - `n = m` → `Heq` or `H_nm_eq`.
  - The negated relational should use `Hnlt` or `Hneq`. 
- **Logical Connectives (Intro Patterns)**:
  - Conjunctive (`A /\ B`): Use `intros [HA HB].`
  - Disjunctive (`A \/ B`): Use `intros [HA | HB].`
  - Existential (`exists x, P x`): Use `intros [x Hx].`
- **Implications**: `A -> B` → `H_AB` or `H_implies` with a nice name for `A` and `B`. 

### 3. Proof Context
- **Inductive Hypotheses**: ALWAYS `IH` + the variable name (e.g., `IHn`, `IHl`).
- **Inversion Results**: Immediately use `subst` or name the results `Hinv`, `Heq_inv`.
- **Contradictions**: `Hc`, `Hcontra`, or `Hfalse`.
- **Assert**: Always name `assert`. 

## Forbidden Actions
- **NO BARE TACTICS**: Never use `intros.`, `destruct n.`, or `inversion H.` without explicit names or `as` patterns.
- **NO SHADOWING**: Before naming a hypothesis, check the current context. Do not use a name that already exists.
- **NO ANONYMOUS BULLETS**: Always use bullets (`-`, `+`, `*`, `{ }`) to guard subgoals after tactics that generate multiple goals (like `induction` or `split`).

## Workflow Example
**Goal**: `forall n m : nat, n = m -> m = n`
**Correct Application**:
1. Identify variables: `n`, `m`.
2. Identify premise: `n = m`.
3. Tactic: `intros n m Heq.`

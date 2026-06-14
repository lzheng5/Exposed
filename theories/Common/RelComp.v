From Coq Require Import Classes.RelationClasses.

(* Composition of Pipelines *)

(* 1. Same Language Composition *)
(* Similiar to R_n in CertiCoq except R is a preorder in this setting,
 * so there is no need to take the transitive closure here *)
Inductive Comp {A : Type} (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
| Zero :
  forall c,
    Comp R 0 c c

| Step :
  forall n c1 c2 c3,
    R c1 c2 ->
    Comp R n c2 c3 ->
    Comp R (S n) c1 c3.

Hint Constructors Comp : core.

Theorem Comp_refl {A} {R : A -> A -> Prop} :
  Reflexive R ->
  forall n, Reflexive (Comp R n).
Proof.
  intros HR n.
  induction n; simpl; intros; econstructor; eauto.
Qed.

Theorem Comp_trans {A} {R : A -> A -> Prop} :
  Transitive R ->
  forall n m c1 c2 c3,
    Comp R n c1 c2 ->
    Comp R m c2 c3 ->
    Comp R (n + m) c1 c3.
Proof.
  intros HR n m c1 c2 c3 H.
  induction H; intros; simpl; eauto.
Qed.

(* 2. Cross Language Composition *)
Definition Cross {A : Type} {B : Type} {C : Type}
  (R1 : A -> B -> Prop) (R2 : B -> C -> Prop)
  (a : A) (c : C) : Prop :=
  exists b, R1 a b /\ R2 b c.

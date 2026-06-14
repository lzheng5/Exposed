From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From Hammer Require Import Hammer Tactics Reflect.

Module M := Maps.PTree.
Definition var := M.elt.
Definition vars := Ensemble var.

(* Constructor Tags *)
Definition ctor_tag := M.elt.

Inductive find_tag {exp : Type} : list (ctor_tag * exp) -> ctor_tag -> exp -> Prop :=
| find_tag_hd :
  forall c e l,
    find_tag ((c, e) :: l) c e

| find_tag_tl :
  forall c e l c' e',
    find_tag l c' e' ->
    c <> c' ->
    find_tag ((c, e) :: l) c' e'.

Hint Constructors find_tag : core.

Lemma find_tag_deterministic {exp : Type} {cl c} {e e' : exp} :
  find_tag cl c e ->
  find_tag cl c e' ->
  e = e'.
Proof.
  intros H. revert e'.
  induction H; sauto.
Qed.

(* Label *)
Definition label := M.elt.
Definition labels := Ensemble label.
Definition next_label l : label := Pos.succ l.

Lemma next_label_lt l : Pos.lt l (next_label l).
Proof.
  unfold next_label.
  eapply Pos.lt_succ_diag_r; eauto.
Qed.

Lemma next_label_le l : Pos.le l (next_label l).
Proof.
  eapply Pos.lt_le_incl; eauto.
  eapply next_label_lt; eauto.
Qed.

(* Fuel *)
Definition fuel := nat.

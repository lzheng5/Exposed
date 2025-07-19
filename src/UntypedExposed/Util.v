Require Import Lia.

Theorem strong_induction : forall P : nat -> Prop,
  (forall m : nat, (forall k : nat, k < m -> P k) -> P m) ->
  forall n : nat, P n.
Proof.
  intros P H n; enough (H_goal: forall p, p <= n -> P p).
  - apply H_goal; lia.
  - induction n.
    + intros.
      apply H; lia.
    + intros.
      apply H.
      intros.
      apply IHn.
      lia.
Qed.


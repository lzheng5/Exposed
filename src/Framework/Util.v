From Coq Require Import Sets.Ensembles Lists.List.
From CertiCoq.Libraries Require Import maps_util.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util tactics.
Require Import Lia.

Ltac rewrite_math t :=
  let H := fresh "Hmath" in
  assert (H : t) by lia;
  rewrite H in *; clear H.

Lemma normalize_step : forall i j, j <= i -> i - (i - j) = j.
Proof. intros; lia. Qed.

Lemma Forall2_nth_error {A B P i vs vs'} {v : A}:
  nth_error vs i = Some v ->
  Forall2 P vs vs' ->
  exists (v' : B),
    nth_error vs' i = Some v' /\
    P v v'.
Proof.
  intros.
  revert i v H.
  induction H0; simpl; intros.
  - apply nth_error_In in H.
    inv H.
  - destruct i; simpl in *; eauto.
    inv H1.
    eexists; split; eauto.
Qed.

Lemma Forall_nth_error {A P i vs} {v : A}:
  nth_error vs i = Some v ->
  Forall P vs ->
  exists (v : A),
    nth_error vs i = Some v /\
    P v.
Proof.
  intros.
  revert i v H.
  induction H0; simpl; intros.
  - apply nth_error_In in H.
    inv H.
  - destruct i; simpl in *; eauto.
Qed.

Lemma Forall_monotonic {A} (R R' : A -> Prop) (l : list A):
  (forall x, R x -> R' x) ->
  Forall R l ->
  Forall R' l.
Proof.
  intros H.
  induction l as [| x xs IHxs ]; intros Hall.
  - inv Hall; eauto.
  - inv Hall. constructor; eauto.
Qed.

Lemma Disjoint_FromList_cons_l {A} : forall {xs a S},
  Disjoint A (FromList (a :: xs)) S ->
  Disjoint A (FromList xs) S.
Proof.
  intros.
  inv H; constructor; intros x Hc.
  apply (H0 x).
  unfold Ensembles.In, FromList in *.
  inv Hc.
  constructor; auto.
  unfold Ensembles.In.
  apply in_cons; auto.
Qed.

Lemma Disjoint_FromList_cons_r {A} : forall {xs a S},
  ~ (In a xs) ->
  Disjoint A (FromList xs) S ->
  Disjoint A (FromList xs) (a |: S).
Proof.
  intros.
  inv H0; constructor; intros x Hc.
  inv Hc.
  inv H2.
  - inv H3.
    unfold Ensembles.In, FromList in *.
    contradiction.
  - apply (H1 x).
    constructor; unfold Ensembles.In, FromList in *; auto.
Qed.

Lemma not_In_cons_Union {A a xs Γ} {x : A}:
  (x \in (FromList (a :: xs) :|: Γ)) ->
  a <> x ->
  (x \in (FromList xs :|: Γ)).
Proof.
  intros.
  inv H.
  - inv H1; try contradiction.
    apply Union_introl; auto.
  - apply Union_intror; auto.
Qed.


Lemma set_lists_In {A} :
  forall {xs vs x ρ ρ'},
    In x xs ->
    @set_lists A xs vs ρ = Some ρ' ->
    exists v, In v vs /\ M.get x ρ' = Some v.
Proof.
  intros xs.
  induction xs; simpl; intros; try contradiction.
  destruct vs; try discriminate.
  destruct (set_lists xs vs ρ) eqn:Heq1; try discriminate.
  inv H0.
  inv H; subst.
  - rewrite M.gss in *; auto.
    eexists; split; eauto.
    apply in_eq.
  - edestruct IHxs as [v [Hin Heqv]]; eauto.
    destruct (M.elt_eq a x); subst.
    + rewrite M.gss in *; auto.
      eexists; split; eauto.
      apply in_eq.
    + rewrite M.gso in *; auto.
      eexists; split; eauto.
      apply in_cons; auto.
Qed.

Lemma set_lists_In2 {A} :
  forall {xs vs x ρ1 ρ2 ρ3 ρ4},
    In x xs ->
    @set_lists A xs vs ρ1 = Some ρ2 ->
    @set_lists A xs vs ρ3 = Some ρ4 ->
    exists v, In v vs /\ M.get x ρ2 = Some v /\ M.get x ρ4 = Some v.
Proof.
  intros xs.
  induction xs; simpl; intros; try contradiction.
  destruct vs; try discriminate.
  destruct (set_lists xs vs ρ1) eqn:Heq1; try discriminate.
  destruct (set_lists xs vs ρ3) eqn:Heq2; try discriminate.
  inv H0; inv H1.
  inv H; subst.
  - rewrite M.gss in *; auto.
    rewrite M.gss in *; auto.
    eexists; repeat (split; eauto).
    apply in_eq.
  - edestruct IHxs with (ρ2 := t) (ρ4 := t0) as [v [Hin [Heqv1 Heqv2]]]; eauto.
    destruct (M.elt_eq a x); subst.
    + rewrite M.gss in *; auto.
      rewrite M.gss in *; auto.
      eexists; repeat (split; eauto).
      apply in_eq.
    + rewrite M.gso in *; auto.
      rewrite M.gso in *; auto.
      eexists; repeat (split; eauto).
      apply in_cons; auto.
Qed.

Lemma get_set_eq {A} x ρ (v : A) :
  M.get x ρ = Some v ->
  M.set x v ρ = ρ.
Proof.
  intros.
  apply M.extensionality; intros.
  destruct (M.elt_eq x i); subst.
  - rewrite M.gss; auto.
  - rewrite M.gso; auto.
Qed.

Lemma set_set {A} x y {v : A} {u : A} {ρ} :
  x <> y ->
  M.set x v (M.set y u ρ) = M.set y u (M.set x v ρ).
Proof.
  intros.
  apply M.extensionality.
  intros.
  destruct (var_dec x i); subst.
  - rewrite M.gss; auto.
    destruct (var_dec y i); subst;
      try contradiction.
    rewrite M.gso; auto.
    rewrite M.gss; auto.
  - rewrite M.gso; auto.
    destruct (var_dec y i); subst.
    + repeat rewrite M.gss; auto.
    + repeat (rewrite M.gso; auto).
Qed.

Lemma set_set_eq {A} x {v : A} {u : A} {ρ} :
  M.set x v (M.set x u ρ) = M.set x v ρ.
Proof.
  apply M.extensionality.
  intros.
  destruct (var_dec x i); subst.
  - repeat rewrite M.gss; auto.
  - repeat (rewrite M.gso; auto).
Qed.

Lemma set_lists_set {A} :
  forall {xs vs} x v {ρ1 ρ2},
    ~ In x xs ->
    @set_lists A xs vs ρ1 = Some ρ2 ->
    set_lists xs vs (M.set x v ρ1) = Some (M.set x v ρ2).
Proof.
  intro xs.
  induction xs; simpl; intros;
    destruct vs; try discriminate.
  - inv H0; auto.
  - destruct (set_lists xs vs ρ1) eqn:Heq1; try discriminate.
    inv H0.
    assert (~ In x xs) by (intros Hc; apply H; right; auto).
    assert (a <> x) by (intros Hc; apply H; left; auto).
    erewrite IHxs; eauto.
    f_equal.
    eapply set_set; eauto.
Qed.

Lemma set_lists_set_inv {A} :
  forall {xs vs x v ρ1 ρ2},
    @set_lists A xs vs (M.set x v ρ1) = Some ρ2 ->
    ~ In x xs ->
    exists ρ3,
      @set_lists A xs vs ρ1 = Some ρ3 /\
      ρ2 = (M.set x v ρ3).
Proof.
  intros xs.
  induction xs; simpl; intros.
  - destruct vs; try discriminate.
    inv H.
    eexists; split; eauto.
  - destruct vs; try discriminate.
    destruct (set_lists xs vs (M.set x v ρ1)) eqn:Heq; try discriminate.
    inv H.
    edestruct IHxs as [ρ3 [Heqr3 Heqr2]]; eauto; subst.
    rewrite Heqr3.
    eexists; split; eauto.
    rewrite set_set; auto.
Qed.

Lemma FromList_cons_assoc {A} {x : A} l Γ:
  FromList (x :: l) :|: Γ \subset x |: (FromList l :|: Γ).
Proof.
  unfold Ensembles.Included, Ensembles.In, FromList.
  intros.
  inv H.
  + inv H0.
    apply Union_introl; auto.
    apply Union_intror; auto.
  + apply Union_intror.
    apply Union_intror; auto.
Qed.

Lemma NoDup_list_norepet:
  forall {A} (l:list A), NoDup l <-> Coqlib.list_norepet l.
Proof.
  intros.
  induction l; split; intro; auto.
  constructor. constructor.
  inv H; constructor; eauto.
  apply  IHl. auto.
  inv H; constructor; auto.
  apply IHl. auto.
Qed.

Lemma keys_NoDup {A} (m : M.t A) :
  NoDup (List.map fst (M.elements m)).
Proof.
  apply NoDup_list_norepet.
  apply M.elements_keys_norepet.
Qed.

Lemma Setminus_Included_Union_l {A} {s1 : Ensemble A} {s2 s3} :
  Decidable s2 ->
  s1 \\ s2 \subset s3 ->
  s1 \subset (s2 :|: s3).
Proof.
  intros.
  unfold Ensembles.Included, Ensembles.In, Ensembles.Setminus in *.
  intros.
  inv X.
  destruct (Dec x).
  - apply Union_introl; auto.
  - apply Union_intror.
    eapply H; eauto.
Qed.

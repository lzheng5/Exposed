From Coq Require Import Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.Libraries Require Import maps_util.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

Lemma normalize_step : forall i j, j <= i -> i - (i - j) = j.
Proof. intros; lia. Qed.

Lemma Forall2_map_r_iff : forall {A B} {P} {f : A -> B} (l1 l2 : list A),
    Forall2 P l1 (map f l2) <-> Forall2 (fun x1 x2 => P x1 (f x2)) l1 l2.
Proof.
  intros.
  revert l2.
  induction l1; intros; split; intro H; inv H.
  - destruct l2; simpl in *; inv H0.
    constructor.
  - constructor.
  - destruct l2; simpl in *; inv H2.
    constructor; auto.
    eapply IHl1; eauto.
  - constructor; auto.
    eapply IHl1; eauto.
Qed.


Lemma map_nth_error_inj
     : forall (A B : Type) (f : A -> B) (n : nat) (l : list A) (d : A),
       (forall a b, f a = f b -> a = b) ->
       nth_error l n = Some d <-> nth_error (map f l) n = Some (f d).
Proof.
intros.
revert n.
induction l; intros.
- split; intros;
  apply nth_error_In in H0; inv H0.
- split; intros;
    destruct n; simpl in *; inversion H0; auto.
  apply IHl; auto.
  f_equal; apply H; auto.
  apply IHl; auto.
Qed.

Lemma nth_error_map' :
  forall (A B : Type) (f : A -> B) (n : nat) (l : list A) (d : B),
    nth_error (map f l) n = Some d -> exists d', d = f d'.
Proof.
  intros; revert n H.
  induction l; intros.
  - apply nth_error_In in H.
    inv H.
  - destruct n; simpl in *; inversion H.
    eexists; eauto.
    eapply IHl; eauto.
Qed.

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
    P v.
Proof.
  intros.
  revert i v H.
  induction H0; simpl; intros.
  - apply nth_error_In in H.
    inv H.
  - destruct i; simpl in *; eauto.
    inv H1; auto.
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

Lemma set_set {A} {x y} {v : A} {u : A} {ρ} :
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

(*
Lemma set_set_eq {A} {x} {v : A} {u : A} {ρ} :
  M.set x v (M.set x u ρ) = M.set x v ρ.
Proof.
  apply M.extensionality.
  intros.
  destruct (var_dec x i); subst.
  - repeat rewrite M.gss; auto.
  - repeat (rewrite M.gso; auto).
Qed.
*)

Lemma set_lists_set {A} :
  forall {xs vs x v ρ1 ρ2},
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

Lemma Forall_fold {A} {P} {l : list A} :
  fold_right (fun x acc => P x /\ acc) True l <-> Forall P l.
Proof.
  induction l; simpl; split; auto; intros.
  - destruct H; constructor; auto.
    rewrite <- IHl; auto.
  - inv H.
    split; auto.
    rewrite IHl; auto.
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


Section All2.
    Context (A : Type) (B : Type) (R : A -> B -> Prop).

    (* A Fixpoint version of List.Forall2 *)
    Fixpoint all2 l1 l2 : Prop :=
      match l1, l2 with
      | [], [] => True
      | [] , _::_ => False
      | _::_, [] => False
      | a::l1', b::l2' => R a b /\ all2 l1' l2'
      end.

    Lemma all2_Forall2 l1 l2 : all2 l1 l2 <-> Forall2 R l1 l2.
    Proof.
      revert l2.
      induction l1; simpl in *.
      - destruct l2; split; intros; auto; try tauto.
        inv H.
      - destruct l2; split; intros; auto; try tauto.
        inv H.
        destruct H.
        constructor; auto.
        apply IHl1; auto.
        inv H.
        split; auto.
        apply IHl1; auto.
    Qed.
End All2.


Section TreeForall.
Context {A : Type}
        {P : A -> Prop}.

Inductive tree_Forall' : (M.tree' A) -> Prop :=
| Forall_Node001 : forall r, tree_Forall' r -> tree_Forall' (M.Node001 r)
| Forall_Node010 : forall x, P x -> tree_Forall' (M.Node010 x)
| Forall_Node011 : forall x r, P x -> tree_Forall' r -> tree_Forall' (M.Node011 x r)
| Forall_Node100 : forall l, tree_Forall' l -> tree_Forall' (M.Node100 l)
| Forall_Node101 : forall l r, tree_Forall' l -> tree_Forall' r -> tree_Forall' (M.Node101 l r)
| Forall_Node110 : forall l x, tree_Forall' l -> P x -> tree_Forall' (M.Node110 l x)
| Forall_Node111 : forall l x r, tree_Forall' l -> P x -> tree_Forall' r -> tree_Forall' (M.Node111 l x r).

Hint Constructors tree_Forall' : core.

Inductive tree_Forall : (M.tree A) -> Prop :=
| Forall_Empty : tree_Forall M.Empty
| Forall_Nodes : forall m', tree_Forall' m' -> tree_Forall (M.Nodes m').

Hint Constructors tree_Forall : core.

Lemma tree_Forall_prop : forall m, tree_Forall m -> (forall x v, m ! x = Some v -> P v).
Proof.
  intros m H x v.
  induction H; intros.
  - rewrite M.gempty in *.
    inversion H.
  - unfold M.get in *.
    revert x v H0.
    induction H; intros y v; intros; simpl in *; destruct y; simpl in *; eauto;
      match goal with
      | [H : None = Some _ |- _] => inversion H
      | [H : Some _ = None |- _] => inversion H
      | [H : Some _ = Some _ |- _] => inversion H; subst; auto
      end.
Qed.

End TreeForall.

Lemma map'_ignore : forall {A B} {f : A -> B} {t i j},
    M.map' (fun _ v => f v) t i = M.map' (fun _ v => f v) t j.
Proof.
  induction t; simpl; intros; f_equal; try eapply IHt; try eapply IHt1; try eapply IHt2.
Qed.


Lemma get_list_M_set_Disjoint : forall {A : Type} xs x {v : A} (ρ : M.t A),
    (~ In x xs) ->
    get_list xs (M.set x v ρ) = get_list xs ρ.
Proof.
  induction xs; intros; simpl in *; auto.
  rewrite M.gso in *; auto.
  destruct (ρ ! a); auto.
  erewrite IHxs; auto.
Qed.

Lemma M_get_set_eq : forall {A : Type} x (v : A) (ρ : M.t A),
    ρ ! x = Some v -> M.set x v ρ = ρ.
Proof.
  intros.
  eapply M.extensionality.
  intro.
  destruct (var_dec x i); subst.
  - rewrite M.gss; auto.
  - rewrite M.gso; auto.
Qed.

Lemma bool_dec : forall b, b = true \/ b = false.
Proof.
  intros; destruct b; auto.
Qed.

Lemma In_dec : forall {A : Type} {xs : list A} {x : A}, (forall x y : A, {x = y} + {x <> y}) -> (In x xs \/ ~ In x xs).
Proof.
  intros A xs x A_dec; revert x.
  induction xs; intros; simpl in *; try tauto.
  destruct (A_dec x a); subst.
  - eapply or_introl; auto.
  - destruct (IHxs x).
    + eapply or_introl.
      eapply or_intror; auto.
    + eapply or_intror.
      intro; apply H.
      destruct H0; subst; try tauto.
Qed.

Lemma set_lists_length_2:
  forall {A : Type} {xs1 xs2 : list map_util.M.elt} {rho1 rho1' rho2 : map_util.M.t A} {vs1 vs2 : list A},
  set_lists xs1 vs1 rho1 = Some rho1' ->
  length xs1 = length xs2 ->
  length vs1 = length vs2 ->
  exists rho2' : map_util.M.t A, set_lists xs2 vs2 rho2 = Some rho2'.
Proof.
  induction xs1; intros; destruct xs2; simpl in *; try lia.
  - destruct vs1; destruct vs2; simpl in *; try lia.
    eexists; eauto.
    inv H.
  - destruct vs1; destruct vs2; simpl in *; try lia.
    inv H.
    destruct (set_lists xs1 vs1 rho1) eqn:H2; inv H.
    edestruct IHxs1 with (xs2 := xs2) (vs1 := vs1) (vs2 := vs2) (rho2 := rho2); eauto.
    eexists.
    rewrite H; eauto.
Qed.

Lemma not_Dom_map_eq {A} (sig:M.t A) x :
  M.get x sig = None <-> ~ Dom_map sig x.
Proof.
  split.
  - unfold Dom_map.
    intro. intro Hc.
    inv Hc.
    rewrite H0 in H; inv H.
  - eapply map_util.not_Dom_map_eq; eauto.
Qed.

Lemma Dom_map_eq {A} (sig:M.t A) x :
  (exists y, M.get x sig = Some y) <-> Dom_map sig x.
Proof.
  unfold Dom_map.
  split; intros [y Hy]; eauto.
Qed.

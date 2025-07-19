From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

Require Import UntypedExposed.ANF.

(* Logical Relations *)
Definition R' (V' : nat -> val -> Prop) (i : nat) (r : res) :=
  match r with
  | OOT => True
  | Res v => V' i v
  end.

Definition E' (V' : nat -> val -> Prop) (ex : bool) (i : nat) (ρ : env) (e : exp) : Prop :=
  forall j r,
    j <= i ->
    bstep_fuel ex ρ e j r ->
    R' V' (i - j) r.

Fixpoint V (i : nat) (v : val) {struct i} : Prop :=
  match i with
  | 0 => True
  | S i' =>
      let fix V' (v : val) : Prop :=
        match v with
        | Vprim p => True
        | Vfun f ρ w xs e =>
            forall j vs ρ',
              j <= i' ->
              (w \in Exposed -> Forall exposed vs) ->
              Forall (V (i' - (i' - j))) vs ->
              set_lists xs vs (M.set f (Vfun f ρ w xs e) ρ) = Some ρ' ->
              E' V (exposedb w) (i' - (i' - j)) ρ' e
        end
      in V' v
  end.

Notation R := (R' V).

Notation E := (E' V).

(* Environment Relation *)
Definition G i ρ :=
  forall x v,
    M.get x ρ = Some v ->
    V i v.

Definition related e :=
  forall ex i ρ,
    G i ρ ->
    E ex i ρ e.

(* Environment Lemmas *)
Lemma G_set {i ρ}:
  G i ρ ->
  forall {x v},
    V i v ->
    G i (M.set x v ρ).
Proof.
  unfold G.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - rewrite M.gss in *.
    inv H1; eauto.
  - rewrite M.gso in *; auto.
    eapply H; eauto.
Qed.

Lemma G_set_lists {i ρ}:
  G i ρ ->
  forall {xs vs ρ'},
    Forall (V i) vs ->
    set_lists xs vs ρ = Some ρ' ->
    G i ρ'.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct vs; try discriminate.
    inv H0.
    eapply HG; eauto.
  - destruct vs; try discriminate.
    destruct (set_lists xs vs ρ) eqn:Heq2; try discriminate.
    inv H; inv H0.
    destruct (M.elt_eq x a); subst.
    + rewrite M.gss in *; eauto.
      inv H1; auto.
    + rewrite M.gso in *; auto.
      eapply IHxs; eauto.
Qed.

Lemma G_get_list {i ρ} :
  G i ρ ->
  forall {xs vs},
    get_list xs ρ = Some vs ->
    Forall (V i) vs.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - inv H; auto.
  - destruct (ρ ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ) eqn:Heq2; try discriminate.
    inv H; constructor; eauto.
Qed.

(* Monotonicity Lemmas *)
Lemma V_mono {v} i j:
  V i v ->
  j <= i ->
  V j v.
Proof.
  intros.
  generalize dependent v.
  induction H0; simpl; intros; auto.
  apply IHle.
  destruct m.
  - unfold V. auto.
  - destruct v; auto.
    simpl.
    intros.
    assert (j0 <= S m). lia.
    assert ((m - (m - j0)) = (S m - (S m - j0))). lia.
    rewrite H6 in H3.
    rewrite H6.
    apply (H j0 vs ρ'); auto.
Qed.

Lemma ForallV_mono {vs} i j :
  Forall (V i) vs ->
  j <= i ->
  Forall (V j) vs.
Proof.
  intros H.
  revert j.
  induction H; simpl; intros; auto.
  constructor; eauto.
  eapply V_mono; eauto.
Qed.

Lemma R_mono {r} i j :
  R i r ->
  j <= i ->
  R j r.
Proof.
  unfold R.
  intros.
  destruct r; auto.
  eapply V_mono; eauto.
Qed.

Lemma E_mono {ex ρ e} i j:
  E ex i ρ e ->
  j <= i ->
  E ex j ρ e.
Proof.
  unfold E.
  intros.
  apply R_mono with (i - j0); try lia.
  apply (H j0 r); auto; try lia.
Qed.

Lemma G_mono {ρ} i j:
  G i ρ ->
  j <= i ->
  G j ρ.
Proof.
  unfold G.
  intros.
  apply V_mono with i; eauto.
Qed.

(* Compatibility Lemmas *)
Lemma ret_compat x :
  related (Eret x).
Proof.
  unfold related, G, E, R.
  intros.
  destruct r; auto.
  inv H1.
  inv H2.
  apply V_mono with i; try lia.
  eapply H; eauto.
Qed.

Lemma prim_val_compat {k} x p :
  related k ->
  related (Eprim_val x p k).
Proof.
  unfold related.
  intros.

  assert (HE : E ex i (M.set x (Vprim p) ρ) k).
  {
    apply H.
    apply G_set; auto.
    destruct i; simpl; auto.
  }

  unfold E in *.
  intros.
  inv H2.
  - eapply HE; eauto.
  - inv H3.
    apply R_mono with (i - c); try lia.
    eapply HE; eauto; lia.
Qed.

Lemma Vfun_V {e} :
  related e ->
  forall {i ρ} f w xs,
    G i ρ ->
    V i (Vfun f ρ w xs e).
Proof.
  unfold related.
  intros He i.
  induction i; simpl; intros; auto.
  apply (He (exposedb w) (i - (i - j)) ρ').
  eapply G_set_lists; eauto.
  apply G_set; auto.
  - apply G_mono with (S i); auto; lia.
  - apply V_mono with i; try lia.
    apply IHi; auto.
    apply G_mono with (S i); auto; lia.
Qed.

Lemma fun_compat {e k} f w xs :
  related e ->
  related k ->
  related (Efun f w xs e k).
Proof.
  unfold related, E.
  intros.
  inv H3.
  - simpl; auto.
  - inv H4.
    apply R_mono with ((i - 1) - c); try lia.
    eapply (H0 ex (i - 1) (M.set f (Vfun f ρ w xs e) ρ)); eauto; try lia.
    apply G_set.
    + apply G_mono with i; auto; lia.
    + eapply Vfun_V; eauto.
      apply G_mono with i; auto; lia.
Qed.

Lemma app_compat f w xs :
  related (Eapp f w xs).
Proof.
  unfold related, G, E.
  intros.
  inv H1; simpl; auto.
  inv H2.
  apply H in H6.
  unfold R.
  destruct r; auto.
  destruct i; simpl; auto.
  simpl in H6.

  assert (HE : E (exposedb w) i ρ'' e).
  {
    apply E_mono with (i - (i - i)); try lia.
    eapply (H6 i vs); eauto.
    - intros.
      destruct H13; auto.
    - apply ForallV_mono with (S i).
      eapply G_get_list; eauto.
      lia.
  }

  unfold E in HE.
  specialize (HE c (Res v)).
  simpl in HE.
  apply HE; auto; try lia.
Qed.

Lemma letapp_compat {k} x f w xs :
  related k ->
  related (Eletapp x f w xs k).
Proof.
  (* direct proof *)
  unfold related, G, E.
  intros.
  inv H2; simpl; auto.
  inv H3; simpl; auto.
  apply H0 in H9.
  apply R_mono with ((i - (S c0)) - c'); try lia.
  eapply (H ex (i - (S c0)) (M.set x v ρ)); eauto; try lia.
  apply G_set.
  eapply G_mono; eauto; try lia.
  destruct i; simpl in *; auto.
  assert (HE : E (exposedb w) i ρ'' e).
  {
    apply E_mono with (i - (i - i)); try lia.
    eapply (H9 i vs); eauto.
    - intros.
      destruct H16; auto.
    - apply ForallV_mono with (S i).
      eapply G_get_list; eauto.
      lia.
  }
  unfold E in HE.
  specialize (HE c0 (Res v)).
  simpl in HE.
  apply HE; auto; try lia.
Qed.

Lemma letapp_compat' {k} x f w xs :
  related k ->
  related (Eletapp x f w xs k).
Proof.
  (* alternative proof using app_compat *)
  intros.
  specialize (app_compat f w xs); intros Ha.
  unfold related, E in *.
  intros.
  specialize (Ha (exposedb w) _ _ H0).
  (* the result of this *aritificial* app is governed by (w \in Exposed) not ex *)
  inv H2; auto.
  inv H3; simpl; auto.
  apply R_mono with ((i - (S c0)) - c'); try lia.
  eapply (H ex (i - (S c0)) (M.set x v ρ)); eauto; try lia.
  apply G_set.
  apply G_mono with i; try lia; auto.
  apply (Ha (S c0) (Res v)); auto; try lia.
  constructor.
  eapply BStep_app; eauto; intros.
  - destruct H16; auto.
  - destruct (exposed_reflect w); auto.
    destruct H16; auto.
Qed.

Lemma if_compat {e t} x:
  related t ->
  related e ->
  related (Eif x t e).
Proof.
  unfold related, G, E.
  intros Ht He. intros.
  inv H1; simpl; auto.
  inv H2.
  - apply R_mono with (i - c); try lia.
    eapply Ht; try lia; eauto.
  - apply R_mono with (i - c); try lia.
    eapply He; try lia; eauto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {e} :
  related e.
Proof.
  induction e.
  - apply ret_compat.
  - apply app_compat.
  - apply letapp_compat; auto.
  - apply fun_compat; auto.
  - apply prim_val_compat; auto.
  - apply if_compat; auto.
Qed.

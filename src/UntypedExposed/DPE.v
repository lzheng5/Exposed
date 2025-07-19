From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

Require Import UntypedExposed.ANF.
Require Import UntypedExposed.Refl.

(* Map from web identifier to the live parameter list *)
Definition live_map : Type := M.t (list bool).

(* Apply bit mask to argument list *)
Fixpoint live_args {A} (ys : list A) (bs : list bool) : list A :=
  match bs, ys with
  | [], [] => ys
  | b :: bs', y :: ys' =>
    if b then y :: (live_args ys' bs')
    else live_args ys' bs'
  | _, _ => ys
  end.

Fixpoint dead_args {A} (ys : list A) (bs : list bool) : list A :=
  match bs, ys with
  | [], [] => ys
  | b :: bs', y :: ys' =>
    if b then (dead_args ys' bs')
    else y :: dead_args ys' bs'
  | _, _ => ys
  end.

(* DPE Specification *)
Parameter L : live_map.

Definition live_map_inv := forall w, w \in Exposed -> L ! w = None.

Hint Unfold live_map_inv : core.

Inductive trans (Γ : Ensemble var) : exp -> exp -> Prop :=
| Trans_ret :
  forall {x},
    trans Γ (Eret x) (Eret x)

| Trans_fun :
  forall {f w xs e k bs e' k'},
    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->

    M.get w L = Some bs ->
    ~ (w \in Exposed) ->
    length xs = length bs ->

    NoDup (f :: xs) ->
    Disjoint _ (FromList (f :: xs)) Γ ->
    Disjoint _ (FromList (dead_args xs bs)) (occurs_free e') ->
    trans Γ (Efun f w xs e k) (Efun f w (live_args xs bs) e' k')

| Trans_fun_exposed :
  forall {f w xs e k e' k'},
    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->
    M.get w L = None ->
    trans Γ (Efun f w xs e k) (Efun f w xs e' k')

| Trans_app :
  forall {f w xs bs},
    M.get w L = Some bs ->
    ~ (w \in Exposed) ->
    length xs = length bs ->
    trans Γ (Eapp f w xs) (Eapp f w (live_args xs bs))

| Trans_app_exposed :
  forall {f w xs},
    M.get w L = None ->
    trans Γ (Eapp f w xs) (Eapp f w xs)

| Trans_letapp :
  forall {x f w xs k bs k'},
    trans (x |: Γ) k k' ->
    M.get w L = Some bs ->
    ~ (w \in Exposed) ->
    length xs = length bs ->
    trans Γ (Eletapp x f w xs k) (Eletapp x f w (live_args xs bs) k')

| Trans_letapp_exposed :
  forall {x f w xs k k'},
    trans (x |: Γ) k k' ->
    M.get w L = None ->
    trans Γ (Eletapp x f w xs k) (Eletapp x f w xs k')

| Trans_prim_val :
  forall {x p k k'},
    trans (x |: Γ) k k' ->
    trans Γ (Eprim_val x p k) (Eprim_val x p k')

| Trans_if :
  forall {x t e t' e'},
    trans Γ t t' ->
    trans Γ e e' ->
    trans Γ (Eif x t e) (Eif x t' e').

Hint Constructors trans : core.

(* Logical Relations *)
Definition R' (P : nat -> val -> val -> Prop) (i : nat) (r1 : res) (r2 : res) :=
  match r1, r2 with
  | OOT, OOT => True
  | Res v1, Res v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> val -> val -> Prop) (ex : bool) (i : nat) (ρ1 : env) (e1 : exp) (ρ2 : env) (e2 : exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    bstep_fuel ex ρ1 e1 j1 r1 ->
    exists j2 r2,
      bstep_fuel ex ρ2 e2 j2 r2 /\
      R' P (i - j1) r1 r2.

Fixpoint V (i : nat) (v1 : val) (v2 : val) {struct i} : Prop :=
  match v1, v2 with
  | Vprim p1, Vprim p2 => p1 = p2
  | Vfun f1 ρ1 w1 xs1 e1, Vfun f2 ρ2 w2 xs2 e2 =>
      w1 = w2 /\ (* web stay the same *)
      match i with
      | 0 => True
      | S i0 =>
          match M.get w1 L with
          | None => (* reflexively related *)
              length xs1 = length xs2 /\
              forall j vs1 vs2 ρ3 ρ4,
                j <= i0 ->
                (w1 \in Exposed -> Forall exposed vs1 /\ Forall exposed vs2) -> (* web can be either exposed or non-exposed *)
                Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                set_lists xs1 vs1 (M.set f1 (Vfun f1 ρ1 w1 xs1 e1) ρ1) = Some ρ3 ->
                set_lists xs2 vs2 (M.set f2 (Vfun f2 ρ2 w2 xs2 e2) ρ2) = Some ρ4 ->
                E' V (exposedb w1) (i0 - (i0 - j)) ρ3 e1 ρ4 e2

          | Some bs => (* non-reflexively related *)
              length xs1 = length bs /\
              xs2 = live_args xs1 bs /\
              ~ (w1 \in Exposed) /\ (* web has to be non-exposed *)
              forall j vs1 vs2 ρ3 ρ4,
                j <= i0 ->
                Forall2 (V (i0 - (i0 - j))) (live_args vs1 bs) vs2 -> (* only live inputs matter *)
                set_lists xs1 vs1 (M.set f1 (Vfun f1 ρ1 w1 xs1 e1) ρ1) = Some ρ3 ->
                set_lists xs2 vs2 (M.set f2 (Vfun f2 ρ2 w2 xs2 e2) ρ2) = Some ρ4 ->
                E' V (exposedb w1) (i0 - (i0 - j)) ρ3 e1 ρ4 e2
          end
      end
  | _, _ => False
  end.

Notation R := (R' V).

Notation E := (E' V).

(* Environment Relation *)
Definition G i Γ1 ρ1 Γ2 ρ2 :=
  forall x,
    x \in Γ1 ->
    exists v1,
      M.get x ρ1 = Some v1 /\
      (x \in Γ2 ->
        exists v2,
          M.get x ρ2 = Some v2 /\
          V i v1 v2).

Definition trans_correct Γ e1 e2 :=
  forall ex i ρ1 ρ2,
    (occurs_free e1) \subset Γ ->
    (occurs_free e2) \subset Γ ->
    G i Γ ρ1 (occurs_free e2) ρ2 ->
    E ex i ρ1 e1 ρ2 e2.

(* Monotonicity Lemmas *)
Lemma V_mono {v1 v2} i j:
  V i v1 v2 ->
  j <= i ->
  V j v1 v2.
Proof.
  intros.
  generalize dependent v1.
  generalize dependent v2.
  induction H0; simpl; intros; auto.
  apply IHle.
  destruct v1.
  - destruct v2; try contradiction.
    destruct (L ! w) eqn:Hw.
    + destruct H as [Heqw [Hlen [Hl0 [Hexp Hfv]]]]; subst.
      destruct m; simpl; auto; try contradiction.
      rewrite Hw.
      repeat split; auto.
      intros.
      assert (Hj0 : m - (m - j0) = (S m - (S m - j0))) by lia.
      rewrite Hj0 in *.
      eapply Hfv; eauto.
    + destruct H as [Heqw [Hlen Hfv]]; subst.
      destruct m; simpl; auto; try contradiction.
      rewrite Hw.
      repeat split; auto.
      intros.
      assert (Hj0 : m - (m - j0) = (S m - (S m - j0))) by lia.
      rewrite Hj0 in *.
      eapply Hfv; eauto.
  - destruct v2; try contradiction.
    subst.
    destruct m; simpl; eauto.
Qed.

Lemma ForallV_mono {vs1 vs2} i j :
  Forall2 (V i) vs1 vs2 ->
  j <= i ->
  Forall2 (V j) vs1 vs2.
Proof.
  intros H.
  revert j.
  induction H; simpl; intros; auto.
  constructor; eauto.
  eapply V_mono; eauto.
Qed.

Lemma R_mono {r1 r2} i j :
  R i r1 r2 ->
  j <= i ->
  R j r1 r2.
Proof.
  unfold R.
  intros.
  destruct r1; auto.
  destruct r2; auto.
  eapply V_mono; eauto.
Qed.

Lemma E_mono {ex ρ1 ρ2 e1 e2} i j:
  E ex i ρ1 ρ2 e1 e2 ->
  j <= i ->
  E ex j ρ1 ρ2 e1 e2.
Proof.
  unfold E.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; auto.
  apply R_mono with (i - j1); try lia; auto.
Qed.

Lemma G_mono {Γ1 Γ2 ρ1 ρ2} i j:
  G i Γ1 ρ1 Γ2 ρ2 ->
  j <= i ->
  G j Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G.
  intros.
  edestruct H as [v1 [Heqv1 Hv2]]; eauto.
  eexists; eexists; repeat split; eauto.
  intros.
  destruct Hv2 as [v2 [Heqv2 HV]]; eauto.
  eexists; split; eauto.
  apply V_mono with i; eauto.
Qed.

(* Exposed Lemmas *)
Lemma V_exposed : forall {i v1 v2},
  V i v1 v2 ->
  exposed v1 ->
  exposed v2.
Proof.
  intros.
  destruct v1; destruct v2;
    destruct i; try contradiction; auto;
    destruct H as [Heq1 _]; subst;
    inv H0; auto.
Qed.

Lemma V_exposed_Forall : forall {i vs1 vs2},
  Forall2 (V i) vs1 vs2 ->
  Forall exposed vs1 ->
  Forall exposed vs2.
Proof.
  intros.
  induction H; intros; auto.
  inv H0.
  constructor; auto.
  eapply V_exposed; eauto.
Qed.

Lemma V_exposed_res : forall {i v1 v2},
  V i v1 v2 ->
  exposed_res (Res v1) ->
  exposed_res (Res v2).
Proof.
  intros.
  inv H0.
  constructor.
  eapply V_exposed; eauto.
Qed.

Lemma R_exposed : forall {i r1 r2},
  R i r1 r2 ->
  exposed_res r1 ->
  exposed_res r2.
Proof.
  unfold R.
  intros.
  destruct r1;
    destruct r2;
    try contradiction; auto.
  eapply V_exposed_res; eauto.
Qed.

(* Lemmas about [live_args] and [dead_args] *)
Lemma live_args_incl {A xs bs} :
  incl (@live_args A xs bs) xs.
Proof.
  revert bs.
  induction xs; intros.
  - destruct bs; simpl; apply incl_nil_l.
  - destruct bs; simpl.
    + apply incl_refl.
    + destruct b.
      * apply incl_cons.
        apply in_eq; auto.
        apply incl_tl; auto.
      * apply incl_tl; auto.
Qed.

Lemma live_args_In : forall {A xs bs a}, In a (@live_args A xs bs) -> In a xs.
Proof.
  intros; eapply live_args_incl; eauto.
Qed.

Lemma live_args_not_In : forall {A xs a} bs, ~ In a xs -> ~ In a (@live_args A xs bs).
Proof.
  intros.
  intro Hc.
  apply H.
  eapply live_args_In; eauto.
Qed.

Lemma live_args_length {A B} xs ys bs :
  length xs = length ys ->
  length (@live_args A xs bs) = length (@live_args B ys bs).
Proof.
  revert ys bs. induction xs; intros; eauto.
  - destruct ys; try (simpl in * ; congruence).
    destruct bs; reflexivity.
  - simpl.
    destruct ys; try (simpl in * ; congruence). inv H.
    destruct bs. simpl. congruence.
    destruct b0; simpl; eauto.
Qed.

Lemma dead_args_incl {A xs bs} :
  incl (@dead_args A xs bs) xs.
Proof.
  revert bs.
  induction xs; intros.
  - destruct bs; simpl; apply incl_nil_l.
  - destruct bs; simpl.
    + apply incl_refl.
    + destruct b.
      * apply incl_tl; auto.
      * apply incl_cons.
        apply in_eq; auto.
        apply incl_tl; auto.
Qed.

Lemma dead_args_In : forall {A xs bs a}, In a (@dead_args A xs bs) -> In a xs.
Proof. intros; eapply dead_args_incl; eauto. Qed.

Lemma dead_args_not_In : forall {A xs a} bs, ~ In a xs -> ~ In a (@dead_args A xs bs).
Proof.
  intros.
  intro Hc.
  apply H.
  eapply dead_args_In; eauto.
Qed.

Lemma not_live_dead_args {A} : forall {xs bs x},
    length xs = length bs ->
    ~ In x (@live_args A xs bs) ->
    In x xs ->
    In x (@dead_args A xs bs).
Proof.
  intros xs.
  induction xs; simpl; intros.
  - contradiction.
  - destruct bs; inv H.
    destruct b.
    + inv H1.
      * exfalso.
        apply H0; apply in_eq.
      * apply IHxs; auto.
        intro Hc.
        apply H0; apply in_cons; auto.
    + inv H1.
      * apply in_eq.
      * apply in_cons; apply IHxs; auto.
Qed.

(* Invariants of [trans] *)
Lemma free_trans_inv {Γ e e'} :
  trans Γ e e' ->
  (occurs_free e') \subset (occurs_free e).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros H.
  induction H; intros; auto.
  - inv H7; auto.
    destruct (in_dec M.elt_eq x xs); auto.
    apply not_live_dead_args in H15; auto.
    exfalso.
    inv H6.
    apply (H7 x); auto.
  - inv H2; auto.
  - inv H2; auto.
    apply live_args_In in H7; auto.
  - inv H3; auto.
    apply live_args_In in H10; auto.
  - inv H1; auto.
  - inv H0; auto.
  - inv H1; auto.
Qed.

(* Environment Lemmas *)
Lemma G_set {i Γ1 ρ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall {x v1 v2},
    V i v1 v2 ->
    G i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
Proof.
  unfold G.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss in *.
    eexists; split; eauto; intros.
  - rewrite M.gso in *; auto.
    rewrite M.gso in *; auto.
    inv H1.
    + inv H2; contradiction.
    + edestruct H as [v1' [Heqv1' Hv2]]; eauto.
      eexists; split; eauto.
      intros.
      apply Hv2.
      inv H1; auto.
      inv H3.
      contradiction.
Qed.

Lemma G_subset Γ1 Γ2 {i ρ1 Γ3 ρ2 Γ4}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  Γ3 \subset Γ1 ->
  Γ4 \subset Γ2 ->
  G i Γ3 ρ1 Γ4 ρ2.
Proof.
  unfold G.
  intros.
  unfold Ensembles.Included in *.
  edestruct H as [v1 [Heqv1 Hv2]]; eauto.
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

Lemma G_set_lists_refl {i Γ1 ρ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 (V i) vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    G i (FromList xs :|: Γ1) ρ3 (FromList xs :|: Γ2) ρ4.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    inv H0; inv H1.
    edestruct HG as [v1 [Heqv1 Hv2]]; eauto.
    inv H2; eauto.
    inv H0.
    eexists; split; eauto; intros.
    inv H0.
    inv H1.
    apply Hv2; auto.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
    inv H; inv H0; inv H1.
    destruct (M.elt_eq x a); subst.
    + repeat rewrite M.gss in *; eauto.
    + rewrite M.gso in *; auto.
      rewrite M.gso in *; auto.
      edestruct IHxs as [v1 [Heqv1 Hv2]]; eauto.
      inv H2.
      inv H; try contradiction.
      apply Union_introl; eauto.
      apply Union_intror; auto.
      eexists; split; eauto; intros.
      apply Hv2.
      inv H.
      inv H0; try contradiction.
      apply Union_introl; auto.
      apply Union_intror; auto.
Qed.

Lemma G_set_lists {i Γ1 ρ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  Γ2 \subset Γ1 ->
  forall {xs vs1 vs2 ρ3 ρ4 bs},
    length xs = length bs ->
    Forall2 (V i) (live_args vs1 bs) vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists (live_args xs bs) vs2 ρ2 = Some ρ4 ->
    NoDup xs ->
    Disjoint _ (FromList xs) Γ1 ->
    G i (FromList xs :|: Γ1) ρ3 (FromList (live_args xs bs) :|: Γ2) ρ4.
Proof.
  unfold G.
  intros HG HS xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct bs; try discriminate.
    simpl in *.
    destruct vs2; try discriminate.
    inv H0; inv H1; inv H2; inv H3.
    edestruct HG as [v1 [Heqv1 Hv2]]; eauto.
    inv H5; eauto.
    inv H0.
    eexists; split; eauto; intros.
    inv H0.
    inv H1.
    destruct Hv2 as [v2 [Heqv2 HV]]; auto.
    eexists; split; eauto.
  - destruct vs1; try discriminate.
    destruct bs; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    inv H; inv H1; inv H3.
    destruct b; simpl in *.
    + destruct vs2; try discriminate.
      destruct (set_lists (live_args xs bs) vs2 ρ2) eqn:Heq2; try discriminate.
      inv H2; inv H0.
      destruct (M.elt_eq x a); subst.
      * repeat rewrite M.gss in *; eauto.
      * rewrite M.gso in *; auto.
        rewrite M.gso in *; auto.
        edestruct IHxs as [v1 [Heqv1 Hv2]]; eauto.
        eapply Disjoint_FromList_cons_l; eauto.
        inv H5.
        inv H; try contradiction.
        apply Union_introl; eauto.
        apply Union_intror; eauto.
        eexists; split; eauto; intros.
        apply Hv2; auto.
        inv H.
        inv H0; try contradiction.
        apply Union_introl; auto.
        apply Union_intror; auto.
    + destruct (M.elt_eq x a); subst.
      * rewrite M.gss in *; eauto.
        eexists; split; eauto; intros.
        inv H4.
        exfalso.
        apply (H1 a); auto.
        inv H; unfold Ensembles.In, FromList in *.
        -- apply live_args_not_In with bs in H6.
           contradiction.
        -- constructor; auto.
           unfold Ensembles.In.
           apply in_eq.
      * rewrite M.gso in *; auto.
        edestruct IHxs as [v1 [Heqv1 Hv2]]; eauto.
        eapply Disjoint_FromList_cons_l; eauto.
        inv H5.
        -- inv H; try contradiction.
           apply Union_introl; auto.
        -- apply Union_intror; auto.
Qed.

Lemma G_get_list_refl {i Γ1 ρ1 Γ2 ρ2} :
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall xs vs1,
    (FromList xs) \subset Γ1 ->
    (FromList xs) \subset Γ2 ->
    get_list xs ρ1 = Some vs1 ->
    exists vs2,
      get_list xs ρ2 = Some vs2 /\
      Forall2 (V i) vs1 vs2.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - inv H1; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H1.
    unfold Ensembles.Included, Ensembles.In, FromList in *.
    edestruct HG as [v1 [Heqv1 Hv2]]; eauto.
    eapply (H a).
    apply in_eq.
    rewrite Heqv1 in Heq1; inv Heq1.
    destruct Hv2 as [v2 [Heqv2 HV]].
    apply H0.
    apply in_eq.
    edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
    + intros.
      apply H.
      apply in_cons; auto.
    + intros.
      apply H0.
      apply in_cons; auto.
    + rewrite Heqvs2.
      exists (v2 :: vs2); split; auto.
      rewrite Heqv2; auto.
Qed.

Lemma G_get_list {i Γ1 Γ2 ρ1 ρ2} :
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall xs bs vs1,
    (FromList xs) \subset Γ1 ->
    (FromList (live_args xs bs)) \subset Γ2 ->
    length xs = length bs ->
    get_list xs ρ1 = Some vs1 ->
    exists vs2,
      get_list (live_args xs bs) ρ2 = Some vs2 /\
      Forall2 (V i) (live_args vs1 bs) vs2.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - inv H2.
    destruct bs; simpl in *; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H2.
    destruct bs; inv H1.
    destruct b; simpl in *.
    + unfold Ensembles.Included, Ensembles.In, Dom_map, FromList in *.
      destruct (HG a) as [v1 [Heqv1 Hv2]].
      apply H; apply in_eq.
      destruct Hv2 as [v2 [Heqv2 HV]].
      apply H0; apply in_eq.
      rewrite Heqv2.
      rewrite Heqv1 in Heq1; inv Heq1.
      edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
      intros; apply H; apply in_cons; auto.
      intros; apply H0; apply in_cons; auto.
      exists (v2 :: vs2); split; auto.
      rewrite Heqvs2; auto.
    + edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
      unfold Ensembles.Included, Ensembles.In, FromList in *.
      intros.
      apply H; apply in_cons; auto.
Qed.

(* Compatibility Lemmas *)
Lemma ret_compat Γ x:
  trans_correct Γ (Eret x) (Eret x).
Proof.
  unfold trans_correct, G, E, Ensembles.Included, Ensembles.In, Dom_map.
  intros.
  inv H3.
  - exists 0, OOT; simpl; split; eauto.
  - inv H4.
    edestruct (H1 x) as [v1 [Heqv1 Hv2]]; eauto.
    destruct Hv2 as [v2 [Heqv2 HV]]; auto.
    rewrite Heqv1 in H7; inv H7.
    exists 1, (Res v2); split; auto.
    + constructor; auto.
      destruct ex; auto.
      eapply V_exposed_res; eauto.
    + unfold R.
      eapply V_mono with i; try lia; eauto.
Qed.

Lemma prim_val_compat {Γ x p k k'} :
  trans_correct (x |: Γ) k k' ->
  trans_correct Γ (Eprim_val x p k) (Eprim_val x p k').
Proof.
  unfold trans_correct, E.
  intros.
  inv H4.
  - exists 0, OOT; split; simpl; auto.
  - inv H5.
    edestruct (H ex i (M.set x (Vprim p) ρ1) (M.set x (Vprim p) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk' Rr]]]; eauto; try lia.
    + eapply free_prim_val_k_inv; eauto.
    + eapply free_prim_val_k_inv; eauto.
    + eapply G_subset.
      eapply G_set; eauto.
      * destruct i; simpl; eauto.
      * apply Included_refl.
      * apply free_prim_val_k_subset.
    + exists (S j2), r2; split; eauto.
      * constructor; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * apply R_mono with (i - c); try lia; auto.
Qed.

Lemma Vfun_V_refl {f xs Γ1 Γ2 e e'} :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  Γ2 \subset Γ1 ->
  forall {i ρ1 ρ2} w,
    L ! w = None ->
    G i Γ1 ρ1 Γ2 ρ2 ->
    occurs_free e \subset (FromList xs :|: (f |: Γ1)) ->
    occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
    V i (Vfun f ρ1 w xs e) (Vfun f ρ2 w xs e').
Proof.
  unfold trans_correct.
  intros He HS i.
  induction i; simpl; intros; auto.
  split; auto.
  destruct (L ! w) eqn:Hw; try discriminate.
  inv H.
  split; auto; intros.
  apply (He (exposedb w) (i - (i - j)) ρ3 ρ4); auto.
  - eapply Included_trans; eauto.
    apply Included_Union_compat.
    apply Included_refl.
    apply Included_Union_compat; auto.
    apply Included_refl.
  - eapply G_subset.
    eapply G_set_lists_refl; eauto.
    eapply G_set; eauto.
    + apply G_mono with (S i); eauto; lia.
    + apply V_mono with i; try lia.
      eapply IHi; auto.
      apply G_mono with (S i); eauto; lia.
    + apply Included_refl.
    + auto.
Qed.

Lemma fun_compat_refl {Γ e e' k k'} f w xs :
  trans_correct (FromList xs :|: (f |: Γ)) e e' ->
  trans_correct (f |: Γ) k k' ->
  M.get w L = None ->
  trans_correct Γ (Efun f w xs e k) (Efun f w xs e' k').
Proof.
  unfold trans_correct, E.
  intros.
  inv H6.
  - exists 0, OOT; split; simpl; eauto.
  - inv H7.
    edestruct (H0 ex (i - 1) (M.set f (Vfun f ρ1 w xs e) ρ1) (M.set f (Vfun f ρ2 w xs e') ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply free_fun_k_inv; eauto.
    + eapply free_fun_k_inv; eauto.
    + eapply G_subset with (Γ2 := (f |: occurs_free (Efun f w xs e' k'))).
      eapply G_set.
      * apply G_mono with i; eauto; lia.
      * eapply Vfun_V_refl; eauto.
        apply G_mono with i; eauto; lia.
        eapply free_fun_e_inv; eauto.
        eapply free_fun_e_inv; eauto.
        eapply Included_refl.
      * apply Included_refl.
      * apply free_fun_k_subset.
    + exists (S j2), r2; split; auto.
      * constructor; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma Vfun_V Γ2 {f xs Γ1 e e'} :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  Γ2 \subset Γ1 ->
  NoDup (f :: xs) ->
  Disjoint _ (FromList (f :: xs)) Γ1 ->
  forall {i ρ1 ρ2 bs} w,
    L ! w = Some bs ->
    length xs = length bs ->
    G i Γ1 ρ1 Γ2 ρ2 ->
    occurs_free e \subset (FromList xs :|: (f |: Γ1)) ->
    occurs_free e' \subset (FromList (live_args xs bs) :|: (f |: Γ2)) ->
    ~ (w \in Exposed) ->
    Disjoint _ (FromList (dead_args xs bs)) (occurs_free e') ->
    V i (Vfun f ρ1 w xs e) (Vfun f ρ2 w (live_args xs bs) e').
Proof.
  unfold trans_correct.
  intros He HS Hn Hd i.
  induction i; simpl; intros; auto.
  split; auto.
  destruct (L ! w) eqn:Hw; try discriminate.
  inv H. inv Hn.
  repeat split; auto; intros.
  apply (He (exposedb w) (i - (i - j)) ρ3 ρ4); auto.
  eapply Included_trans.
  eapply H3.
  apply Included_Union_compat; eauto.
  apply live_args_incl.
  apply Included_Union_compat; eauto.
  eapply Included_refl.
  eapply G_subset with (Γ2 := (FromList (live_args xs bs) :|: (f |: Γ2))); eauto.
  - eapply G_set_lists; eauto.
    + eapply G_set; eauto.
      apply G_mono with (S i); eauto; try lia.
      apply V_mono with i; try lia.
      apply IHi; auto.
      apply G_mono with (S i); auto; lia.
    + apply Included_Union_compat; auto.
      apply Included_refl.
    + apply Disjoint_FromList_cons_r; auto.
      eapply Disjoint_FromList_cons_l; eauto.
  - apply Included_refl.
Qed.

Lemma fun_compat {Γ1 e e' bs k k'} f w xs :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  trans_correct (f |: Γ1) k k' ->
  M.get w L = Some bs ->
  length xs = length bs ->
  NoDup (f :: xs) ->
  Disjoint _ (FromList (f :: xs)) Γ1 ->
  Disjoint _ (FromList (dead_args xs bs)) (occurs_free e') ->
  ~ (w \in Exposed) ->
  trans_correct Γ1 (Efun f w xs e k) (Efun f w (live_args xs bs) e' k').
Proof.
  unfold trans_correct, E.
  intros.
  inv H11.
  - exists 0, OOT; split; simpl; eauto.
  - inv H12.
    edestruct (H0 ex (i - 1) (M.set f (Vfun f ρ1 w xs e) ρ1) (M.set f (Vfun f ρ2 w (live_args xs bs) e') ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply free_fun_k_inv; eauto.
    + eapply free_fun_k_inv; eauto.
    + eapply G_subset with (Γ2 := (f |: (occurs_free (Efun f w (live_args xs bs) e' k')))); eauto.
      * eapply G_set; eauto.
        -- eapply G_mono with i; eauto; try lia.
        -- eapply Vfun_V; eauto.
           ++ apply G_mono with i; eauto; try lia.
           ++ eapply free_fun_e_inv; eauto.
           ++ apply free_fun_e_subset.
      * apply Included_refl.
      * apply free_fun_k_subset.
    + exists (S j2), r2; split; auto.
      * constructor; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma app_compat_refl xs Γ f w :
  M.get w L = None ->
  trans_correct Γ (Eapp f w xs) (Eapp f w xs).
Proof.
  unfold trans_correct, G, E.
  intros.
  inv H4.
  - exists 0, OOT; split; simpl; auto.
  - inv H5.
    unfold Ensembles.Included, Ensembles.In, Dom_map in *.
    destruct (H2 f) as [fv1 [Heqfv1 Hfv2]]; eauto.
    rewrite Heqfv1 in H9; inv H9.
    destruct Hfv2 as [fv2 [Heqfv2 HV]]; auto.
    destruct fv2.
    + destruct i.
      inv H3.
      simpl in HV.
      destruct HV; subst.
      destruct (L ! w0); try discriminate.
      destruct H5 as [Hlen HVv].

      edestruct (G_get_list_refl H2 xs) as [vs2 [Heqvs2 Vvs]]; eauto.
      {
        unfold Ensembles.Included, Ensembles.In, FromList, Dom_map.
        intros.
        eapply H0.
        apply Free_app2; auto.
      }
      {
        unfold Ensembles.Included, Ensembles.In, FromList, Dom_map.
        intros; auto.
      }
      destruct (set_lists_length3 (M.set v (Vfun v t w0 l e0) t) l vs2) as [ρ4 Heqρ4].
      rewrite <- (Forall2_length _ _ _ Vvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H12); auto.

      assert (HE : E (exposedb w0) (i - (i - i)) ρ'' e ρ4 e0).
      {
        eapply (HVv i vs vs2); eauto.
        - intros.
          destruct H16; auto.
          split; auto.
          eapply V_exposed_Forall; eauto.
        - apply ForallV_mono with (S i); auto; lia.
      }

      apply (E_mono _ i) in HE; try lia.
      unfold E in HE.
      destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
      exists (S j2), r2; split; eauto.
      constructor.
      * eapply BStep_app; eauto.
        intros.
        destruct H16; auto.
        split.
        eapply V_exposed_Forall; eauto.
        eapply R_exposed; eauto.
      * destruct ex; auto.
        eapply R_exposed; eauto.
    + destruct i; try contradiction.
Qed.

Lemma app_compat {xs bs} Γ f w :
  M.get w L = Some bs ->
  length xs = length bs ->
  ~ (w \in Exposed) ->
  trans_correct Γ (Eapp f w xs) (Eapp f w (live_args xs bs)).
Proof.
  unfold trans_correct, G, E.
  intros.
  inv H6.
  - exists 0, OOT; split; simpl; auto.
  - inv H7.
    unfold Ensembles.Included, Ensembles.In, Dom_map in *.
    destruct (H4 f) as [fv1 [Heqfv1 Hfv2]]; eauto.
    rewrite Heqfv1 in H11; inv H11.
    destruct Hfv2 as [fv2 [Heqfv2 HV]]; auto.
    destruct fv2.
    + destruct i.
      inv H5.
      simpl in HV.
      destruct HV; subst.
      destruct (L ! w0); try discriminate.
      inv H.
      destruct H7 as [Hlen [Heql [_ HVv]]]; subst.

      edestruct (G_get_list H4 xs bs) as [vs2 [Heqvs2 Vvs]]; eauto.
      {
        unfold Ensembles.Included, Ensembles.In, FromList, Dom_map.
        intros.
        eapply H2; auto.
      }
      {
        unfold Ensembles.Included, Ensembles.In, FromList, Dom_map.
        intros; auto.
      }

      destruct (set_lists_length3 (M.set v (Vfun v t w0 (live_args xs' bs) e0) t) (live_args xs' bs) vs2) as [ρ4 Heqρ4].
      rewrite <- (Forall2_length _ _ _ Vvs).
      apply live_args_length.
      rewrite <- (set_lists_length_eq _ _ _ _ H14); auto.

      assert (HE : E (exposedb w0) (i - (i - i)) ρ'' e ρ4 e0).
      {
        eapply (HVv i vs vs2); eauto.
        apply ForallV_mono with (S i); auto; lia.
      }

      apply (E_mono _ i) in HE; try lia.
      unfold E in HE.
      destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
      exists (S j2), r2; split; eauto.
      constructor.
      * eapply BStep_app; eauto.
        intros.
        destruct H18; auto.
        split.
        eapply V_exposed_Forall; eauto.
        eapply incl_Forall; eauto.
        apply live_args_incl.
        eapply R_exposed; eauto.
      * destruct ex; auto.
        eapply R_exposed; eauto.
    + destruct i; try contradiction.
Qed.

Lemma letapp_compat_refl {Γ k k' w xs} x f :
  trans_correct (x |: Γ) k k' ->
  M.get w L = None ->
  trans_correct Γ (Eletapp x f w xs k) (Eletapp x f w xs k').
Proof.
  intros.
  specialize (app_compat_refl xs Γ f w H0); intros Ha.
  unfold trans_correct, E in *.
  intros.
  assert (HFa : occurs_free (Eapp f w xs) \subset Γ).
  {
    apply Included_trans with (occurs_free (Eletapp x f w xs k')); auto.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H6; auto.
  }

  assert (HGa : G i Γ ρ1 (occurs_free (Eapp f w xs)) ρ2).
  {
    eapply G_subset; eauto.
    apply Included_refl.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H6; auto.
  }

  specialize (Ha (exposedb w) _ _ _ HFa HFa HGa).
  inv H5.
  - exists 0, OOT; split; simpl; auto.
  - inv H6.
    + destruct (Ha (S c0) (Res v)) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      * constructor.
        -- eapply BStep_app; eauto.
           intros.
           destruct H19; auto.
        -- destruct (exposed_reflect w); auto.
           destruct H19; auto.
      * simpl in Rra.
        destruct ra; try contradiction.
        edestruct (H ex (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
        -- eapply free_letapp_k_inv; eauto.
        -- eapply free_letapp_k_inv; eauto.
        -- eapply G_subset with (Γ2 := (x |: (occurs_free (Eletapp x f w xs k')))).
           eapply G_set; eauto.
           apply G_mono with i; try lia; eauto.
           apply Included_refl.
           apply free_letapp_k_subset.
        -- exists (j1 + j2), r2; split.
           ++ inv Hap.
              inv H5.
              assert ((S c + j2) = S (c + j2)). lia.
              rewrite H5.
              constructor.
              ** eapply BStep_letapp_Res; eauto.
                 intros.
                 destruct H24; auto.
                 split; auto.
                 inv H10; auto.
              ** destruct ex; auto.
                 eapply R_exposed; eauto.
           ++ apply R_mono with (i - S c0 - c'); try lia; auto.
    + destruct (Ha (S c) OOT) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      constructor; eauto.
      destruct (exposed_reflect w); auto.
      exists j1, ra.
      destruct ra; try contradiction.
      split; auto.
      inv Hap; eauto.
      inv H5; eauto.
      constructor.
      eapply BStep_letapp_OOT; eauto.
      * intros.
        destruct H23; auto.
      * intros; auto.
Qed.

Lemma letapp_compat {Γ k k' w bs xs} x f :
  trans_correct (x |: Γ) k k' ->
  M.get w L = Some bs ->
  length xs = length bs ->
  ~ (w \in Exposed) ->
  trans_correct Γ (Eletapp x f w xs k) (Eletapp x f w (live_args xs bs) k').
Proof.
  intros.
  specialize (app_compat Γ f w H0 H1 H2); intros Ha.
  unfold trans_correct, E in *.
  intros.
  assert (HFa : occurs_free (Eapp f w xs) \subset Γ).
  {
    apply Included_trans with (occurs_free (Eletapp x f w xs k)); auto.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H8; auto.
  }

  assert (HFa' : occurs_free (Eapp f w (live_args xs bs)) \subset Γ).
  {
    apply Included_trans with (occurs_free (Eletapp x f w (live_args xs bs) k')); auto.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H8; auto.
  }

  assert (HGa : G i Γ ρ1 (occurs_free (Eapp f w (live_args xs bs))) ρ2).
  {
    eapply G_subset; eauto.
    apply Included_refl.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H8; auto.
  }

  specialize (Ha (exposedb w) _ _ _ HFa HFa' HGa).
  inv H7.
  - exists 0, OOT; split; simpl; auto.
  - inv H8.
    + destruct (Ha (S c0) (Res v)) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      * constructor.
        -- eapply BStep_app; eauto.
           intros.
           destruct H21; auto.
        -- destruct (exposed_reflect w); auto.
           destruct H21; auto.
      * simpl in Rra.
        destruct ra; try contradiction.
        edestruct (H ex (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
        -- eapply free_letapp_k_inv; eauto.
        -- eapply free_letapp_k_inv; eauto.
        -- eapply G_subset with (Γ2 := (x |: (occurs_free (Eletapp x f w (live_args xs bs) k')))).
           eapply G_set; eauto.
           apply G_mono with i; try lia; eauto.
           apply Included_refl.
           apply free_letapp_k_subset.
        -- exists (j1 + j2), r2; split.
           ++ inv Hap.
              inv H7.
              assert ((S c + j2) = S (c + j2)). lia.
              rewrite H7.
              constructor.
              ** eapply BStep_letapp_Res; eauto.
                 intros.
                 destruct H2; auto.
              ** destruct ex; auto.
                 eapply R_exposed; eauto.
           ++ apply R_mono with (i - S c0 - c'); try lia; auto.
    + destruct (Ha (S c) OOT) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      constructor; eauto.
      destruct (exposed_reflect w); auto.
      exists j1, ra.
      destruct ra; try contradiction.
      split; auto.
      inv Hap; eauto.
      inv H7; eauto.
      constructor.
      eapply BStep_letapp_OOT; eauto.
      * intros.
        destruct H2; auto.
      * intros; auto.
Qed.

Lemma if_compat {Γ e e' t t'} x :
  trans_correct Γ t t' ->
  trans_correct Γ e e' ->
  trans_correct Γ (Eif x t e) (Eif x t' e').
Proof.
  unfold trans_correct, E.
  intros Ht He. intros.
  inv H3.
  - exists 0, OOT; simpl; eauto.
  - inv H4.
    + edestruct Ht with (i := i) (j1 := c) as [j2 [r2 [Ht' Rr]]]; eauto; try lia; intros.
      * eapply free_if_t_inv; eauto.
      * eapply free_if_t_inv; eauto.
      * apply G_mono with i; try lia; eauto.
        eapply G_subset; eauto.
        apply Included_refl.
        apply free_if_t_subset.
      * unfold G in *.
        destruct (H1 x) as [v1 [Heqv1 Hv2]]; auto.
        destruct Hv2 as [v2 [Heqv2 HV]]; auto.
        rewrite Heqv1 in H11; inv H11.
        destruct v2.
        destruct i; contradiction.
        exists (S j2), r2.
        destruct i; simpl in HV; subst; split.
        -- constructor; auto.
           destruct ex; auto.
           eapply R_exposed; eauto.
        -- apply R_mono with (0 - c); try lia; auto.
        -- constructor; auto.
           destruct ex; auto.
           eapply R_exposed; eauto.
        -- apply R_mono with (S i - c); try lia; auto.
    + edestruct He with (i := i) (j1 := c) as [j2 [r2 [Ht' Rr]]]; eauto; try lia; intros.
      * eapply free_if_e_inv; eauto.
      * eapply free_if_e_inv; eauto.
      * apply G_mono with i; try lia; eauto.
        eapply G_subset; eauto.
        apply Included_refl.
        apply free_if_e_subset.
      * unfold G in *.
        destruct (H1 x) as [v1 [Heqv1 Hv2]]; auto.
        destruct Hv2 as [v2 [Heqv2 HV]]; auto.
        rewrite Heqv1 in H11; inv H11.
        destruct v2.
        destruct i; contradiction.
        exists (S j2), r2.
        destruct i; simpl in HV; subst; split.
        -- constructor; auto.
           destruct ex; auto.
           eapply R_exposed; eauto.
        -- apply R_mono with (0 - c); try lia; auto.
        -- constructor; auto.
           destruct ex; auto.
           eapply R_exposed; eauto.
        -- apply R_mono with (S i - c); try lia; auto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {Γ e e'} :
  trans Γ e e' -> trans_correct Γ e e'.
Proof.
  intro H.
  induction H.
  - apply ret_compat; auto.
  - eapply fun_compat; eauto.
  - eapply fun_compat_refl; eauto.
  - eapply app_compat; eauto.
  - eapply app_compat_refl; eauto.
  - eapply letapp_compat; eauto.
  - eapply letapp_compat_refl; eauto.
  - eapply prim_val_compat; eauto.
  - apply if_compat; auto.
Qed.

(* Top Level *)
Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  forall x,
    (x \in Γ1) ->
    exists v1,
      M.get x ρ1 = Some v1 /\
      exposed v1 /\
      ((x \in Γ2) ->
       exists v2,
         M.get x ρ2 = Some v2 /\
         V i v1 v2).

Lemma G_top_G : forall {i Γ1 ρ1 Γ2 ρ2},
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    G i Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G_top, G.
  intros.
  edestruct H as [v1 [Heqv1 [Hexv1 Hv2]]]; eauto.
Qed.

Definition trans_correct_top etop etop' :=
  forall i ρ1 ρ2,
    G_top i (occurs_free etop) ρ1 (occurs_free etop') ρ2 ->
    E true i ρ1 etop ρ2 etop'.

Theorem top etop etop' :
  trans (occurs_free etop) etop etop' ->
  trans_correct_top etop etop'.
Proof.
  unfold trans_correct_top.
  intros.
  specialize (fundamental_property H);
    unfold trans_correct; intros.
  eapply H1.
  - apply Included_refl.
  - eapply free_trans_inv; eauto.
  - eapply G_top_G; eauto.
Qed.

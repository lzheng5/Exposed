From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

Require Import UntypedExposed.ANF.

(* Reflexive logical relation used by CertiCoq *)

(* Logical Relations *)
Definition R' (P : nat -> val -> val -> Prop) (i : nat) (r1 : res) (r2 : res) :=
  match r1, r2 with
  | OOT, OOT => True
  | Res v1, Res v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> val -> val -> Prop) (ex : bool) (i : nat) (ρ1 : env) (e1 :exp) (ρ2 : env) (e2 : exp) : Prop :=
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
      w1 = w2 /\
      match i with
      | 0 => True
      | S i0 =>
          length xs1 = length xs2 /\
            forall j vs1 vs2 ρ3 ρ4,
            j <= i0 ->
            (w1 \in Exposed -> Forall exposed vs1 /\ Forall exposed vs2) ->
            Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
            set_lists xs1 vs1 (M.set f1 (Vfun f1 ρ1 w1 xs1 e1) ρ1) = Some ρ3 ->
            set_lists xs2 vs2 (M.set f2 (Vfun f2 ρ2 w2 xs2 e2) ρ2) = Some ρ4 ->
            E' V (exposedb w1) (i0 - (i0 - j)) ρ3 e1 ρ4 e2
      end
  | _, _ => False
  end.

Notation R := (R' V).

Notation E := (E' V).

(* Environment Relation *)
Definition G i ρ1 ρ2 :=
  forall x v1,
    M.get x ρ1 = Some v1 ->
    exists v2,
      M.get x ρ2 = Some v2 /\
      V i v1 v2.

Definition related e1 e2 :=
  forall ex i ρ1 ρ2,
    G i ρ1 ρ2 ->
    E ex i ρ1 e1 ρ2 e2.

(* Environment Lemmas *)
Lemma G_set {i ρ1 ρ2}:
  G i ρ1 ρ2 ->
  forall {x v1 v2},
    V i v1 v2 ->
    G i (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  unfold G.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - rewrite M.gss in *.
    inv H1; eauto.
  - rewrite M.gso in *; auto.
Qed.

Lemma G_set_lists {i ρ1 ρ2}:
  G i ρ1 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 (V i) vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    G i ρ3 ρ4.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    inv H0; inv H1.
    eapply HG; eauto.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
    inv H; inv H0; inv H1.
    destruct (M.elt_eq x a); subst.
    + rewrite M.gss in *; eauto.
      inv H2; eauto.
    + rewrite M.gso in *; auto.
      eapply IHxs; eauto.
Qed.

Lemma G_get_list {i ρ1 ρ2} :
  G i ρ1 ρ2 ->
  forall {xs vs1},
    get_list xs ρ1 = Some vs1 ->
    exists vs2,
      get_list xs ρ2 = Some vs2 /\
      Forall2 (V i) vs1 vs2.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - inv H; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H.
    edestruct HG as [v2 [Heqv2 Vv]]; eauto.
    rewrite Heqv2.
    edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
    rewrite Heqvs2.
    exists (v2 :: vs2); split; auto.
Qed.

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
    destruct H as [Hw [Hlen Hv]].
    destruct m; simpl; auto; try contradiction.
    repeat split; auto; intros.
    assert (Hj0 : m - (m - j0) = (S m - (S m - j0))). lia.
    rewrite Hj0 in *.
    eapply Hv; eauto.
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

Lemma E_mono {w ρ1 ρ2 e1 e2} i j:
  E w i ρ1 e1 ρ2 e2 ->
  j <= i ->
  E w j ρ1 e1 ρ2 e2.
Proof.
  unfold E.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; eauto.
  apply R_mono with (i - j1); try lia; auto.
Qed.

Lemma G_mono {ρ1 ρ2} i j:
  G i ρ1 ρ2 ->
  j <= i ->
  G j ρ1 ρ2.
Proof.
  unfold G.
  intros.
  edestruct H as [v2 [Heqv2 Vv]]; eauto.
  exists v2; split; auto.
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

(* Compatibility Lemmas *)
Lemma ret_compat x :
  related (Eret x) (Eret x).
Proof.
  unfold related, G, E, R.
  intros.
  inv H1.
  - exists 0, OOT; auto.
  - inv H2.
    edestruct H as [v2 [Heqv2 Vv]]; eauto.
    exists 1, (Res v2); split; auto.
    + constructor; auto.
      destruct ex; auto.
      eapply V_exposed_res; eauto.
    + apply V_mono with i; try lia; auto.
Qed.

Lemma prim_val_compat {k} x p :
  related k k ->
  related (Eprim_val x p k) (Eprim_val x p k).
Proof.
  unfold related.
  intros.

  assert (HE : E ex i (M.set x (Vprim p) ρ1) k (M.set x (Vprim p) ρ2) k).
  {
    apply H.
    apply G_set; auto.
    destruct i; simpl; auto.
  }

  unfold E in *.
  intros.
  inv H2.
  - exists 0, OOT; split; simpl; auto.
  - inv H3.
    edestruct (HE c r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    exists (S j2), r2; split; eauto.
    constructor; auto.
    + destruct ex; auto.
      eapply R_exposed; eauto.
    + apply R_mono with (i - c); try lia; auto.
Qed.

Lemma Vfun_V {e} :
  related e e ->
  forall {i ρ1 ρ2} f w xs,
    G i ρ1 ρ2 ->
    V i (Vfun f ρ1 w xs e) (Vfun f ρ2 w xs e).
Proof.
  unfold related.
  intros He i.
  induction i; simpl; intros; auto.
  repeat split; auto; intros.
  apply (He (exposedb w) (i - (i - j)) ρ3 ρ4).
  eapply G_set_lists; eauto.
  apply G_set; auto.
  - apply G_mono with (S i); auto; lia.
  - apply V_mono with i; try lia.
    apply IHi; auto.
    apply G_mono with (S i); auto; lia.
Qed.

Lemma fun_compat {e k} f w xs :
  related e e ->
  related k k ->
  related (Efun f w xs e k) (Efun f w xs e k).
Proof.
  unfold related, E.
  intros.
  inv H3.
  - exists 0, OOT; split; simpl; auto.
  - inv H4.
    edestruct (H0 ex (i - 1) (M.set f (Vfun f ρ1 w xs e) ρ1) (M.set f (Vfun f ρ2 w xs e) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + apply G_set.
      * apply G_mono with i; auto; lia.
      * eapply Vfun_V; eauto.
        apply G_mono with i; auto; lia.
    + exists (S j2), r2; split.
      * constructor; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma app_compat f w xs :
  related (Eapp f w xs) (Eapp f w xs).
Proof.
  unfold related, G, E.
  intros.
  inv H1.
  - exists 0, OOT; split; simpl; auto.
  - inv H2.
    edestruct H as [v2 [Heqv2 Vv]]; eauto.
    destruct v2.
    + destruct i.
      inv H0.
      simpl in Vv.
      destruct Vv as [Hw [Hlen HVv]]; subst.
      destruct (G_get_list H H7) as [vs2 [Heqvs2 Vvs]]; eauto.
      destruct (set_lists_length3 (M.set v (Vfun v t w0 l e0) t) l vs2) as [ρ4 Heqρ4].
      rewrite <- (Forall2_length _ _ _ Vvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H9).
      symmetry; auto.

      assert (HE : E (exposedb w0) (i - (i - i)) ρ'' e ρ4 e0).
      {
        eapply (HVv i vs vs2); eauto.
        - intros.
          destruct H13; auto.
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
        destruct H13; auto.
        split.
        eapply V_exposed_Forall; eauto.
        eapply R_exposed; eauto.
      * destruct ex; auto.
        eapply R_exposed; eauto.
    + destruct i; try contradiction.
Qed.

Lemma letapp_compat {k} x f w xs :
  related k k ->
  related (Eletapp x f w xs k) (Eletapp x f w xs k).
Proof.
  intros.
  specialize (app_compat f w xs); intros Ha.
  unfold related, E in *.
  intros.
  specialize (Ha (exposedb w) _ _ _ H0).
  inv H2.
  - exists 0, OOT; split; simpl; auto.
  - inv H3.
    + destruct (Ha (S c0) (Res v)) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      * constructor.
        -- eapply BStep_app; eauto.
           intros.
           destruct H16; auto.
        -- destruct (exposed_reflect w); auto.
           destruct H16; auto.
      * simpl in Rra.
        destruct ra; try contradiction.
        edestruct (H ex (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
        -- apply G_set; auto.
           apply G_mono with i; try lia; auto.
        -- exists (j1 + j2), r2; split.
           ++ inv Hap.
              inv H2.
              assert ((S c + j2) = S (c + j2)). lia.
              rewrite H2.
              constructor.
              ** eapply BStep_letapp_Res; eauto.
                 intros.
                 destruct H21; auto.
                 inv H7.
                 split; auto.
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
      inv H2; eauto.
      constructor.
      eapply BStep_letapp_OOT; eauto.
      * intros.
        destruct H20; auto.
      * intros; auto.
Qed.

Lemma if_compat {e t} x :
  related t t ->
  related e e ->
  related (Eif x t e) (Eif x t e).
Proof.
  unfold related, G, E.
  intros Ht He. intros.
  inv H1.
  - exists 0, OOT; simpl; eauto.
  - inv H2.
    + edestruct Ht with (j1 := c) as [j2 [r2 [Ht' Rr]]]; eauto; try lia.
      exists (S j2), r2; split; eauto.
      * constructor; auto.
        apply BStep_if_true; auto.
        edestruct H as [v2 [Heqv2 Vv]]; eauto.
        destruct v2.
        destruct i; contradiction.
        destruct i; simpl in Vv; subst; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * apply R_mono with (i - c); try lia; auto.
    + edestruct He with (j1 := c) as [j2 [r2 [He' Rr]]]; eauto; try lia.
      exists (S j2), r2; split; eauto.
      * constructor; auto.
        apply BStep_if_false; auto.
        edestruct H as [v2 [Heqv2 Vv]]; eauto.
        destruct v2.
        destruct i; contradiction.
        destruct i; simpl in Vv; subst; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * apply R_mono with (i - c); try lia; auto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property e :
  related e e.
Proof.
  induction e.
  - apply ret_compat.
  - apply app_compat.
  - apply letapp_compat; auto.
  - apply fun_compat; auto.
  - apply prim_val_compat; auto.
  - apply if_compat; auto.
Qed.

(* Top Level *)
Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  (* need to add an extra invariant at the top-level to relate Refl2.G_top
   * which should make sense as transformations in CertiCoq
   * don't introduce new free/imported variables *)
  Γ2 \subset Γ1 /\
  Γ1 \subset (Dom_map ρ1) /\
  forall x v1,
    M.get x ρ1 = Some v1 ->
    (exposed v1 /\
     exists v2,
       M.get x ρ2 = Some v2 /\
       V i v1 v2).

Lemma G_top_G : forall {i Γ1 ρ1 Γ2 ρ2},
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    G i ρ1 ρ2.
Proof.
  unfold G_top, G.
  intros.
  destruct H as [HΓ [Hρ HG]].
  unfold Ensembles.Included, Ensembles.In, Dom_map in *.
  edestruct HG as [Hexv1 [v2 [Heqv2 HV]]]; eauto.
Qed.

Definition related_top etop etop' :=
  forall i ρ1 ρ2,
    G_top i (occurs_free etop) ρ1 (occurs_free etop') ρ2 ->
    E true i ρ1 etop ρ2 etop'.

Theorem top {etop}:
  related_top etop etop.
Proof.
  unfold related_top.
  intros.
  specialize (fundamental_property etop);
    unfold related; intros.
  eapply H0.
  eapply G_top_G; eauto.
Qed.

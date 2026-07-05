From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From LambdaANF Require Import ANF.
From LambdaWeb Require Import ANF.
From Erase Require Import Erase.

Module A0 := LambdaANF.ANF.
Module A1 := LambdaWeb.ANF.

(* Cross-language Compositionality *)

(* Adequacy *)
Theorem adequacy e1 e2:
  trans_correct_top e1 e2 ->
  forall ρ1 ρ2,
    wf_env ρ1 ->
    (forall k, G_top k (A1.occurs_free e1) ρ1 ρ2) ->
    forall j1 r1,
      A1.bstep_fuel true ρ1 e1 j1 r1 ->
      exists j2 r2,
        A0.bstep_fuel ρ2 e2 j2 r2 /\
        (forall k, R k r1 r2).
Proof.
  intros.
  unfold trans_correct_top in H.
  destruct H as [HS HT].

  assert (HE : E true j1 ρ1 e1 ρ2 e2) by (eapply (HT j1); eauto).
  edestruct (HE j1) as [j2 [r2 [Hstep2 HR]]]; eauto.
  eexists; eexists; split; eauto.

  intros.
  assert (HE' : E true (j1 + k) ρ1 e1 ρ2 e2) by (eapply HT; eauto).
  edestruct (HE' j1) as [j2' [r2' [Hstep2' HR']]]; eauto; try lia.

  rewrite_math (j1 + k - j1 = k).
  rewrite_math (j1 - j1 = 0).

  destruct r2; destruct r2'; destruct r1;
    simpl in *; auto; try contradiction.

  edestruct (A0.bstep_fuel_deterministic v v0 Hstep2 Hstep2'); subst; eauto.
Qed.

(* Behavioral Refinement *)
Inductive val_ref : A1.wval -> A0.val -> Prop :=
| Ref_Tag :
  forall w v1 v2,
    (w \in Exposed) ->
    val_ref' v1 v2 ->
    val_ref (Tag w v1) v2

with val_ref' : A1.val -> A0.val -> Prop :=
| Ref_Vfun :
  forall f1 ρ1 xs1 e1 f2 ρ2 xs2 e2,
    val_ref' (A1.Vfun f1 ρ1 xs1 e1) (A0.Vfun f2 ρ2 xs2 e2)

| Ref_Vconstr_nil :
  forall c,
    val_ref' (A1.Vconstr c []) (A0.Vconstr c [])

| Ref_Vconstr_cons :
  forall c v1 v2 vs1 vs2,
    val_ref v1 v2 ->
    val_ref' (A1.Vconstr c vs1) (A0.Vconstr c vs2) ->
    val_ref' (A1.Vconstr c (v1 :: vs1)) (A0.Vconstr c (v2 :: vs2)).

Hint Constructors val_ref : core.
Hint Constructors val_ref' : core.

Scheme val_ref_mut := Induction for val_ref Sort Prop
with val_ref'_mut := Induction for val_ref' Sort Prop.

Lemma val_ref_Vconstr c w vs1 vs2 :
  (w \in Exposed) ->
  Forall2 val_ref vs1 vs2 ->
  val_ref (Tag w (A1.Vconstr c vs1)) (A0.Vconstr c vs2).
Proof.
  intros.
  induction H0; simpl; auto.
  fcrush.
Qed.

Lemma V_val_ref {v1 v2} :
  wf_val v1 ->
  exposed v1 ->
  (forall i, V i v1 v2) ->
  val_ref v1 v2.
Proof.
  intros H.
  revert v2.
  induction H using wf_val_mut with (P0 := fun v1 wf =>
                                             forall (v2 : A0.val) w,
                                               (w \in Exposed) ->
                                               (match v1 with
                                                | Vfun _ _ _ _ => True
                                                | Vconstr c vs1 => Forall exposed vs1
                                                end) ->
                                               (forall i, (V i (Tag w v1) v2)) ->
                                               match v1, v2 with
                                               | A1.Vfun _ _ _ _, A0.Vfun _ _ _ _ => True
                                               | A1.Vconstr c1 vs1, A0.Vconstr c2 vs2  =>
                                                   c1 = c2 /\ Forall2 val_ref vs1 vs2
                                               | _ , _ => False
                                               end)
                                    (P1 := fun ρ wf => True);
    intros; simpl in *; eauto.
  - inv H.
    + specialize (IHwf_val v2 _ H2).
      destruct v2.
      destruct v; try contradiction; subst; auto.
      fcrush.
    + specialize (IHwf_val v2 _ H3 H4).
      destruct v2.
      destruct v; try contradiction; subst; auto.
      * edestruct IHwf_val as [Heqc Hval]; eauto; subst.
        eapply val_ref_Vconstr; eauto.
  - destruct v2.
    destruct v; auto;
      destruct (H1 0) as [_ [_ [Hw H']]]; subst; auto; contradiction.
    specialize (H1 0).
    sfirstorder.
  - destruct v2.
    + specialize (H1 0); sfirstorder.
    + specialize (H1 0); simpl in *;
        destruct H1 as [Hc Hlen].
      sauto.
  - destruct v2.
    + specialize (H2 0); sfirstorder.
    + pose proof H2 as HV.
      specialize (H2 1); simpl in *;
        destruct H2 as [Hv1 [Hc HV']]; subst;
          split; auto.
      inv HV'.
      clear H4 H6.
      assert (HV' : forall i, V i v y /\ V i (A1.Tag w0 (A1.Vconstr c0 vs)) (A0.Vconstr c0 l')).
      {
        intros.
        specialize (HV (S i)).
        destruct i; simpl in *;
          destruct HV as [_ [_ HFV]];
          inv HFV.
          - inv Hv1.
            inv H1.
            inv H6.
            repeat (split; auto).
            + eapply Forall2_length; eauto.
          - inv Hv1.
            inv H1.
            inv H6.
            repeat (split; auto).
            eapply V_mono_Forall with (S i); eauto.
      }

      assert (HV0 : forall i, V i v y) by (intros; destruct (HV' i); auto).
      assert (HV1 : forall i, V i (A1.Tag w0 (A1.Vconstr c0 vs)) (A0.Vconstr c0 l')) by (intros; destruct (HV' i); auto).

      inv H1.
      constructor; auto.
      fcrush.
Qed.

Lemma R_res_val_ref {v1 v2} :
  wf_val v1 ->
  exposed v1 ->
  (forall i, R i (A1.Res v1) (A0.Res v2)) ->
  val_ref v1 v2.
Proof. intros; eapply V_val_ref; eauto. Qed.

(* Linking Compat Lemmas *)

(* [trans_correct] is stronger than [trans_correct_top] due to [G_top] *)
Lemma trans_correct_trans_correct_top e1 e2 :
  A0.occurs_free e2 \subset A1.occurs_free e1 ->
  trans_correct (A1.occurs_free e1) e1 e2 ->
  trans_correct_top e1 e2.
Proof.
  unfold trans_correct_top, trans_correct.
  intros.
  split; auto; intros.
  eapply H0; eauto.
  eapply G_top_G; eauto.
Qed.

(* Top-level Environment Lemmas *)

Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 :
  G_top i Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  G_top i Γ2 ρ1 ρ2.
Proof. unfold G_top. fcrush. Qed.

Lemma G_top_wf_env_l i Γ1 ρ1 ρ2 :
  G_top i Γ1 ρ1 ρ2 ->
  wf_env ρ1.
Proof. unfold G_top. intros; tauto. Qed.

Lemma G_top_get {Γ1 i ρ1 ρ2}:
  G_top i Γ1 ρ1 ρ2 ->
  forall x v1,
    (x \in Γ1) ->
    M.get x ρ1 = Some v1 ->
    exists v2,
      M.get x ρ2 = Some v2 /\
        exposed v1 /\
        V i v1 v2.
Proof.
  unfold G.
  intros.
  destruct H as [Hwf HG].
  edestruct HG as [v1' [v2 [Heqv1 [Heqv2 HV]]]]; eauto; invc.
  fcrush.
Qed.

Lemma G_top_get_list {i Γ1 ρ1 ρ2} :
  G_top i Γ1 ρ1 ρ2 ->
  forall xs vs1,
    (FromList xs) \subset Γ1 ->
    get_list xs ρ1 = Some vs1 ->
    exists vs2,
      get_list xs ρ2 = Some vs2 /\
        Forall exposed vs1 /\
        Forall2 (V i) vs1 vs2.
Proof.
  intros HG xs.
  induction xs; simpl; intros.
  - fcrush.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H0.
    unfold Ensembles.Included, Ensembles.In in *.
    edestruct (G_top_get HG) as [v2 [Heqv2 HV]]; eauto.
    eapply (H a); fcrush.
    edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto; fcrush.
Qed.

Lemma G_top_set {i Γ1 ρ1 ρ2}:
  G_top i Γ1 ρ1 ρ2 ->
  forall {x v1 v2},
    exposed v1 ->
    V i v1 v2 ->
    G_top i (x |: Γ1) (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  unfold G.
  intro HG.
  pose proof HG as HG'.
  intros.

  destruct HG as [Hwf1 HG].
  split.
  eapply wf_env_set; eauto.
  eapply V_wf_val_l; eauto.

  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss.
    fcrush.
  - repeat (rewrite M.gso; auto).
    fcrush.
Qed.

Lemma G_top_set_lists {i Γ1 ρ1 ρ2}:
  G_top i Γ1 ρ1 ρ2 ->
  forall xs vs1 vs2 ρ3 ρ4,
    Forall exposed vs1 ->
    Forall2 (V i) vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    G_top i (FromList xs :|: Γ1) ρ3 ρ4.
Proof.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    inv H0; inv H1.
    eapply G_top_subset; fcrush.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
    inv H; inv H0; invc.
    eapply G_top_subset with (Γ1 := (a |: (FromList xs :|: Γ1)));
      try (normalize_sets;
           rewrite Union_assoc;
           apply Included_refl).
    eapply G_top_set; eauto.
Qed.

(* Monotonicity Lemma *)
Lemma G_top_mono {Γ1 ρ1 ρ2} i j:
  G_top i Γ1 ρ1 ρ2 ->
  j <= i ->
  G_top j Γ1 ρ1 ρ2.
Proof.
  unfold G_top.
  intros.
  destruct H as [Hwf1 HG].
  repeat (split; eauto); intros.
  edestruct HG as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto.
  eexists; eexists; repeat (split; eauto).
  apply V_mono with i; eauto.
Qed.

(* Compatibility Lemmas *)
Lemma Vfun_V_top e e' :
  trans_correct_top e e' ->
  forall i f w xs Γ1 ρ1 ρ2,
    wf_env ρ1 ->
    G_top i Γ1 ρ1 ρ2 ->
    (w \in Exposed) ->
    A1.occurs_free e \subset (FromList xs :|: (f |: Γ1)) ->
    V i (Tag w (A1.Vfun f ρ1 xs e)) (A0.Vfun f ρ2 xs e').
Proof.
  unfold trans_correct_top.
  intros [HS He] i.
  induction i; simpl; intros; auto.
  repeat (split; auto); intros.
  destruct (exposed_reflect w); try contradiction.

  apply (He (i - (i - j)) ρ3 ρ4); auto.
  eapply G_top_subset with (Γ1 := FromList xs :|: (f |: Γ1)); eauto.
  eapply G_top_set_lists with (vs1 := vs1) (vs2 := vs2); eauto.
  eapply G_top_set; eauto.
  eapply G_top_mono; eauto; try lia.
  apply V_mono with i; try lia.
  eapply IHi; eauto.
  apply G_top_mono with (S i); eauto; lia.
Qed.

Lemma free_fun_compat e e' f w k k' xs :
  A0.occurs_free e' \subset A1.occurs_free e ->
  A0.occurs_free k' \subset A1.occurs_free k ->
  A0.occurs_free (A0.Efun f xs e' k') \subset A1.occurs_free (A1.Efun f w xs e k).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  inv H1; auto.
Qed.

Lemma fun_compat_top e e' k k' f w xs :
  (w \in Exposed) ->
  trans_correct_top e e' ->
  trans_correct_top k k' ->
  trans_correct_top (A1.Efun f w xs e k) (A0.Efun f xs e' k').
Proof.
  unfold trans_correct_top, E, E'.
  intro Hex.
  intros.
  destruct H.
  destruct H0.
  split; intros.
  eapply free_fun_compat; eauto.

  pose proof H3 as HG.
  destruct H3 as [Hr2 HG'].
  inv H5.
  - fcrush.
  - inv H3.
    edestruct (H2 (i - 1) (M.set f (Tag w (A1.Vfun f ρ1 xs e)) ρ1) (M.set f (A0.Vfun f ρ2 xs e') ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_top_subset with (Γ1 := (f |: (A1.occurs_free (A1.Efun f w xs e k)))); eauto.
      * eapply G_top_set; eauto.
        eapply G_top_mono; eauto; try lia.
        eapply Vfun_V_top with (Γ1 := (A1.occurs_free (A1.Efun f w xs e k))); eauto.
        -- unfold trans_correct_top.
           split; auto.
        -- eapply G_top_mono; eauto; try lia.
        -- eapply A1.free_fun_e_subset; eauto.
      * eapply A1.free_fun_k_subset; eauto.
    + exists (S j2), r2; split; auto.
      apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma free_letapp_compat k k' f w x xs :
  A0.occurs_free k' \subset A1.occurs_free k ->
  A0.occurs_free (A0.Eletapp x f xs k') \subset A1.occurs_free (A1.Eletapp x f w xs k).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  inv H0; auto.
Qed.

Lemma letapp_compat_top k k' xs x f w :
  (w \in Exposed) ->
  trans_correct_top k k' ->
  trans_correct_top (A1.Eletapp x f w xs k) (A0.Eletapp x f xs k').
Proof.
  unfold trans_correct_top, E, E'.
  intro Hex.
  intros.
  destruct H.
  split; intros.
  eapply free_letapp_compat; eauto.

  pose proof H1 as HG.
  destruct H1 as [Hr2 HG'].
  inv H3.
  - fcrush.
  - inv H1.
    + edestruct (HG' f) as [fv1 [fv2 [Heqfv1 [Heqfv2 [Hexfv HVf]]]]]; eauto.
      rewrite Heqfv1 in H9; inv H9.
      destruct i.
      inv H2.
      destruct fv2; simpl in HVf.
      2 : { inv HVf; contradiction. }

      destruct HVf as [Hfv2 [Hlen HV]]; subst.

      edestruct (G_top_get_list HG xs) as [vs2 [Heqvs2 [Hexvs HVvs]]]; eauto.
      eapply A1.free_letapp_xs_subset; eauto.

      destruct (set_lists_length3 (M.set v0 (A0.Vfun v0 t l e0) t) l vs2) as [ρ4 Heqρ4].
      unfold wval in *.
      rewrite <- (Forall2_length _ _ _ HVvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H13); auto.

      unfold E' in HV.
      edestruct (HV i vs vs2 ρ'' ρ4) with (j1 := c0) as [j2 [r2 [He0 HR]]]; eauto; try lia.
      * eapply V_mono_Forall; eauto; lia.
      * destruct r2; simpl in HR; try contradiction.
        edestruct (H0 (i - c0) (M.set x v ρ1) (M.set x v1 ρ2)) with (j1 := c') as [j3 [r3 [He1 HR']]]; eauto; try lia.
        eapply G_top_subset with (Γ1 := x |: (A1.occurs_free (A1.Eletapp x f w xs k))); eauto.
        eapply G_top_set; eauto.
        eapply G_top_mono; eauto; lia.
        -- destruct H15; auto.
        -- eapply V_mono; eauto; try lia.
        -- eapply A1.free_letapp_k_subset; eauto.
        -- exists (S (j2 + j3)), r3; split; eauto.
           eapply R_mono; eauto; lia.
    + fcrush.
Qed.

(* Linking Preservation *)
Lemma preserves_linking f w x e1 e2 e1' e2' :
  (w \in Exposed) ->
  trans_correct_top e1 e2 ->
  trans_correct_top e1' e2' ->
  trans_correct_top (A1.link f w x e1 e1') (A0.link f x e2 e2').
Proof.
  unfold A0.link, A1.link.
  intros.
  eapply fun_compat_top; eauto.
  eapply letapp_compat_top; eauto.
Qed.

From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util RelComp ANF Refl.

(* Compositionality of The Reflexive Pipeline Based on [Refl.related_top] *)

(* Adequacy / Preservation of Termination *)
(* Behavioral Refinement *)
(* Linking Preservation *)

Section ReflComp.

  Definition Top_n := Comp related_top.

  Definition V_n := Comp (fun v1 v2 => forall k, V k v1 v2).

  Definition R_n := Comp (fun r1 r2 => forall k, R k r1 r2).

  Definition G_n n Γ1 Γ2 := Comp (fun ρ1 ρ2 => forall k, G_top k Γ1 ρ1 Γ2 ρ2) n.

  Lemma V_n_refl n v :
    wf_val v ->
    V_n n v v.
  Proof.
    revert v.
    induction n; intros.
    - constructor.
    - econstructor.
      + intros. eapply refl_V; eauto.
      + eapply IHn; eauto.
  Qed.

  Lemma R_n_V_n n v1 v2:
    R_n n (Res v1) (Res v2) ->
    V_n n v1 v2.
  Proof.
    intros H.
    remember (Res v1) as r1.
    remember (Res v2) as r2.
    generalize dependent v1.
    generalize dependent v2.
    induction H; simpl; intros; subst.
    - inv Heqr1; constructor.
    - destruct c2; simpl in H.
      + specialize (H 0); contradiction.
      + econstructor; eauto.
        eapply IHComp; eauto.
  Qed.

  Lemma R_n_Res_inv n v1 r2 :
    R_n n (Res v1) r2 ->
    wf_val v1 ->
    exists v2, r2 = Res v2 /\ V_n n v1 v2.
  Proof.
    intros H.
    remember (Res v1) as r1.
    generalize dependent v1.
    induction H; simpl; intros; subst; eauto.
    - eexists; split; eauto.
      apply V_n_refl; auto.
    - pose proof (H 0) as Hr.
      destruct c2; simpl in Hr; try contradiction.
      destruct Hr as [Hv1 [Hw HV]].
      edestruct IHComp as [v2 [Heq1 HVn]]; subst; eauto.
      eexists; split; eauto.
      econstructor.
      + intros.
        specialize (H k); simpl in *; eauto.
      + eapply R_n_V_n; eauto.
  Qed.

  Lemma Top_n_refl n e:
    Top_n n e e.
  Proof.
    apply Comp_refl.
    apply refl_related_top.
  Qed.

  Lemma Top_n_trans n m e1 e2 e3 :
    Top_n n e1 e2 ->
    Top_n m e2 e3 ->
    Top_n (n + m) e1 e3.
  Proof.
    apply Comp_trans.
    apply trans_related_top.
  Qed.

  Lemma Top_n_subset n e1 e2 :
    Top_n n e1 e2 ->
    occurs_free e2 \subset occurs_free e1.
  Proof.
    intros H.
    induction H.
    - apply Included_refl.
    - destruct H.
      eapply Included_trans; eauto.
  Qed.

  Lemma G_n_wf_env { n Γ1 Γ2 ρ1 ρ2 } :
    G_n n Γ1 Γ2 ρ1 ρ2 ->
    wf_env ρ2 ->
    wf_env ρ1.
  Proof.
    intros.
    induction H; auto.
    destruct (H 0) as [Hr1 [Hr2 _]]; auto.
  Qed.

  Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4 :
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    Γ3 \subset Γ1 ->
    Γ4 \subset Γ3 ->
    G_top i Γ3 ρ1 Γ4 ρ2.
  Proof.
    unfold G_top.
    intros.
    destruct H as [Hr1 [Hr2 [Hs HG]]].
    repeat (split; auto).
  Qed.

  Lemma G_n_subset n Γ1 Γ2 ρ1 Γ3 Γ4 ρ2 :
    G_n n Γ1 Γ2 ρ1 ρ2 ->
    Γ3 \subset Γ1 ->
    Γ4 \subset Γ3 ->
    G_n n Γ3 Γ4 ρ1 ρ2.
  Proof.
    intros H.
    revert Γ3 Γ4.
    induction H; simpl; intros.
    - constructor.
    - econstructor.
      + intros.
        eapply G_top_subset; eauto.
      + eapply IHComp; eauto.
  Qed.

End ReflComp.

Section Adequacy.

  Lemma Top_n_R_n n e1 e2:
    Top_n n e1 e2 ->
    forall ρ1 ρ2,
      wf_env ρ1 ->
      wf_env ρ2 ->
      G_n n (occurs_free e1) (occurs_free e2) ρ1 ρ2 ->
      forall j1 r1,
        bstep_fuel true ρ1 e1 j1 r1 ->
        exists j2 r2,
          bstep_fuel true ρ2 e2 j2 r2 /\
          R_n n r1 r2.
  Proof.
    intros Hrel.
    induction Hrel; intros.
    - inv H1.
      eexists; eexists; split; eauto.
      econstructor.
    - inv H2.
      rename c4 into ρ1'.
      unfold G_n in *.
      unfold related_top in H.
      destruct H.
      unfold E, E' in *.
      pose proof (H5 0) as HG0.
      destruct HG0 as [Hw1 [Hw2 [HS _]]].

      edestruct (H2 j1 ρ1 ρ1') with (j1 := j1) as [j2 [r2 [Hr2 HR]]]; eauto.
      + destruct (H5 j1) as [Hw1' [Hw2' [_ HG]]].
        repeat (split; auto).
      + edestruct (IHHrel ρ1' ρ2) as [j3 [r3 [Hr3 HR']]]; eauto.
        eapply G_n_subset; eauto.
        eapply Top_n_subset; eauto.

        eexists; eexists; split; eauto.
        econstructor; eauto.
        intros.
        edestruct (H2 (k + j1) ρ1 ρ1') with (j1 := j1) as [j4 [r4 [Hr4 HR'']]]; eauto; try lia.
        * specialize (H5 (k + j1)).
          eapply G_top_subset; eauto.
          apply Included_refl.
        * unfold R, R' in *.
          destruct r1; destruct r4; destruct r2; try contradiction; auto.
          edestruct (bstep_fuel_deterministic w1 w0 Hr2 Hr4); subst; eauto.
          eapply V_mono; eauto; try lia.
  Qed.

  (* Termination Perservation *)
  Theorem Top_n_preserves_termination n e1 e2 :
    Top_n n e1 e2 ->
    forall ρ1 ρ2,
      wf_env ρ1 ->
      wf_env ρ2 ->
      G_n n (occurs_free e1) (occurs_free e2) ρ1 ρ2 ->
      forall j1 v1,
        bstep_fuel true ρ1 e1 j1 (Res v1) ->
        exists j2 v2,
          bstep_fuel true ρ2 e2 j2 (Res v2) /\
          V_n n v1 v2.
  Proof.
    intros.
    edestruct Top_n_R_n with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
    inv H3.
    inv H5.
    assert (wf_val v1) by (eapply bstep_wf_res in H4; eauto; inv H4; auto).
    edestruct R_n_Res_inv as [v2 [Heq HVn]]; eauto; subst.
    eexists; eexists; split; eauto.
  Qed.

End Adequacy.

Section Refinement.

  Inductive val_ref : wval -> wval -> Prop :=
  | Ref_Tag :
    forall w v1 v2,
      val_ref' v1 v2 ->
      val_ref (Tag w v1) (Tag w v2)

  with val_ref' : val -> val -> Prop :=
  | Ref_Vfun :
    forall f1 ρ1 xs1 e1 f2 ρ2 xs2 e2,
      val_ref' (Vfun f1 ρ1 xs1 e1) (Vfun f2 ρ2 xs2 e2)

  | Ref_Vconstr_nil :
    forall c,
      val_ref' (Vconstr c []) (Vconstr c [])

  | Ref_Vconstr_cons :
    forall c v1 v2 vs1 vs2,
      val_ref v1 v2 ->
      val_ref' (Vconstr c vs1) (Vconstr c vs2) ->
      val_ref' (Vconstr c (v1 :: vs1)) (Vconstr c (v2 :: vs2)).

  Hint Constructors val_ref : core.
  Hint Constructors val_ref' : core.

  Scheme val_ref_mut := Induction for val_ref Sort Prop
  with val_ref'_mut := Induction for val_ref' Sort Prop.

  Lemma val_ref_Vconstr c w vs1 vs2 :
    Forall2 val_ref vs1 vs2 ->
    val_ref (Tag w (Vconstr c vs1)) (Tag w (Vconstr c vs2)).
  Proof.
    intros.
    induction H; simpl; auto.
    constructor.
    econstructor; eauto.
    inv IHForall2; auto.
  Qed.

  Lemma val_ref_refl v :
    wf_val v ->
    val_ref v v.
  Proof.
    intros H.
    induction H using wf_val_mut with (P0 := fun v wf =>
                                               match v with
                                               | Vfun _ _ _ _ => True
                                               | Vconstr c vs => Forall2 val_ref vs vs
                                               end)
                                      (P1 := fun ρ wf => True);
      intros; auto.
    destruct v; auto.
    eapply val_ref_Vconstr; eauto.
  Qed.

  Lemma val_ref_trans : Transitive val_ref.
  Proof.
    intros v1 v2 v3 H.
    revert v3.
    induction H using val_ref_mut with (P0 := fun v1 v2 vr =>
                                                forall v3,
                                                  val_ref' v2 v3 ->
                                                  val_ref' v1 v3);
      simpl; intros; inv H; auto.
    inv H0.
    apply IHval_ref in H5.
    apply IHval_ref0 in H6.
    constructor; auto.
  Qed.

  Lemma V_val_ref {v1 v2} :
    wf_val v1 ->
    (forall i, V i v1 v2) ->
    val_ref v1 v2.
  Proof.
    intros H.
    revert v2.
    induction H using wf_val_mut with (P0 := fun v1 wf =>
                                               forall (v2 : wval) w,
                                                 (forall i, (V i (Tag w v1) v2)) ->
                                                 match v1, v2 with
                                                 | Vfun _ _ _ _, TAG _ w' (Vfun _ _ _ _) => w = w'
                                                 | Vconstr c1 vs1, TAG _ w' (Vconstr c2 vs2) =>
                                                     w = w' /\ c1 = c2 /\ Forall2 val_ref vs1 vs2
                                                 | _ , _ => False
                                                 end)
                                      (P1 := fun ρ wf => True);
      intros; simpl in *; eauto.
    - specialize (IHwf_val _ _ H).
      destruct v2.
      destruct v; destruct v0; try contradiction; subst; auto.
      destruct IHwf_val as [Hw [Hc HV]]; subst; auto.
      destruct (H 0) as [_ [_ [Hw _]]]; subst.
      eapply val_ref_Vconstr; eauto.
    - destruct v2.
      destruct v; auto;
        destruct (H 0) as [_ [_ [Hw H']]]; subst; auto; contradiction.
    - destruct v2.
      destruct v.
      + destruct (H 0) as [_ [_ [_ H']]]; contradiction.
      + destruct (H 1) as [Hv1 [Hv2 [Hw [Hc HV]]]]; subst;
          split; auto.
        inv HV; auto.
    - destruct v2.
      destruct v0.
      + destruct (H0 0) as [_ [_ [_ H']]]; contradiction.
      + destruct (H0 1) as [Hv1 [Hv2 [Hw [Hc HV']]]]; subst;
          split; auto.
        inv HV'.
        clear H3 H5.
        assert (HV' : forall i, V i v y /\ V i (Tag w1 (Vconstr c0 vs)) (Tag w1 (Vconstr c0 l'))).
        {
          intros.
          specialize (H0 (S i)).
          destruct i; simpl in *;
            destruct H0 as [_ [_ [_ [_ HFV]]]];
            inv HFV.
          - inv Hv1; inv Hv2.
            inv H4; inv H7.
            repeat (split; auto).
            + intros.
              apply H2 in H0.
              inv H0.
              inv H13; auto.
            + intros.
              apply H6 in H0.
              inv H0.
              inv H13; auto.
            + eapply Forall2_length; eauto.
          - inv Hv1; inv Hv2.
            inv H4; inv H7.
            repeat (split; auto).
            + intros.
              apply H2 in H0.
              inv H0.
              inv H13; auto.
            + intros.
              apply H6 in H0.
              inv H0.
              inv H13; auto.
            + eapply V_mono_Forall with (S i); eauto.
        }

        assert (HV0 : forall i, V i v y) by (intros; destruct (HV' i); auto).
        assert (HV1 : forall i, V i (Tag w1 (Vconstr c0 vs)) (Tag w1 (Vconstr c0 l'))) by (intros; destruct (HV' i); auto).

        constructor; auto.
        specialize (IHwf_val0 _ _ HV1).
        simpl in IHwf_val0.
        destruct IHwf_val0 as [Hw [Hc HF]]; auto.
  Qed.

  Lemma R_res_val_ref {v1 v2} :
    wf_val v1 ->
    (forall i, R i (Res v1) (Res v2)) ->
    val_ref v1 v2.
  Proof.
    intros; eapply V_val_ref; eauto.
  Qed.

  Lemma R_n_res_val_ref {n v1 v2} :
    wf_val v1 ->
    R_n n (Res v1) (Res v2) ->
    val_ref v1 v2.
  Proof.
    intros.
    remember (Res v1) as r1.
    remember (Res v2) as r2.
    generalize dependent v1.
    generalize dependent v2.
    induction H0; simpl; intros; subst.
    - inv Heqr1; auto.
      apply val_ref_refl; auto.
    - pose proof (H 0) as HR0.
      destruct c2; simpl in HR0; try contradiction.
      destruct HR0 as [_ [Hw _]].
      assert (Heqv2 : Res v2 = Res v2) by auto.
      assert (Heqw : Res w = Res w) by auto.
      specialize (IHComp _ Heqv2 _ Hw Heqw).
      specialize (R_res_val_ref H1 H); intros.
      eapply val_ref_trans; eauto.
  Qed.

  (* Behavioral Refinement *)
  Theorem Top_n_val_ref n e1 e2 :
    Top_n n e1 e2 ->
    forall ρ1 ρ2,
      wf_env ρ1 ->
      wf_env ρ2 ->
      G_n n (occurs_free e1) (occurs_free e2) ρ1 ρ2 ->
      forall j1 v1,
        bstep_fuel true ρ1 e1 j1 (Res v1) ->
        exists j2 v2,
          bstep_fuel true ρ2 e2 j2 (Res v2) /\
          val_ref v1 v2.
  Proof.
    intros.
    edestruct Top_n_R_n with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
    inv H3.
    inv H5.
    assert (wf_val v1) by (eapply bstep_wf_res in H4; eauto; inv H4; auto).
    edestruct R_n_Res_inv as [v2 [Heq HVn]]; eauto; subst.
    eexists; eexists; split; eauto.
    eapply R_n_res_val_ref; eauto.
  Qed.

End Refinement.

Section Linking.

  (* The linking preservation theorem is more general than CertiCoq's, which only links program of a single hole with a closed program. Here,
     1. e1 and e2 can contain multiple holes
     2. f can be either free or not in either e1 or e2 as long as e1 is compiled by the pipeline.
     3. x can be either free or not in e2 as long as e2 is compiled by the pipeline.
     4. w needs to be exposed *)
  Definition link f w x e1 e2 : exp :=
    Efun f w [] e1
      (Eletapp x f w [] e2).

  (* Note the following lemma is not applicable as [trans_correct] is not the top-level relation.
   * Thus, we need to show the compat lemmas for fun and letapp with [related_top] *)
  Lemma related_preserves_linking f w x e1 e2 e1' e2':
    (w \in Exposed) ->
    related e1 e2 ->
    related e1' e2' ->
    related (link f w x e1 e1') (link f w x e2 e2').
  Proof.
    unfold link.
    intros Hw He He'.
    eapply fun_compat; eauto.
    eapply letapp_compat; eauto.
  Qed.

  (* [related] is stronger than [related_top] due to [G_top] *)
  Lemma related_related_top e1 e2 :
    occurs_free e2 \subset occurs_free e1 ->
    related e1 e2 ->
    related_top e1 e2.
  Proof.
    unfold related_top, related.
    intros.
    split; auto; intros.
    eapply H0; eauto.
    eapply G_top_G; eauto.
  Qed.

  Lemma related_top_related e1 e2 :
    related_top e1 e2 ->
    related e1 e2.
  Proof.
    unfold related_top, related.
    intros.
  Abort.

  Lemma G_G_top i Γ1 ρ1 Γ2 ρ2 :
    G i Γ1 ρ1 ρ2 ->
    Γ2 \subset Γ1 ->
    wf_env ρ1 ->
    wf_env ρ2 ->
    G_top i Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold G, G_top.
    intros.
    repeat (split; auto); intros.
  Abort.

  (* Environment Lemmas *)
  Lemma G_top_get_list {i Γ1 ρ1 Γ2 ρ2} :
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    forall xs,
      (FromList xs) \subset Γ1 ->
      exists vs1 vs2,
        get_list xs ρ1 = Some vs1 /\
        get_list xs ρ2 = Some vs2 /\
        Forall2 (V i) vs1 vs2.
  Proof.
    unfold G_top.
    intros HG xs.
    destruct HG as [Hr1 [Hr2 [HS HG]]].
    induction xs; simpl; intros.
    - eexists; eexists; repeat split; eauto.
    - rewrite FromList_cons in H.
      edestruct IHxs as [vs1 [vs2 [Heqvs1 [Heqvs2 HVs]]]].
      eapply Included_trans; eauto.
      apply Included_Union_r.

      destruct (HG a) as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]].
      unfold Ensembles.Included, Ensembles.In, FromList in *.
      eapply H; eauto.
      apply Union_introl; auto.

      rewrite Heqv1.
      rewrite Heqvs1.
      rewrite Heqv2.
      rewrite Heqvs2.
      exists (v1 :: vs1), (v2 :: vs2); split; auto.
  Qed.

  Lemma G_top_set {i Γ1 ρ1 Γ2 ρ2}:
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    forall {x v1 v2},
      wf_val v1 ->
      wf_val v2 ->
      exposed v1 ->
      V i v1 v2 ->
      G_top i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
  Proof.
    unfold G_top.
    intros.
    destruct H as [Hr1 [Hr2 [HS HG]]].
    split.
    eapply wf_env_set; eauto.

    split.
    eapply wf_env_set; eauto.

    split.
    apply Included_Union_compat; auto.
    apply Included_refl.

    intros.
    destruct (M.elt_eq x0 x); subst.
    - repeat rewrite M.gss.
      eexists; repeat split; eauto.
    - repeat (rewrite M.gso; auto).
      inv H.
      inv H4; contradiction.
      eapply HG; eauto.
  Qed.

  Lemma G_top_set_lists {i Γ1 ρ1 Γ2 ρ2}:
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    forall {xs vs1 vs2 ρ3 ρ4 w},
      Forall2 (V i) vs1 vs2 ->
      (w \in Exposed) ->
      Forall exposed vs1 ->
      Forall exposed vs2 ->
      set_lists xs vs1 ρ1 = Some ρ3 ->
      set_lists xs vs2 ρ2 = Some ρ4 ->
      G_top i (FromList xs :|: Γ1) ρ3 (FromList xs :|: Γ2) ρ4.
  Proof.
    unfold G_top.
    intros HG xs.
    induction xs; simpl; intros.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      inv H3; inv H4.
      destruct HG as [Hr1 [Hr2 [HS HG]]].
      repeat (split; auto); intros.
      apply Included_Union_compat; auto.
      apply Included_refl.
      inv H3.
      inv H4.
      eapply HG; eauto.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
      destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
      inv H; inv H1; inv H2; inv H3; inv H4.
      destruct HG as [Hr1 [Hr2 [HS HG]]].

      split.
      eapply wf_env_set; eauto.
      eapply (wf_env_set_lists _ Hr1 vs1 xs); eauto.
      eapply V_wf_val_Forall_l; eauto.
      eapply V_wf_val_l; eauto.

      split.
      eapply wf_env_set; eauto.
      eapply (wf_env_set_lists _ Hr2 vs2 xs); eauto.
      eapply V_wf_val_Forall_r; eauto.
      eapply V_wf_val_r; eauto.

      split.
      apply Included_Union_compat; auto.
      apply Included_refl.

      intros.
      destruct (M.elt_eq x a); subst.
      + repeat rewrite M.gss in *; eauto.
        eexists; eexists; split; eauto.
      + repeat (rewrite M.gso in *; auto).
        edestruct IHxs as [v1' [v2' [Heqv1' [Heqv2' [Hex HV']]]]]; eauto.
        eapply not_In_cons_Union; eauto.
  Qed.

  (* Monotonicity Lemma *)
  Lemma G_top_mono {Γ1 Γ2 ρ1 ρ2} i j:
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    j <= i ->
    G_top j Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold G_top.
    intros.
    destruct H as [Hr1 [Hr2 [HS HG]]].
    repeat (split; auto); intros.
    edestruct HG as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto.
    eexists; eexists; repeat split; eauto.
    apply V_mono with i; eauto.
  Qed.

  (* Compatibility Lemmas *)
  Lemma Vfun_V e e' :
    related_top e e' ->
    forall i f xs Γ1 Γ2 ρ1 ρ2 w,
      (w \in Exposed) ->
      wf_env ρ1 ->
      wf_env ρ2 ->
      G_top i Γ1 ρ1 Γ2 ρ2 ->
      occurs_free e \subset (FromList xs :|: (f |: Γ1)) ->
      occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
      V i (Tag w (Vfun f ρ1 xs e)) (Tag w (Vfun f ρ2 xs e')).
  Proof.
    unfold related_top.
    intros [HS He] i.
    induction i; simpl; intros; auto;
      repeat (split; auto); intros;
      destruct (exposed_reflect w); try contradiction.

    apply (He (i - (i - j)) ρ3 ρ4); auto.
    eapply G_top_subset with (Γ1 := FromList xs :|: (f |: Γ1)) (Γ2 := FromList xs :|: (f |: Γ2)); eauto.
    eapply G_top_set_lists; eauto.
    eapply G_top_set; eauto.
    eapply G_top_mono; eauto; try lia.
    apply V_mono with i; try lia.
    eapply IHi with (Γ2 := Γ2); eauto.
    apply G_top_mono with (S i); eauto; lia.
    destruct H6; auto.
    destruct H6; auto.
  Qed.

  Lemma fun_compat_top e e' k k' f w xs :
    (w \in Exposed) ->
    related_top e e' ->
    related_top k k' ->
    related_top (Efun f w xs e k) (Efun f w xs e' k').
  Proof.
    unfold related_top, E, E'.
    intros.
    destruct H0.
    destruct H1.
    split; intros.
    eapply free_fun_compat; eauto.

    pose proof H4 as HG.
    destruct H4 as [Hr1 [Hr2 [HS HG']]].
    inv H6.
    - exists 0, OOT; split; simpl; eauto.
    - inv H4.
      edestruct (H3 (i - 1) (M.set f (Tag w (Vfun f ρ1 xs e)) ρ1) (M.set f (Tag w (Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + eapply G_top_subset with (Γ1 := (f |: (occurs_free (Efun f w xs e k)))) (Γ2 := (f |: (occurs_free (Efun f w xs e' k')))); eauto.
        * eapply G_top_set; eauto.
          eapply G_top_mono; eauto; try lia.
          eapply Vfun_V with (Γ1 := (occurs_free (Efun f w xs e k))) (Γ2 := (occurs_free (Efun f w xs e' k'))); eauto.
          -- unfold related_top.
             split; auto.
          -- eapply G_top_mono; eauto; try lia.
          -- eapply free_fun_e_subset; eauto.
          -- eapply free_fun_e_subset; eauto.
        * eapply free_fun_k_subset; eauto.
      + exists (S j2), r2; split; auto.
        * constructor; auto.
          eapply R_exposed; eauto.
        * apply R_mono with ((i - 1) - c); try lia; auto.
  Qed.

  Lemma letapp_compat_top k k' w xs x f :
    (w \in Exposed) ->
    related_top k k' ->
    related_top (Eletapp x f w xs k) (Eletapp x f w xs k').
  Proof.
    unfold related_top, E, E'.
    intros.
    destruct H0.
    split; intros.
    eapply free_letapp_compat; eauto.

    pose proof H2 as HG.
    destruct H2 as [Hr1 [Hr2 [HS HG']]].
    inv H4.
    - exists 0, OOT; split; simpl; auto.
    - inv H2.
      + edestruct (HG' f) as [fv1 [fv2 [Heqfv1 [Heqfv2 [Hexfv HVf]]]]]; eauto.
        rewrite Heqfv1 in H10; inv H10.
        destruct fv2.
        destruct i.
        inv H3.
        simpl in HVf.
        destruct HVf as [Hfv1 [Hfv2 [Hw HV]]]; subst.
        destruct v0; try contradiction.
        destruct HV as [Hlen HV].

        edestruct (G_top_get_list HG xs) as [vs1 [vs2 [Heqvs1 [Heqvs2 HVvs]]]].
        eapply free_letapp_xs_subset; eauto.

        rewrite Heqvs1 in H11; inv H11.

        destruct (set_lists_length3 (M.set v0 (Tag w0 (Vfun v0 t l e0)) t) l vs2) as [ρ4 Heqρ4].
        unfold wval in *.
        rewrite <- (Forall2_length _ _ _ HVvs).
        rewrite <- (set_lists_length_eq _ _ _ _ H14); auto.

        unfold E' in HV.
        edestruct (HV i vs vs2 ρ'' ρ4) with (j1 := c0) as [j2 [r2 [He0 HR]]]; eauto; try lia.
        * intros.
          destruct H16; auto.
          split; auto.
          eapply V_exposed_Forall; eauto.
        * eapply V_mono_Forall; eauto; lia.
        * destruct r2; simpl in HR; try contradiction.
          edestruct (H1 (i - c0) (M.set x v ρ1) (M.set x w ρ2)) with (j1 := c') as [j3 [r3 [He1 HR']]]; eauto; try lia.
          eapply G_top_subset with (Γ1 := x |: (occurs_free (Eletapp x f w0 xs k))) (Γ2 := x |: (occurs_free (Eletapp x f w0 xs k'))); eauto.
          eapply G_top_set; eauto.
          eapply G_top_mono; eauto; lia.
          -- eapply bstep_fuel_wf_res in H15; eauto; inv H15; auto.
             eapply (wf_env_set_lists (M.set f' (Tag w0 (Vfun f' ρ' xs' e)) ρ')) with (xs := xs') (vs := vs); eauto.
             eapply wf_env_set; eauto.
             inv Hfv1.
             inv H9; auto.
             eapply V_wf_val_Forall_l; eauto.
          -- eapply bstep_fuel_wf_res in He0; eauto; inv He0; auto.
             eapply (wf_env_set_lists (M.set v0 (Tag w0 (Vfun v0 t l e0)) t)) with (xs := l) (vs := vs2); eauto.
             eapply wf_env_set; eauto.
             inv Hfv2.
             inv H9; auto.
             eapply V_wf_val_Forall_r; eauto.
          -- destruct H16; auto.
          -- eapply V_mono; eauto; try lia.
          -- eapply free_letapp_k_subset; eauto.
          -- exists (S (j2 + j3)), r3; split; eauto.
             2 : { eapply R_mono; eauto; lia. }

             constructor; auto.
             econstructor; eauto.
             intros.
             destruct H16; auto.
             split.
             eapply V_exposed_Forall; eauto.
             eapply V_exposed; eauto.
             inv He1; auto.
      + eexists; exists OOT; split; simpl; eauto.
  Qed.

  (* Linking Preservation for [related_top] *)
  Theorem related_top_preserves_linking f w x e1 e2 e1' e2':
    (w \in Exposed) ->
    related_top e1 e2 ->
    related_top e1' e2' ->
    related_top (link f w x e1 e1') (link f w x e2 e2').
  Proof.
    unfold link.
    intros.
    eapply fun_compat_top; eauto.
    eapply letapp_compat_top; eauto.
  Qed.

  Lemma Top_n_preserves_linking_l f w x n e1 e2 e1' :
    (w \in Exposed) ->
    Top_n n e1 e2 ->
    Top_n n (link f w x e1 e1') (link f w x e2 e1').
  Proof.
    intros Hw Hrel. revert e1'.
    induction Hrel; simpl; intros.
    - eapply Top_n_refl; eauto.
    - assert (He1' : related_top e1' e1') by (eapply refl_related_top; eauto).
      econstructor; eauto.
      eapply related_top_preserves_linking; eauto.
      eapply IHHrel; eauto.
  Qed.

  Lemma Top_n_preserves_linking_r f w x n e1' e2' e1 :
    (w \in Exposed) ->
    Top_n n e1' e2' ->
    Top_n n (link f w x e1 e1') (link f w x e1 e2').
  Proof.
    intros Hw Hrel. revert e1.
    induction Hrel; simpl; intros.
    - eapply Top_n_refl; eauto.
    - assert (He1' : related_top e1 e1) by (eapply refl_related_top; eauto).
      econstructor; eauto.
      eapply related_top_preserves_linking; eauto.
      eapply IHHrel; eauto.
  Qed.

  (* Linking Preservation *)
  Theorem Top_n_preserves_linking f w x n m e1 e2 e1' e2' :
    (w \in Exposed) ->
    Top_n n e1 e2 ->
    Top_n m e1' e2' ->
    Top_n (n + m) (link f w x e1 e1') (link f w x e2 e2').
  Proof.
    intros.
    eapply Top_n_trans; eauto.
    - eapply Top_n_preserves_linking_l; eauto.
    - eapply Top_n_preserves_linking_r; eauto.
  Qed.

End Linking.

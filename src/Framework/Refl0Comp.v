From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF0 Refl0.

(* Compositionality of The Reflexive Pipeline Based on [Refl0.related_top] *)

(* Adequacy / Preservation of Termination *)
(* Behavioral Refinement *)
(* Linking Preservation *)

Section RelComp.

  (* TODO: refactor *)

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

  Definition Top_n := Comp related_top.

  Definition V_n := Comp (fun v1 v2 => forall k, V k v1 v2).

  Definition R_n := Comp (fun r1 r2 => forall k, R k r1 r2).

  Definition G_n n Γ1 Γ2 := Comp (fun ρ1 ρ2 => forall k, G_top k Γ1 ρ1 Γ2 ρ2) n.

  Lemma V_n_refl n v :
    V_n n v v.
  Proof.
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

  Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4 :
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    Γ3 \subset Γ1 ->
    Γ4 \subset Γ3 ->
    G_top i Γ3 ρ1 Γ4 ρ2.
  Proof.
    unfold G_top.
    intros.
    destruct H as [Hs HG].
    repeat (split; auto).
    eapply G_subset; eauto.
  Qed.

  Lemma G_n_subset n Γ1 Γ2 ρ2 Γ3 ρ3 :
    G_n n Γ1 Γ3 ρ2 ρ3 ->
    Γ2 \subset Γ1 ->
    Γ3 \subset Γ2 ->
    G_n n Γ2 Γ3 ρ2 ρ3.
  Proof.
    intros H.
    revert Γ2.
    induction H; simpl; intros.
    - constructor.
    - econstructor.
      + intros.
        eapply G_top_subset; eauto.
      + eapply IHComp; eauto.
  Qed.

End RelComp.

Section Adequacy.

  Lemma Top_n_R_n n e1 e2:
    Top_n n e1 e2 ->
    forall ρ1 ρ2,
      G_n n (occurs_free e1) (occurs_free e2) ρ1 ρ2 ->
      forall j1 r1,
        bstep_fuel ρ1 e1 j1 r1 ->
        exists j2 r2,
          bstep_fuel ρ2 e2 j2 r2 /\
          R_n n r1 r2.
  Proof.
    intros Hrel.
    induction Hrel; intros.
    - inv H.
      eexists; eexists; split; eauto.
      econstructor.
    - inv H0.
      rename c4 into ρ1'.
      unfold G_n in *.
      unfold related_top in H.
      destruct H.
      unfold E, E' in *.
      pose proof (H3 0) as HG0.
      destruct HG0 as [HS _].

      edestruct (H0 j1 ρ1 ρ1') with (j1 := j1) as [j2 [r2 [Hr2 HR]]]; eauto.
      + destruct (H3 j1) as [_ HG].
        repeat (split; auto).
      + edestruct (IHHrel ρ1' ρ2) as [j3 [r3 [Hr3 HR']]]; eauto.
        eapply G_n_subset; eauto.
        eapply Top_n_subset; eauto.

        eexists; eexists; split; eauto.
        econstructor; eauto.
        intros.
        edestruct (H0 (k + j1) ρ1 ρ1') with (j1 := j1) as [j4 [r4 [Hr4 HR'']]]; eauto; try lia.
        * specialize (H3 (k + j1)).
          eapply G_top_subset; eauto.
          apply Included_refl.
        * unfold R, R' in *.
          destruct r1; destruct r4; destruct r2; try contradiction; auto.
          edestruct (bstep_fuel_deterministic v1 v0 Hr2 Hr4); subst; eauto.
          eapply V_mono; eauto; try lia.
  Qed.

  (* Termination Perservation *)
  Theorem Top_n_preserves_termination n e1 e2 :
    Top_n n e1 e2 ->
    forall ρ1 ρ2,
      G_n n (occurs_free e1) (occurs_free e2) ρ1 ρ2 ->
      forall j1 v1,
        bstep_fuel ρ1 e1 j1 (Res v1) ->
        exists j2 v2,
          bstep_fuel ρ2 e2 j2 (Res v2) /\
          V_n n v1 v2.
  Proof.
    intros.
    edestruct Top_n_R_n with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
    edestruct R_n_Res_inv as [v2 [Heq HVn]]; eauto; subst.
    eexists; eexists; split; eauto.
  Qed.

End Adequacy.

Section Refinement.

  Inductive val_ref : val -> val -> Prop :=
  | Ref_Vfun :
    forall f1 ρ1 xs1 e1 f2 ρ2 xs2 e2,
      val_ref (Vfun f1 ρ1 xs1 e1) (Vfun f2 ρ2 xs2 e2)

  | Ref_Vconstr_nil :
    forall c,
      val_ref (Vconstr c []) (Vconstr c [])

  | Ref_Vconstr_cons :
    forall c v1 v2 vs1 vs2,
      val_ref v1 v2 ->
      val_ref (Vconstr c vs1) (Vconstr c vs2) ->
      val_ref (Vconstr c (v1 :: vs1)) (Vconstr c (v2 :: vs2)).

  Hint Constructors val_ref : core.

  Lemma val_ref_Vconstr c vs1 vs2 :
    Forall2 val_ref vs1 vs2 ->
    val_ref (Vconstr c vs1) (Vconstr c vs2).
  Proof.
    intros.
    induction H; simpl; auto.
  Qed.

  Lemma val_ref_refl v :
    val_ref v v.
  Proof.
    induction v using val_ind'; auto.
  Qed.

  Lemma val_ref_trans : Transitive val_ref.
  Proof.
    intros v1 v2 v3 H.
    revert v3.
    induction H; simpl; intros; inv H; auto.
    - inv H1; auto.
    - inv H1.
      inv H5; auto.
    - inv H1; auto.
  Qed.

  Lemma V_val_ref {v1 v2} :
    (forall i, V i v1 v2) ->
    val_ref v1 v2.
  Proof.
    revert v2.
    induction v1 using val_ind'; intros; simpl.
    - specialize (H 0).
      destruct v2; simpl in *; try contradiction.
      destruct H as [Hc Hlen]; subst.
      symmetry in Hlen.
      apply length_zero_iff_nil in Hlen; subst; auto.
    - destruct v2.
      + specialize (H 0); simpl in *; contradiction.
      + destruct l0;
          pose proof (H 1) as H1; simpl in *;
          inv H1; subst;
          inv H2.
        clear H4 H6.

        assert (HV' : forall i, V i v1 v /\ V i (Vconstr c l) (Vconstr c l0)).
        {
          intros.
          specialize (H (S i)).
          destruct i; simpl in *;
            destruct H as [_ HFV];
            inv HFV;
            destruct v1; destruct v; try contradiction;
            repeat (split; auto);
            try (eapply Forall2_length; eauto);
            try (eapply V_mono_Forall with (S i); eauto).
        }

        assert (HV0 : forall i, V i v1 v) by (intros; destruct (HV' i); auto).
        assert (HV1 : forall i, V i (Vconstr c l) (Vconstr c l0)) by (intros; destruct (HV' i); auto).

        auto.
    - specialize (H 0); simpl in *.
      destruct v2; try contradiction; auto.
  Qed.

  Lemma R_res_val_ref {v1 v2} :
    (forall i, R i (Res v1) (Res v2)) ->
    val_ref v1 v2.
  Proof.
    intros; eapply V_val_ref; eauto.
  Qed.

  Lemma R_n_res_val_ref {n v1 v2} :
    R_n n (Res v1) (Res v2) ->
    val_ref v1 v2.
  Proof.
    intros.
    remember (Res v1) as r1.
    remember (Res v2) as r2.
    generalize dependent v1.
    generalize dependent v2.
    induction H; simpl; intros; subst.
    - inv Heqr1; auto.
      apply val_ref_refl; auto.
    - pose proof (H 0) as HR0.
      destruct c2; simpl in HR0; try contradiction.
      assert (Heqv : Res v = Res v) by auto.
      assert (Heqv2 : Res v2 = Res v2) by auto.
      specialize (IHComp _ Heqv2 _ Heqv).
      specialize (R_res_val_ref H); intros.
      eapply val_ref_trans; eauto.
  Qed.

  (* Termination Refinement *)
  Theorem Top_n_val_ref n e1 e2 :
    Top_n n e1 e2 ->
    forall ρ1 ρ2,
      G_n n (occurs_free e1) (occurs_free e2) ρ1 ρ2 ->
      forall j1 v1,
        bstep_fuel ρ1 e1 j1 (Res v1) ->
        exists j2 v2,
          bstep_fuel ρ2 e2 j2 (Res v2) /\
          val_ref v1 v2.
  Proof.
    intros.
    edestruct Top_n_R_n with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
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
  Definition link f x e1 e2 : exp :=
    Efun f [] e1
      (Eletapp x f [] e2).

  Lemma related_preserves_linking f x e1 e2 e1' e2':
    related e1 e2 ->
    related e1' e2' ->
    related (link f x e1 e1') (link f x e2 e2').
  Proof.
    unfold link.
    intros He He'.
    eapply fun_compat; eauto.
    eapply letapp_compat; eauto.
  Qed.

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

  Lemma G_G_top i Γ1 ρ1 Γ2 ρ2 :
    G i Γ1 ρ1 ρ2 ->
    Γ2 \subset Γ1 ->
    G_top i Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold G, G_top.
    intros.
    repeat (split; auto); intros.
  Qed.

  Lemma related_top_related e1 e2 :
    related_top e1 e2 ->
    related e1 e2.
  Proof.
    unfold related_top, related.
    intros.
    destruct H as [HS H].
    eapply H; eauto.
    eapply G_G_top; eauto.
  Qed.

  Lemma free_fun_compat e' e k' k f xs :
    occurs_free e' \subset occurs_free e ->
    occurs_free k' \subset occurs_free k ->
    occurs_free (Efun f xs e' k') \subset occurs_free (Efun f xs e k).
  Proof.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H1; auto.
  Qed.

  Lemma free_letapp_compat k' k x f xs :
    occurs_free k' \subset occurs_free k ->
    occurs_free (Eletapp x f xs k') \subset occurs_free (Eletapp x f xs k).
  Proof.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H0; auto.
  Qed.

  (* Linking Preservation for [related_top] *)
  Theorem related_top_preserves_linking f x e1 e2 e1' e2':
    related_top e1 e2 ->
    related_top e1' e2' ->
    related_top (link f x e1 e1') (link f x e2 e2').
  Proof.
    unfold link.
    intros.
    apply related_related_top.
    - unfold related_top in *.
      destruct H as [HS _].
      destruct H0 as [HS0 _].
      eapply free_fun_compat; eauto.
      eapply free_letapp_compat; eauto.
    - apply related_top_related in H.
      apply related_top_related in H0.
      apply related_preserves_linking; auto.
  Qed.

  Lemma Top_n_preserves_linking_l f x n e1 e2 e1' :
    Top_n n e1 e2 ->
    Top_n n (link f x e1 e1') (link f x e2 e1').
  Proof.
    intros Hrel. revert e1'.
    induction Hrel; simpl; intros.
    - eapply Top_n_refl; eauto.
    - assert (He1' : related_top e1' e1') by (eapply refl_related_top; eauto).
      econstructor; eauto.
      eapply related_top_preserves_linking; eauto.
      eapply IHHrel; eauto.
  Qed.

  Lemma Top_n_preserves_linking_r f x n e1' e2' e1 :
    Top_n n e1' e2' ->
    Top_n n (link f x e1 e1') (link f x e1 e2').
  Proof.
    intros Hrel. revert e1.
    induction Hrel; simpl; intros.
    - eapply Top_n_refl; eauto.
    - assert (He1' : related_top e1 e1) by (eapply refl_related_top; eauto).
      econstructor; eauto.
      eapply related_top_preserves_linking; eauto.
      eapply IHHrel; eauto.
  Qed.

  (* Linking Preservation *)
  Theorem Top_n_preserves_linking f x n m e1 e2 e1' e2' :
    Top_n n e1 e2 ->
    Top_n m e1' e2' ->
    Top_n (n + m) (link f x e1 e1') (link f x e2 e2').
  Proof.
    intros.
    eapply Top_n_trans; eauto.
    - eapply Top_n_preserves_linking_l; eauto.
    - eapply Top_n_preserves_linking_r; eauto.
  Qed.

End Linking.

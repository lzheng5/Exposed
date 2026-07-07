From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util RelComp.
From LambdaANF Require Import ANF Refl.

(* Compositionality of The Reflexive Pipeline Based on [Refl0.related_top] *)

(* Adequacy / Preservation of Termination *)
(* Behavioral Refinement *)
(* Linking Preservation *)

Section Refl0Comp.

  Definition Top_n := Comp related_top.

  Definition V_n := Comp (fun v1 v2 => forall k, V k v1 v2).

  Definition R_n := Comp (fun r1 r2 => forall k, R k r1 r2).

  Definition G_n n Γ1 := Comp (fun ρ1 ρ2 => forall k, G_top k Γ1 ρ1 ρ2) n.

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

  Lemma G_n_subset n Γ1 Γ2 ρ1 ρ2 :
    G_n n Γ1 ρ1 ρ2 ->
    Γ2 \subset Γ1 ->
    G_n n Γ2 ρ1 ρ2.
  Proof.
    intros H.
    induction H; simpl; intros.
    - constructor.
    - econstructor.
      + intros.
        eapply G_top_subset; eauto.
      + eapply IHComp; eauto.
  Qed.

End Refl0Comp.

Section Adequacy.

  Lemma Top_n_adequcy n e1 e2:
    Top_n n e1 e2 ->
    forall ρ1 ρ2,
      G_n n (occurs_free e1) ρ1 ρ2 ->
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

      edestruct (H0 j1 ρ1 ρ1') with (j1 := j1) as [j2 [r2 [Hr2 HR]]]; eauto.
      edestruct (IHHrel ρ1' ρ2) as [j3 [r3 [Hr3 HR']]]; eauto.
      eapply G_n_subset; eauto.

      eexists; eexists; split; eauto.
      econstructor; eauto.
      intros.
      edestruct (H0 (k + j1) ρ1 ρ1') with (j1 := j1) as [j4 [r4 [Hr4 HR'']]]; eauto; try lia.
      unfold R, R' in *.
      destruct r1; destruct r4; destruct r2; try contradiction; auto.
      edestruct (bstep_fuel_deterministic v1 v0 Hr2 Hr4); subst; eauto.
      eapply V_mono; eauto; try lia.
  Qed.

  (* Termination Preservation *)
  Theorem Top_n_preserves_termination n e1 e2 :
    Top_n n e1 e2 ->
    forall ρ1 ρ2,
      G_n n (occurs_free e1) ρ1 ρ2 ->
      forall j1 v1,
        bstep_fuel ρ1 e1 j1 (Res v1) ->
        exists j2 v2,
          bstep_fuel ρ2 e2 j2 (Res v2) /\
          V_n n v1 v2.
  Proof.
    intros.
    edestruct Top_n_adequcy with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
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

  (* Behavioral Refinement *)
  Theorem Top_n_val_ref n e1 e2 :
    Top_n n e1 e2 ->
    forall ρ1 ρ2,
      G_n n (occurs_free e1) ρ1 ρ2 ->
      forall j1 v1,
        bstep_fuel ρ1 e1 j1 (Res v1) ->
        exists j2 v2,
          bstep_fuel ρ2 e2 j2 (Res v2) /\
          val_ref v1 v2.
  Proof.
    intros.
    edestruct Top_n_adequcy with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
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
     4. w needs to be exposed

     Print link.
   *)

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

  (* [related] is strictly stronger than [related_top] *)
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
    destruct H as [HS H].
    eapply H; eauto.
  Abort.

  (* Environment Lemmas *)
  Lemma G_top_get {i Γ ρ1 ρ2}:
  G_top i Γ ρ1 ρ2 ->
  forall x v1,
    (x \in Γ) ->
    M.get x ρ1 = Some v1 ->
    exists v2,
      M.get x ρ2 = Some v2 /\
        V i v1 v2.
  Proof.
    unfold G_top.
    intros HG; intros.
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
      V i v1 v2 ->
      G_top i (x |: Γ1) (M.set x v1 ρ1) (M.set x v2 ρ2).
  Proof.
    unfold G_top.
    intros.
    destruct (M.elt_eq x0 x); subst.
    - repeat rewrite M.gss.
      fcrush.
    - repeat (rewrite M.gso; auto).
      fcrush.
  Qed.

  Lemma G_top_set_lists {i Γ1 ρ1 ρ2}:
    G_top i Γ1 ρ1 ρ2 ->
    forall {xs vs1 vs2 ρ3 ρ4},
      Forall2 (V i) vs1 vs2 ->
      set_lists xs vs1 ρ1 = Some ρ3 ->
      set_lists xs vs2 ρ2 = Some ρ4 ->
      G_top i (FromList xs :|: Γ1) ρ3 ρ4.
  Proof.
    intros HG xs.
    induction xs; simpl; intros.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      invc.
      unfold G_top.
      fcrush.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
      destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
      inv H; invc.
      eapply G_top_subset; eauto.
      eapply G_top_set; eauto.
      normalize_sets.
      rewrite Union_assoc; eauto.
      fcrush.
  Qed.

  (* Monotonicity Lemma *)
  Lemma G_top_mono {Γ1 ρ1 ρ2} i j:
    G_top i Γ1 ρ1 ρ2 ->
    j <= i ->
    G_top j Γ1 ρ1 ρ2.
  Proof.
    unfold G_top.
    intros.
    edestruct H as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto.
    eexists; eexists; repeat split; eauto.
    apply V_mono with i; eauto.
  Qed.

  (* Compatibility Lemmas *)
  Lemma Vfun_V e e' :
    related_top e e' ->
    forall i f xs Γ1 ρ1 ρ2,
      G_top i Γ1 ρ1 ρ2 ->
      occurs_free e \subset (FromList xs :|: (f |: Γ1)) ->
      V i (Vfun f ρ1 xs e) (Vfun f ρ2 xs e').
  Proof.
    unfold related_top.
    intros [HS He] i.
    induction i; simpl; intros; auto;
      repeat (split; auto); intros.

    apply (He (i - (i - j)) ρ3 ρ4); auto.
    eapply G_top_subset with (Γ1 := FromList xs :|: (f |: Γ1)); eauto.
    eapply G_top_set_lists; eauto.
    eapply G_top_set; eauto.
    eapply G_top_mono; eauto; try lia.
    apply V_mono with i; try lia.
    eapply IHi; eauto.
    apply G_top_mono with (S i); eauto; lia.
  Qed.

  Lemma fun_compat_top e e' k k' f xs :
    related_top e e' ->
    related_top k k' ->
    related_top (Efun f xs e k) (Efun f xs e' k').
  Proof.
    unfold related_top, E, E'.
    intros [HSe He] [HSk Hk].
    split; intros.
    eapply free_fun_compat; eauto.

    pose proof H as HG.
    inv H1.
    - fcrush.
    - inv H2.
      edestruct (Hk (i - 1) (M.set f (Vfun f ρ1 xs e) ρ1) (M.set f (Vfun f ρ2 xs e') ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + eapply G_top_subset with (Γ1 := (f |: (occurs_free (Efun f xs e k)))); eauto.
        * eapply G_top_set; eauto.
          eapply G_top_mono; eauto; try lia.
          eapply Vfun_V with (Γ1 := (occurs_free (Efun f xs e k))); eauto.
          -- unfold related_top.
             split; auto.
          -- eapply G_top_mono; eauto; try lia.
          -- eapply free_fun_e_subset; eauto.
        * eapply free_fun_k_subset; eauto.
      + exists (S j2), r2; split; auto.
        apply R_mono with ((i - 1) - c); try lia; auto.
  Qed.

  Lemma letapp_compat_top k k' xs x f :
    related_top k k' ->
    related_top (Eletapp x f xs k) (Eletapp x f xs k').
  Proof.
    unfold related_top, E, E'.
    intros [HSk Hk].
    split; intros.
    eapply free_letapp_compat; eauto.

    pose proof H as HG.
    inv H1.
    - fcrush.
    - inv H2.
      2 : { fcrush. }
      edestruct (G_top_get HG f) as [fv2 [Heqfv2 HVf]]; eauto.
      destruct fv2.
      2 : { destruct i; fcrush. }
      destruct i.
      fcrush.
      simpl in HVf.
      destruct HVf as [Hlen HV].

      edestruct (G_top_get_list HG xs) as [vs2 [Heqvs2 HVvs]]; eauto.
      eapply free_letapp_xs_subset; eauto.

      destruct (set_lists_length3 (M.set v0 (Vfun v0 t l e0) t) l vs2) as [ρ4 Heqρ4].
      rewrite <- (Forall2_length _ _ _ HVvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H10); auto.

      unfold E' in HV.
      edestruct (HV i vs vs2 ρ'' ρ4) with (j1 := c0) as [j2 [r2 [He0 HR]]]; eauto; try lia.
      + eapply V_mono_Forall; eauto; lia.
      + destruct r2; simpl in HR; try contradiction.
        edestruct (Hk (i - c0) (M.set x v ρ1) (M.set x v1 ρ2)) with (j1 := c') as [j3 [r3 [He1 HR']]]; eauto; try lia.
        eapply G_top_subset with (Γ1 := x |: (occurs_free (Eletapp x f xs k))); eauto.
        eapply G_top_set; eauto.
        eapply G_top_mono; eauto; lia.

        * eapply V_mono; eauto; try lia.
        * eapply free_letapp_k_subset; eauto.
        * exists (S (j2 + j3)), r3; split; eauto.
          eapply R_mono; eauto; lia.
  Qed.

  (* Linking Preservation for [related_top] *)
  Theorem related_top_preserves_linking f x e1 e2 e1' e2':
    related_top e1 e2 ->
    related_top e1' e2' ->
    related_top (link f x e1 e1') (link f x e2 e2').
  Proof.
    unfold link.
    intros.
    eapply fun_compat_top; eauto.
    eapply letapp_compat_top; eauto.
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

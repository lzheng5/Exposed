From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util RelComp.
From LambdaANF Require Import ANF ANFLex Util Tactics ReflLex.

(* Compositionality of The Reflexive Pipeline Based on [related_top] *)

(* Adequacy / Preservation of Termination *)
(* Behavioral Refinement *)
(* Linking Preservation *)

Section Comp.

  Definition Top_n := Comp related_top.

  Definition V_n := Comp (fun v1 v2 => forall k, V k v1 v2).

  Definition R_n := Comp (fun r1 r2 => forall k, R k r1 r2).

  Definition G_n n Γ1 := Comp (fun ρ1 ρ2 => forall k, G_top k Γ1 ρ1 ρ2) n.

  Lemma V_n_refl n v :
    V_n n v v.
  Proof.
    revert v.
    induction n; prog.
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
      rewrite V_eq in Hr.
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

  Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 :
    G_top i Γ1 ρ1 ρ2 ->
    Γ2 \subset Γ1 ->
    G_top i Γ2 ρ1 ρ2.
  Proof.
    unfold G_top.
    intros; eauto.
  Qed.

  Lemma G_n_subset n Γ1 Γ2 ρ2 ρ3 :
    G_n n Γ1 ρ2 ρ3 ->
    Γ2 \subset Γ1 ->
    G_n n Γ2 ρ2 ρ3.
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

End Comp.

Section Adequacy.

  Lemma Top_n_adequacy n e1 e2:
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
    edestruct Top_n_adequacy with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
    inv H1.
    edestruct R_n_Res_inv as [v2 [Heq HVn]]; eauto; subst.
    eexists; eexists; split; eauto.
  Qed.

End Adequacy.

Section Refinement.

  Fixpoint val_ref' (v1 v2 : val) : Prop:=
    let fix Forall2_aux vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 =>
          val_ref' v1 v2 /\ Forall2_aux vs1 vs2
        | _, _ => False
        end
    in
    match v1, v2 with
    | Vconstr c1 vs1, Vconstr c2 vs2 =>
        c1 = c2 /\ Forall2_aux vs1 vs2
    | Vfun _ _ _ _, Vfun _ _ _ _ => True
    | _, _ => False
    end.

  Definition val_ref (v1 v2 : val) : Prop:=
    match v1, v2 with
    | Vconstr c1 vs1, Vconstr c2 vs2 =>
        c1 = c2 /\ Forall2 val_ref' vs1 vs2
    | Vfun _ _ _ _, Vfun _ _ _ _ => True
    | _, _ => False
    end.

  Lemma val_ref_eq v1 v2 :
    val_ref' v1 v2 <-> val_ref v1 v2.
  Proof.
    destruct v1; destruct v2; simpl; try easy;
    split; intros H1; split; eauto.
    + destruct H1; auto.
    + destruct H1 as [Hc HF]; subst.
      revert l0 HF. induction l; intros l0 H2; destruct l0; intros; eauto; inv H2.
      constructor. easy. eauto.
    + destruct H1; auto.
    + destruct H1 as [Hc HF]; subst.
      induction HF; auto.
  Qed.

  Lemma val_ref_eq_Forall vs1 vs2 :
    Forall2 val_ref' vs1 vs2 <-> Forall2 val_ref vs1 vs2.
  Proof.
    split; intros H; induction H; simpl; auto;
      constructor; auto.
    - rewrite <- val_ref_eq; auto.
    - rewrite val_ref_eq; auto.
  Qed.

  Lemma val_ref_Vconstr c vs1 vs2 :
    Forall2 val_ref vs1 vs2 ->
    val_ref (Vconstr c vs1) (Vconstr c vs2).
  Proof.
    intros.
    induction H; simpl; auto.
    repeat (split; auto).
    constructor.
    rewrite val_ref_eq; auto.
    rewrite val_ref_eq_Forall; auto.
  Qed.

  Lemma val_ref_refl v :
    val_ref v v.
  Proof.
    induction v using val_ind''; unfold val_ref; auto.
    repeat (split; auto).
    induction H.
    constructor.
    constructor.
    rewrite val_ref_eq; auto.
    eapply IHForall.
  Qed.

  Lemma val_ref_trans :
    forall {v1 v2 v3},
      val_ref v1 v2 ->
      val_ref v2 v3 ->
      val_ref v1 v3.
  Proof.
    intros v1.
    induction v1 using val_ind''; intros v2 v3;
      destruct v2; destruct v3; intros; simpl in *; eauto; try contradiction.
    prog.
    revert l l0 H3 H2.
    induction vs; prog.
    rewrite val_ref_eq in *.
    eapply H2; eauto.
    eapply IHvs; eauto.
  Qed.

  Lemma V_val_ref {i v1 v2} :
    V i v1 v2 ->
    val_ref v1 v2.
  Proof.
    revert i v2.
    induction v1 using val_ind''; prog.
    - constructor.
    - eapply val_ref_Vconstr; eauto.
      generalize dependent l; induction vs; prog.
      eapply H2; eauto.
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
    induction H; simpl; prog.
    - inv Heqr1.
      apply val_ref_refl; auto.
    - pose proof (H 0) as HR0.
      destruct c2; simpl in HR0; try contradiction.
      apply V_val_ref in HR0.
      assert (Heqv2 : Res v2 = Res v2) by auto.
      assert (Heqv : Res v = Res v) by auto.
      specialize (IHComp _ Heqv2 _ Heqv).
      eapply val_ref_trans; eauto.
  Qed.

  (* Termination Refinement *)
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
    edestruct Top_n_adequacy with (ρ1 := ρ1) as [j2 [r2 ?]]; eauto.
    inv H2; prog.
    edestruct R_n_Res_inv as [v2 ?]; eauto; prog.
    eexists; eexists; prog; eauto.
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

  (* Note the following lemma is not applicable as [trans_correct] is not the top-level relation.
   * Thus, we need to show the compat lemmas for fun and letapp with [related_top] *)
  Lemma related_preserves_linking f x e1 e2 e1' e2':
    related e1 e2 ->
    related e1' e2' ->
    related (link f x e1 e1') (link f x e2 e2').
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

  (* Environment Lemmas *)
  Lemma G_top_get_list {i Γ1 ρ1 ρ2} :
    G_top i Γ1 ρ1 ρ2 ->
    forall xs,
      (FromList xs) \subset Γ1 ->
      exists vs1 vs2,
        get_list xs ρ1 = Some vs1 /\
        get_list xs ρ2 = Some vs2 /\
        Forall2 (V i) vs1 vs2.
  Proof.
    unfold G_top.
    induction xs; prog; simpl.
    - eexists; eexists; prog.
    - edestruct H as [v1 [v2 ?]]; prog; eauto.
      edestruct IHxs as [vs1 [vs2 ?]]; prog; eauto.
      eexists; eexists; prog.
  Qed.

  Lemma G_top_set {i Γ1 ρ1 ρ2}:
    G_top i Γ1 ρ1 ρ2 ->
    forall {x v1 v2},
      V i v1 v2 ->
      G_top i (x |: Γ1) (M.set x v1 ρ1) (M.set x v2 ρ2).
  Proof.
    unfold G_top.
    prog.
    destruct (M.elt_eq x0 x); prog.
    - eexists; eexists; prog.
    - inv H1; prog.
  Qed.

  Lemma G_top_set_lists {i Γ1 ρ1 ρ2}:
    G_top i Γ1 ρ1 ρ2 ->
    forall {xs vs1 vs2 ρ3 ρ4},
      Forall2 (V i) vs1 vs2 ->
      set_lists xs vs1 ρ1 = Some ρ3 ->
      set_lists xs vs2 ρ2 = Some ρ4 ->
      G_top i (FromList xs :|: Γ1) ρ3 ρ4.
  Proof.
    unfold G_top.
    intros HG xs.
    induction xs; prog.
    - destruct (M.elt_eq x a); prog.
      + eexists; eexists; prog.
      + eapply IHxs; eauto; prog.
        rewrite <- Union_assoc in H2.
        inv H2; prog.
  Qed.

  (* Monotonicity Lemma *)
  Lemma G_top_mono {Γ1 ρ1 ρ2} i j:
    G_top i Γ1 ρ1 ρ2 ->
    j <= i ->
    G_top j Γ1 ρ1 ρ2.
  Proof.
    unfold G_top.
    prog.
    edestruct H as [v1 [v2 ?]]; eauto; prog.
    eexists; eexists; prog; eauto.
    eapply V_mono; eauto; prog.
  Qed.

  (* Compatibility Lemmas *)
  Lemma Vfun_V e e' :
    related_top e e' ->
    forall i f xs Γ1  ρ1 ρ2,
      G_top i Γ1 ρ1 ρ2 ->
      occurs_free e \subset (FromList xs :|: (f |: Γ1)) ->
      V i (Vfun f ρ1 xs e) (Vfun f ρ2 xs e').
  Proof.
    unfold related_top.
    intros [HS He] i.
    induction i; prog.
    apply (He j ρ3 ρ4); prog.
    eapply G_top_subset with (Γ1 := FromList xs :|: (f |: Γ1)); eauto.
    eapply G_top_set_lists; eauto.
    eapply G_top_set; eauto; try (prog; fail).
    eapply G_top_mono; eauto; prog.
    eapply V_mono with i; try lia.
    eapply IHi; eauto.
    eapply G_top_mono; eauto; prog.
  Qed.

  Lemma fun_compat_top e e' k k' f xs :
    related_top e e' ->
    related_top k k' ->
    related_top (Efun f xs e k) (Efun f xs e' k').
  Proof.
    unfold related_top, E, E'.
    prog.
    {
      unfold Ensembles.Included, Ensembles.In in *; prog.
      inv H3; prog.
    }
    pose proof H4 as HG; unfold G_top in HG; prog.
    inv H5; prog.
    - exists 0, OOT; prog.
    - edestruct (H1 (i - 1) (M.set f (Vfun f ρ1 xs e) ρ1) (M.set f (Vfun f ρ2 xs e') ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 ?]]; eauto; try lia.
      + eapply G_top_subset with (Γ1 := (f |: (occurs_free (Efun f xs e k)))).
        eapply G_top_set; eauto; try (prog; fail).
        eapply G_top_mono; eauto; try lia.
        eapply Vfun_V with (Γ1 := (occurs_free (Efun f xs e k))); eauto; prog.
        unfold related_top; prog.
        eapply G_top_mono; eauto; try lia.
        eapply free_fun_e_subset; eauto.
        eapply free_fun_k_subset; eauto.
      + fcrush.
      + exists (S j2), r2.
        inv H5.
        split.
        fcrush.
        eapply R_mono; eauto; prog.
  Qed.

  Lemma letapp_compat_top k k' xs x f :
    related_top k k' ->
    related_top (Eletapp x f xs k) (Eletapp x f xs k').
  Proof.
    unfold related_top, E, E', R, R'.
    prog.
    {
      unfold Ensembles.Included, Ensembles.In in *; prog.
      inv H1; auto.
    }

    pose proof H1 as HG; unfold G_top in HG; prog.
    inv H3.
    - fcrush.
    - inv H4.
      edestruct (HG f) as [v1 [v2 ?]]; eauto; prog.
      edestruct (G_top_get_list H1 xs) as [vs1 [vs2 ?]]; prog.
      eapply free_letapp_xs_subset.
      destruct (set_lists_length3 (M.set v0 (Vfun v0 t l e0) t) l vs2) as [ρ4 ?].
      {
        rewrite <- (Forall2_length _ _ _ H10).
        rewrite <- (set_lists_length_eq _ _ _ _ H12); auto.
      }
      unfold E, E' in *.
      destruct i; prog.
      edestruct (H5 i vs1 vs2 ρ'' ρ4) with (j1 := c0) as [j2 [r2 ?]]; eauto.
      + eapply V_mono_Forall; eauto; lia.
      + lia.
      + prog.
        destruct r2; try contradiction.
        edestruct (H0 (i - c0) (M.set x v ρ1) (M.set x v1 ρ2)) with (j1 := c') as [j3 [r3 ?]]; eauto.
        * eapply G_top_subset with (Γ1 := x |: (occurs_free (Eletapp x f xs k))); eauto; prog.
          eapply G_top_set; eauto; prog.
          eapply G_top_mono; eauto; lia.
          eapply free_letapp_k_subset.
        * lia.
        * inv H16.
          destruct r1; destruct r3; try contradiction.
          fcrush.
          exists (S (j2 + j3)), (Res v3).
          split.
          fcrush.
          eapply V_mono; eauto; prog.
      + fcrush.
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

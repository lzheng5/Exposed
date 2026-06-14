From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

Require Import UntypedExposed.ANF.
Require Import UntypedExposed.Refl.

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

Definition refl_correct e1 e2 :=
  forall ex i ρ1 ρ2,
    G i (occurs_free e1) ρ1 (occurs_free e2) ρ2 ->
    E ex i ρ1 e1 ρ2 e2.

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

Lemma G_set_lists {i Γ1 ρ1 Γ2 ρ2}:
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

Lemma G_get_list {i Γ1 ρ1 Γ2 ρ2} :
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

(* Monotonicity Lemmas *)
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

(* Compatibility Lemmas *)
Lemma ret_compat x :
  refl_correct (Eret x) (Eret x).
Proof.
  unfold refl_correct, G, E, R, Ensembles.Included, Ensembles.In, Dom_map.
  intros.
  inv H1.
  - exists 0, OOT; auto.
  - inv H2.
    edestruct H as [v1 [Heqv1 [v2 [Heqv2 HV]]]]; eauto.
    rewrite Heqv1 in H5; inv H5.
    exists 1, (Res v2); split; auto.
    + constructor; auto.
      destruct ex; auto.
      eapply V_exposed_res; eauto.
    + apply V_mono with i; try lia; auto.
Qed.

Lemma prim_val_compat {x p k k'} :
  refl_correct k k' ->
  refl_correct (Eprim_val x p k) (Eprim_val x p k').
Proof.
  unfold refl_correct, E.
  intros.
  inv H2.
  - exists 0, OOT; split; simpl; auto.
  - inv H3.
    edestruct (H ex i (M.set x (Vprim p) ρ1) (M.set x (Vprim p) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk' Rr]]]; eauto; try lia.
    + eapply G_subset with (Γ2 := (x |: (occurs_free (Eprim_val x p k')))).
      eapply G_set; eauto.
      * destruct i; simpl; eauto.
      * apply Included_refl.
        apply free_prim_val_k_subset.
      * apply free_prim_val_k_subset.
    + exists (S j2), r2; split; eauto.
      * constructor; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * apply R_mono with (i - c); try lia; auto.
Qed.

Lemma Vfun_V {f xs e e'} :
  refl_correct e e' ->
  forall {i Γ1 Γ2 ρ1 ρ2} w,
    G i Γ1 ρ1 Γ2 ρ2 ->
    occurs_free e \subset (FromList xs :|: (f |: Γ1)) ->
    occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
    V i (Vfun f ρ1 w xs e) (Vfun f ρ2 w xs e').
Proof.
  unfold refl_correct.
  intros He i.
  induction i; simpl; intros; auto.
  repeat split; auto; intros.
  apply (He (exposedb w) (i - (i - j)) ρ3 ρ4); auto.
  eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))).
  eapply G_set_lists; eauto.
  eapply G_set; eauto.
  - apply G_mono with (S i); eauto; lia.
  - apply V_mono with i; try lia.
    eapply IHi with (Γ1 := Γ1) (Γ2 := Γ2); eauto.
    apply G_mono with (S i); eauto; lia.
  - auto.
  - auto.
Qed.

Lemma fun_compat {e e' k k'} f w xs :
  refl_correct e e' ->
  refl_correct k k' ->
  refl_correct (Efun f w xs e k) (Efun f w xs e' k').
Proof.
  unfold refl_correct, E.
  intros.
  inv H3.
  - exists 0, OOT; split; simpl; eauto.
  - inv H4.
    edestruct (H0 ex (i - 1) (M.set f (Vfun f ρ1 w xs e) ρ1) (M.set f (Vfun f ρ2 w xs e') ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_subset with (Γ2 := (f |: occurs_free (Efun f w xs e' k'))).
      eapply G_set; eauto.
      apply G_mono with i; eauto; lia.
      * eapply Vfun_V; eauto.
        -- apply G_mono with i; eauto; lia.
        -- apply free_fun_e_subset.
        -- apply free_fun_e_subset.
      * apply free_fun_k_subset.
      * apply free_fun_k_subset.
    + exists (S j2), r2; split; auto.
      * constructor; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma app_compat xs f w :
  refl_correct (Eapp f w xs) (Eapp f w xs).
Proof.
  unfold refl_correct, G, E.
  intros.
  inv H1.
  - exists 0, OOT; split; simpl; auto.
  - inv H2.
    unfold Ensembles.Included, Ensembles.In, Dom_map in *.
    destruct (H f) as [fv1 [Heqfv1 Hv2]]; eauto.
    rewrite Heqfv1 in H6; inv H6.
    destruct Hv2 as [fv2 [Heqfv2 HV]]; auto.
    destruct fv2.
    + destruct i.
      inv H0.
      simpl in HV.
      destruct HV as [Hw [Hlen HVv]]; subst.

      edestruct (G_get_list H xs vs) as [vs2 [Heqvs2 Vvs]]; eauto.
      {
        unfold Ensembles.Included, Ensembles.In, FromList, Dom_map.
        intros; auto.
      }
      {
        unfold Ensembles.Included, Ensembles.In, FromList, Dom_map.
        intros; auto.
      }

      destruct (set_lists_length3 (M.set v (Vfun v t w0 l e0) t) l vs2) as [ρ4 Heqρ4].
      rewrite <- (Forall2_length _ _ _ Vvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H9); auto.

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

Lemma letapp_compat {k k' w xs} x f :
  refl_correct k k' ->
  refl_correct (Eletapp x f w xs k) (Eletapp x f w xs k').
Proof.
  intros.
  specialize (app_compat xs f w); intros Ha.
  unfold refl_correct, E in *.
  intros.

  assert (HG' : G i (occurs_free (Eapp f w xs)) ρ1 (occurs_free (Eapp f w xs)) ρ2).
  {
    eapply G_subset with (Γ2 := (occurs_free (Eletapp x f w xs k'))); eauto;
      apply Included_refl;
      unfold Ensembles.Included, Ensembles.In;
      intros;
      inv H3; auto.
  }

  inv H2.
  - exists 0, OOT; split; simpl; auto.
  - inv H3.
    + destruct (Ha (exposedb w) i ρ1 ρ2) with (j1 := (S c0)) (r1 := (Res v)) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
      * constructor.
        eapply BStep_app; eauto.
        intros.
        destruct H16; auto.
        destruct (exposed_reflect w); auto.
        destruct H16; auto.
      * simpl in HR.
        destruct r2; try contradiction.
        inv Hr1.
        edestruct (H ex (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
        -- eapply G_subset with (Γ2 := (x |: (occurs_free (Eletapp x f w xs k')))).
           eapply G_set; eauto.
           apply G_mono with i; try lia; eauto.
           apply Included_refl.
           apply free_letapp_k_subset.
           apply free_letapp_k_subset.
        -- exists ((S c) + j2), r2; split.
           ++ inv H2.
              assert (Hc : (S c + j2) = S (c + j2)) by lia.
              rewrite Hc.
              constructor.
              ** eapply BStep_letapp_Res; eauto.
                 intros.
                 destruct H21; auto.
                 split; auto.
                 inv H6; auto.
              ** destruct ex; auto.
                 eapply R_exposed; eauto.
           ++ apply R_mono with (i - S c0 - c'); try lia; auto.
    + destruct (Ha (exposedb w) i ρ1 ρ2) with (j1 := (S c)) (r1 := OOT) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
      constructor; eauto.
      destruct (exposed_reflect w); auto.
      exists j2, r2.
      destruct r2; try contradiction.
      split; auto.
      inv Hr1; eauto.
      inv H2; eauto.
      constructor.
      eapply BStep_letapp_OOT; eauto.
      * intros.
        destruct H20; auto.
      * intros; auto.
Qed.

Lemma if_compat {e e' t t'} x :
  refl_correct t t' ->
  refl_correct e e' ->
  refl_correct (Eif x t e) (Eif x t' e').
Proof.
  unfold refl_correct, E, Ensembles.Included, Ensembles.In, Dom_map.
  intros Ht He. intros.
  inv H1.
  - exists 0, OOT; simpl; eauto.
  - inv H2.
    + edestruct Ht with (i := i) (j1 := c) as [j2 [r2 [Ht' Rr]]]; eauto; try lia.
      * eapply G_subset with (Γ2 := (occurs_free (Eif x t' e'))); eauto.
        apply free_if_t_subset.
        apply free_if_t_subset.
      * exists (S j2), r2; split; eauto.
        constructor; auto.
        apply BStep_if_true; auto.
        -- unfold G in H.
           edestruct H as [v1 [Heqv1 [v2 [Heqv2 HV]]]]; eauto.
           rewrite Heqv1 in H9; inv H9.
           destruct v2; try contradiction.
           destruct i; contradiction.
           destruct i; simpl in HV; subst; auto.
        -- destruct ex; auto.
           eapply R_exposed; eauto.
        -- apply R_mono with (i - c); try lia; auto.
    + edestruct He with (i := i) (j1 := c) as [j2 [r2 [Ht' Rr]]]; eauto; try lia.
      * eapply G_subset with (Γ2 := (occurs_free (Eif x t' e'))); eauto.
        apply free_if_e_subset.
        apply free_if_e_subset.
      * exists (S j2), r2; split; eauto.
        constructor; auto.
        apply BStep_if_false; auto.
        -- unfold G in H.
           edestruct H as [v1 [Heqv1 [v2 [Heqv2 HV]]]]; eauto.
           rewrite Heqv1 in H9; inv H9.
           destruct v2; try contradiction.
           destruct i; contradiction.
           destruct i; simpl in HV; subst; auto.
        -- destruct ex; auto.
           eapply R_exposed; eauto.
        -- apply R_mono with (i - c); try lia; auto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property e:
  refl_correct e e.
Proof.
  induction e.
  - apply ret_compat; auto.
  - eapply app_compat; eauto.
  - eapply letapp_compat; eauto.
  - eapply fun_compat; eauto.
  - apply prim_val_compat; auto.
  - apply if_compat; auto.
Qed.

(* Top Level *)
Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  forall x,
    (x \in Γ1 ->
     exists v1,
       M.get x ρ1 = Some v1 /\
       exposed v1) /\
    (x \in Γ2 ->
     exists v2,
       M.get x ρ2 = Some v2 /\
       exposed v2) /\
    (x \in (Γ1 :&: Γ2) ->
     exists v1 v2,
       M.get x ρ1 = Some v1 /\
       M.get x ρ2 = Some v2 /\
       V i v1 v2).

Lemma G_top_G : forall {i Γ1 ρ1 Γ2 ρ2},
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    G i Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G_top, G.
  intros.
  destruct (H x) as [H1 [H2 HG]].
  destruct H1 as [v1 [Heqv1 Hexv1]]; auto.
  eexists; split; eauto; intros.
  destruct HG as [v1' [v2 [Heqv1' [Heqv2 HV]]]].
  constructor; auto.
  rewrite Heqv1 in Heqv1'; inv Heqv1'.
  eexists; split; eauto.
Qed.

Definition refl_correct_top etop etop' :=
  forall i ρ1 ρ2,
    G_top i (occurs_free etop) ρ1 (occurs_free etop') ρ2 ->
    E true i ρ1 etop ρ2 etop'.

Theorem top {etop}:
  refl_correct_top etop etop.
Proof.
  unfold refl_correct_top.
  intros.
  specialize (fundamental_property etop);
    unfold refl_correct; intros.
  eapply H0; eauto.
  eapply G_top_G; eauto.
Qed.


(*
Theorem refl_trans {e1 e2 e3}:
  refl_correct_top e1 e2 ->
  refl_correct_top e2 e3 ->
  refl_correct_top e1 e3.
Proof.
  unfold refl_correct_top.
  unfold G_top.
  intros.
  rename ρ2 into ρ3.
  assert (
      forall ρ2,
E true i ρ1 e1 ρ2 e2 ->
E true i ρ2 e2 ρ3 e3 ->
E true i ρ1 e1 ρ3 e3
) by admit.
  eapply H2.
  - apply H.
    intros.
    specialize (H1 x).
    destruct H1.
    destruct H3.
    repeat split; trivial.
    + 
*)

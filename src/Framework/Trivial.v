From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Util ANF0 ANF W0 Annotate Erase.

(* Trivial Web Annotation With A Single Exposed Web Id *)

Module A0 := ANF0.
Module A1 := ANF.

Section Trans.

  (* Specification *)
  Inductive trans (Γ : vars) : A0.exp -> A1.exp -> Prop :=
  | Trans_ret :
    forall {x},
      (x \in Γ) ->
      trans Γ (A0.Eret x) (A1.Eret x)

  | Trans_fun :
    forall {f xs e k e' k'},
      trans (FromList xs :|: (f |: Γ)) e e' ->
      trans (f |: Γ) k k' ->
      trans Γ (A0.Efun f xs e k) (A1.Efun f w0 xs e' k')

  | Trans_app :
    forall {f xs},
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans Γ (A0.Eapp f xs) (A1.Eapp f w0 xs)

  | Trans_letapp :
    forall {x f xs k k'},
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w0 xs k')

  | Trans_constr :
    forall {x t xs k k'},
      (FromList xs \subset Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (A0.Econstr x t xs k) (A1.Econstr x w0 t xs k')

  | Trans_proj :
    forall {x y k k' n},
      (y \in Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (A0.Eproj x n y k) (A1.Eproj x w0 n y k')

  | Trans_case_nil :
    forall {x},
      (x \in Γ) ->
      trans Γ (A0.Ecase x []) (A1.Ecase x w0 [])

  | Trans_case_cons :
    forall {x e e' t cl cl'},
      (x \in Γ) ->
      trans Γ e e' ->
      trans Γ (A0.Ecase x cl) (A1.Ecase x w0 cl') ->
      trans Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x w0 ((t, e') :: cl')).

  Hint Constructors trans : core.

  Lemma trans_exp_inv {Γ e e'} :
    trans Γ e e' ->
    (A1.occurs_free e') \subset (A0.occurs_free e).
  Proof.
    unfold Ensembles.Included, Ensembles.In.
    intros H.
    induction H; simpl; intros; auto.
    - inv H0; auto.
    - inv H1; auto.
    - inv H1; auto.
    - inv H2; auto.
    - inv H1; auto.
    - inv H1; auto.
    - inv H0; auto.
    - inv H2; auto.
  Qed.

  Lemma trans_exp_weaken {Γ Γ' e e'} :
    trans Γ e e' ->
    Γ \subset Γ' ->
    trans Γ' e e'.
  Proof.
    intros H.
    revert Γ'.
    induction H; simpl; intros; auto.
    - constructor.
      + eapply IHtrans1; eauto.
        eapply Included_Union_compat; eauto.
        apply Included_refl.
        eapply Included_Union_compat; eauto.
        apply Included_refl.
      + eapply IHtrans2; eauto.
        eapply Included_Union_compat; eauto.
        apply Included_refl.
    - constructor; auto.
      eapply Included_trans; eauto.
    - constructor; auto.
      + eapply Included_trans; eauto.
      + eapply IHtrans; eauto.
        eapply Included_Union_compat; eauto.
        apply Included_refl.
    - constructor.
      + eapply Included_trans; eauto.
      + eapply IHtrans; eauto.
        eapply Included_Union_compat; eauto.
        apply Included_refl.
    - constructor; auto.
      eapply IHtrans; eauto.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
  Qed.

  Theorem trans_total :
    forall e,
      exists e',
        trans (A0.occurs_free e) e e'.
  Proof.
    intros e.
    induction e using A0.exp_ind'.
    - eexists; eauto.
    - exists (A1.Eapp x w0 xs).
      constructor; auto.
      eapply A0.free_app_xs_subset; eauto.
    - inv IHe1; inv IHe2.
      exists (A1.Efun f w0 xs x x0).
      constructor; auto.
      eapply trans_exp_weaken; eauto.
      eapply A0.free_fun_e_subset; eauto.
      eapply trans_exp_weaken; eauto.
      eapply A0.free_fun_k_subset; eauto.
    - inv IHe.
      exists (A1.Eletapp x f w0 xs x0); constructor; auto.
      eapply A0.free_letapp_xs_subset; eauto.
      eapply trans_exp_weaken; eauto.
      eapply A0.free_letapp_k_subset; eauto.
    - inv IHe.
      exists (A1.Econstr x w0 c xs x0); constructor; auto.
      eapply A0.free_constr_xs_subset; eauto.
      eapply trans_exp_weaken; eauto.
      eapply A0.free_constr_k_subset; eauto.
    - exists (A1.Ecase x w0 []); auto.
    - inv IHe; inv IHe0.
      inv H0.
      + exists (A1.Ecase x w0 ([(c, x0)])); constructor; auto.
        eapply trans_exp_weaken; eauto.
        eapply A0.free_case_hd_subset; eauto.
      + exists (A1.Ecase x w0 ((c, x0) :: (t, e') :: cl')); constructor; auto.
        eapply trans_exp_weaken; eauto.
        eapply A0.free_case_hd_subset; eauto.

        eapply trans_exp_weaken; eauto.
        eapply A0.free_case_tl_subset; eauto.
    - inv IHe.
      exists (A1.Eproj x w0 n v0 x0); constructor; auto.
      eapply trans_exp_weaken; eauto.
      eapply A0.free_proj_k_subset; eauto.
  Qed.

  Theorem trans_erase e1 e2 e1' :
    trans (A0.occurs_free e1) e1 e1' ->
    Erase.trans (A1.occurs_free e1') e1' e2 ->
    e1 = e2.
  Proof.
    intro H.
    revert e2.
    induction H; simpl; intros.
    - inv H0; auto.
    - inv H1; auto.
      erewrite IHtrans1 with (e2 := e'0); eauto.
      + erewrite IHtrans2 with (e2 := k'0); eauto.
        eapply Erase.trans_exp_strengthen; eauto.
        eapply A1.free_fun_k_subset; eauto.
      + eapply Erase.trans_exp_strengthen; eauto.
        eapply A1.free_fun_e_subset; eauto.
    - inv H1; auto.
    - inv H2; auto.
      erewrite IHtrans with (e2 := k'0); eauto.
      eapply Erase.trans_exp_strengthen; eauto.
      eapply A1.free_letapp_k_subset; eauto.
    - inv H1; auto.
      erewrite IHtrans with (e2 := k'0); eauto.
      eapply Erase.trans_exp_strengthen; eauto.
      eapply A1.free_constr_k_subset; eauto.
    - inv H1; auto.
      erewrite IHtrans with (e2 := k'0); eauto.
      eapply Erase.trans_exp_strengthen; eauto.
      eapply A1.free_proj_k_subset; eauto.
    - inv H0; auto.
    - inv H2; auto.
      erewrite IHtrans1 with (e2 := e'0); eauto.
      + assert (A0.Ecase x cl = A0.Ecase x cl'0).
        {
          erewrite IHtrans2 with (e2 := (A0.Ecase x cl'0)); eauto.
          eapply Erase.trans_exp_strengthen; eauto.
          eapply A1.free_case_tl_subset; eauto.
        }
        inv H2; auto.
      + eapply Erase.trans_exp_strengthen; eauto.
        eapply A1.free_case_hd_subset; eauto.
  Qed.

End Trans.

Module AM := AnnotateTop.

Section Compat.

  Import AM.VM.

  Definition V := AM.V.
  Definition E := AM.E.
  Definition R := AM.R.

  (* Note we allow the following definitions to be customizable
     depending on the invariants we want to enforce. *)

  (* Environment Relation *)
  Definition G i Γ1 ρ1 Γ2 ρ2 :=
    wf_env ρ2 /\
    forall x,
      (x \in Γ1) ->
      forall v1,
        M.get x ρ1 = Some v1 ->
        ((x \in Γ2) ->
         exists v2,
           M.get x ρ2 = Some v2 /\
           V i v1 v2).

  (* Transformation Relation *)
  Definition trans_correct Γ e1 e2 :=
    forall ex i ρ1 ρ2,
      G i Γ ρ1 (A1.occurs_free e2) ρ2 ->
      E ex i ρ1 e1 ρ2 e2.

  (* Environment Lemmas *)
  Lemma G_wf_env_r {i Γ1 ρ1 Γ2 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    wf_env ρ2.
  Proof.
    unfold G.
    intros H; destruct H; auto.
  Qed.

  Lemma G_get {Γ1 Γ2 i ρ1 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall x v1,
      (x \in Γ1) ->
      (x \in Γ2) ->
      M.get x ρ1 = Some v1 ->
      exists v2,
        M.get x ρ2 = Some v2 /\
        V i v1 v2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hr1 HG].
    eapply HG; eauto.
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
      edestruct (G_get HG) as [v2 [Heqv2 HV]]; eauto.
      eapply (H a).
      apply in_eq.
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

  Lemma G_set {i Γ1 ρ1 Γ2 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall {x v1 v2},
      V i v1 v2 ->
      G i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
  Proof.
    unfold G.
    intros.

    inv H.
    split.
    eapply wf_env_set; eauto.
    eapply V_wf_val_r; eauto.

    intros.
    destruct (M.elt_eq x0 x); subst.
    - repeat rewrite M.gss in *.
      inv H3.
      eexists; split; eauto; intros.
    - rewrite M.gso in *; auto.
      inv H.
      inv H5; try contradiction.
      inv H4.
      inv H; try contradiction.
      edestruct H2 as [v1' [Heqv1' Hv2]]; eauto.
  Qed.

  Lemma G_set_lists {i Γ1 ρ1 Γ2 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall {xs vs1 vs2 ρ3 ρ4},
      Forall2 (V i) vs1 vs2 ->
      set_lists xs vs1 ρ1 = Some ρ3 ->
      set_lists xs vs2 ρ2 = Some ρ4 ->
      G i (FromList xs :|: Γ1) ρ3 (FromList xs :|: Γ2) ρ4.
  Proof.
    intros HG xs.
    induction xs; simpl; intros.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      inv H0; inv H1.
      unfold G.
      split; intros.
      eapply G_wf_env_r; eauto.

      eapply (G_get HG); eauto.
      inv H0; auto.
      inv H3.

      inv H2; auto.
      inv H3.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
      destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
      inv H; inv H0; inv H1.
      unfold G.

      split.
      eapply wf_env_set; eauto.
      eapply (wf_env_set_lists ρ2) with (xs := xs) (vs := vs2); eauto.

      eapply G_wf_env_r; eauto.
      eapply V_wf_val_Forall_r; eauto.
      eapply V_wf_val_r; eauto.

      intros.
      destruct (M.elt_eq x a); subst.
      + repeat rewrite M.gss in *; eauto.
        inv H0.
        eexists; split; eauto.
      + rewrite M.gso in *; auto.
        eapply IHxs; eauto.
        eapply not_In_cons_Union; eauto.
        eapply not_In_cons_Union; eauto.
  Qed.

  Lemma G_subset Γ1 Γ2 {i ρ1 Γ3 ρ2 Γ4}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    Γ3 \subset Γ1 ->
    Γ4 \subset Γ2 ->
    G i Γ3 ρ1 Γ4 ρ2.
  Proof.
    unfold G.
    intros.
    inv H; split; auto.
  Qed.

  Lemma G_mono {Γ1 Γ2 ρ1 ρ2} i j:
    G i Γ1 ρ1 Γ2 ρ2 ->
    j <= i ->
    G j Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold G.
    intros.
    inv H.
    split; auto; intros.
    edestruct H2 as [v2 [Heqv2 HV]]; eauto.
    eexists; eexists; repeat split; eauto.
    apply V_mono with i; eauto.
  Qed.

  (* Compatibility Lemmas *)
  Lemma ret_compat Γ x :
    (x \in Γ) ->
    trans_correct Γ (A0.Eret x) (A1.Eret x).
  Proof.
    unfold trans_correct, G, E, AM.E, AM.VM.E, E', AM.VM.R, R', Ensembles.Included, Ensembles.In, Dom_map.
    intros.
    inv H2.
    - exists 0, A1.OOT; split; auto.
    - inv H3.
      edestruct (G_get H0) as [v2 [Heqv2 HV]]; eauto.
      exists 1, (A1.Res v2); split; auto.
      + constructor.
        * constructor; auto.
        * destruct ex; auto.
          eapply AM.V_exposed_res_r; eauto.
      + eapply V_mono; eauto; lia.
  Qed.

  Lemma constr_compat Γ x t xs k k' :
    (FromList xs \subset Γ) ->
    trans_correct (x |: Γ) k k' ->
    trans_correct Γ (A0.Econstr x t xs k) (A1.Econstr x w0 t xs k').
  Proof.
    unfold trans_correct, E, AM.E, AM.VM.E, E'.
    intros.
    inv H3.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv H4.
      destruct (G_get_list H1 xs vs) as [vs' [Heqvs' Hvs]]; auto.
      + eapply A1.free_constr_xs_subset; eauto.
      + assert (length vs = length vs').
        {
          unfold wval in *.
          rewrite <- (get_list_length_eq _ _ _ H10).
          rewrite <- (get_list_length_eq _ _ _ Heqvs'); auto.
        }

        edestruct (H0 ex i (M.set x (A0.Vconstr t vs) ρ1) (M.set x (Tag w0 (A1.Vconstr t vs')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk' Rr]]]; eauto; try lia.
        * eapply G_subset with (Γ2 := (x |: (A1.occurs_free (A1.Econstr x w0 t xs k')))).
          eapply G_set; eauto.
          -- eapply AM.Vconstr_V; eauto.
             apply w0_exposed.
             eapply V_wf_val_Forall_r; eauto.
          -- apply Included_refl.
          -- apply A1.free_constr_k_subset.
        * exists (S j2), r2; split; eauto.
          -- econstructor.
             econstructor; eauto.
             intros.
             eapply AM.V_exposed_Forall_r; eauto.
             destruct ex; auto.
             eapply AM.R_exposed_res_r; eauto.
          -- eapply R_mono; eauto; lia.
  Qed.

  Lemma Vfun_V Γ1 f xs e e' :
    trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
    forall {i Γ2 ρ1 ρ2},
      wf_env ρ2 ->
      G i Γ1 ρ1 Γ2 ρ2 ->
      A1.occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
      V i (A0.Vfun f ρ1 xs e) (Tag w0 (A1.Vfun f ρ2 xs e')).
  Proof.
    unfold trans_correct.
    intros He i.
    induction i; simpl; intros; auto;
      repeat (split; auto); simpl;
      rewrite w0_exposedb;
      repeat (split; eauto);
      try (constructor; apply w0_exposed);
      intros.

    apply (He true (i - (i - j)) ρ3 ρ4); auto.
    - eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))).
      eapply G_set_lists; eauto.
      eapply G_set; eauto.
      + apply G_mono with (S i); eauto; lia.
      + apply V_mono with i; try lia.
        eapply IHi with (Γ2 := Γ2); eauto.
        apply G_mono with (S i); eauto; lia.
      + apply Included_refl.
      + auto.
  Qed.

  Lemma fun_compat Γ e e' k k' f xs :
    trans_correct (FromList xs :|: (f |: Γ)) e e' ->
    trans_correct (f |: Γ) k k' ->
    trans_correct Γ (A0.Efun f xs e k) (A1.Efun f w0 xs e' k').
  Proof.
    unfold trans_correct, E, AM.E, AM.VM.E, E'.
    intros.
    inv H3.
    - exists 0, A1.OOT; split; simpl; eauto.
    - inv H4.
      edestruct (H0 ex (i - 1) (M.set f (A0.Vfun f ρ1 xs e) ρ1) (M.set f (Tag w0 (A1.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + eapply G_subset with (Γ2 := (f |: A1.occurs_free (A1.Efun f w0 xs e' k'))).
        eapply G_set; eauto.
        apply G_mono with i; eauto; lia.
        * eapply Vfun_V; eauto.
          -- eapply G_wf_env_r; eauto.
          -- apply G_mono with i; eauto; lia.
          -- apply A1.free_fun_e_subset.
        * apply Included_refl.
        * apply A1.free_fun_k_subset.
      + exists (S j2), r2; split; auto.
        constructor.
        econstructor; eauto.
        destruct ex; auto.
        eapply AM.R_exposed_res_r; eauto.
        eapply R_mono; eauto; lia.
  Qed.

  Lemma app_compat Γ xs f :
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct Γ (A0.Eapp f xs) (A1.Eapp f w0 xs).
  Proof.
    unfold trans_correct, G, E, AM.E, AM.VM.E, E'.
    intros.
    inv H3.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv H4.
      edestruct (G_get H1 f) as [fv2 [Heqfv2 HV]]; eauto.
      destruct i.
      inv H2.
      destruct fv2; simpl in HV;
        destruct HV as [Hv1 HV];
        destruct (exposed_reflect w); try contradiction;
        destruct HV as [Hex HV];
        destruct v; try contradiction.
      destruct HV as [Hlen HV].

      assert (Hw : w = w0).
      {
        inv Hex.
        apply Exposed_singleton; eauto.
      }
      subst.

      edestruct (G_get_list H1 xs vs) as [vs2 [Heqvs2 Vvs]]; eauto.
      eapply A1.free_app_xs_subset; eauto.

      destruct (set_lists_length3 (M.set v (Tag w0 (A1.Vfun v t l e0)) t) l vs2) as [ρ4 Heqρ4].
      unfold wval in *.
      rewrite <- (Forall2_length _ _ _ Vvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H8); auto.

      assert (Forall A1.exposed vs2) by (eapply AM.V_exposed_Forall_r; eauto).
      assert (HE : E true (i - (i - i)) ρ'' e ρ4 e0).
      {
        eapply (HV i vs vs2); eauto.
        apply V_mono_Forall with (S i); auto; lia.
      }

      apply (E_mono _ i) in HE; try lia.
      unfold E in HE.
      destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.

      assert (A1.exposed_res r2) by (eapply AM.R_exposed_res_r; eauto).

      exists (S j2), r2; split; eauto.
      constructor; auto.
      econstructor; eauto.
      rewrite w0_exposedb; auto.
      destruct ex; auto.
  Qed.

  Lemma letapp_compat Γ k k' xs x f :
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct (x |: Γ) k k' ->
    trans_correct Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w0 xs k').
  Proof.
    intros.
    specialize (app_compat Γ xs f H H0); intros Ha.
    unfold trans_correct, E, AM.E, AM.VM.E, E' in *.
    intros.

    assert (HG' : G i Γ ρ1 (occurs_free (A1.Eapp f w0 xs)) ρ2).
    {
      eapply G_subset with (Γ2 := (occurs_free (A1.Eletapp x f w0 xs k'))); eauto.
      apply Included_refl.
      eapply free_app_letapp; eauto.
    }

    inv H4.
    - exists 0, OOT; split; simpl; auto.
    - inv H5.
      + destruct (Ha true i ρ1 ρ2) with (j1 := (S c0)) (r1 := (A0.Res v)) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
        * simpl in HR.
          destruct r2; try contradiction.
          rename w into v0.
          inv Hr1.

          edestruct (H1 ex (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
          -- eapply G_subset with (Γ2 := (x |: (A1.occurs_free (A1.Eletapp x f w0 xs k')))).
             eapply G_set; eauto.
             apply G_mono with i; try lia; eauto.
             apply Included_refl.
             apply free_letapp_k_subset.
          -- exists ((S c) + j2), r2; split.
             ++ inv H4.
                rewrite_math ((S c + j2) = S (c + j2)).
                constructor; auto.
                ** eapply BStep_letapp_Res; eauto.
                   intros.
                   destruct H20; auto.
                   inv H7.
                   split; auto.
                ** destruct ex; auto.
                   eapply AM.R_exposed_res_r; eauto.
             ++ eapply R_mono; eauto; lia.
      + eexists; eexists; repeat split; eauto.
        simpl; auto.
  Qed.

  Lemma proj_compat Γ x i y e e' :
    (y \in Γ) ->
    trans_correct (x |: Γ) e e' ->
    trans_correct Γ (A0.Eproj x i y e) (A1.Eproj x w0 i y e').
  Proof.
    unfold trans_correct, E, AM.E, AM.VM.E, E'.
    intros.
    inv H3.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv H4.
      edestruct (G_get H1 y) as [v2 [Heqv2 HV]]; eauto.
      destruct i0.
      inv H2.
      destruct v2;
        simpl in HV;
        destruct HV as [Hv1 HV]; subst;
        destruct (exposed_reflect w); try contradiction;
        destruct HV as [Hex HV];
        destruct v0; try contradiction.
      rename l into vs'.
      rename c0 into t'.
      destruct HV as [Heqt HFvs]; subst.
      destruct (Forall2_nth_error H11 HFvs) as [v' [Heqv' HFv]].
      edestruct (H0 ex i0 (M.set x v ρ1) (M.set x v' ρ2)) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
      + eapply G_subset with (Γ2 := (x |: (A1.occurs_free (A1.Eproj x w0 i y e')))).
        eapply G_set; eauto.
        eapply G_mono; eauto; lia.
        eapply V_mono; eauto; lia.
        apply Included_refl.
        apply A1.free_proj_k_subset.
      + assert (Hw : w = w0).
        {
          inv Hex.
          apply Exposed_singleton; eauto.
        }
        subst.

        exists (S j2), r2; split; eauto.
        constructor.
        econstructor; eauto.
        destruct ex; auto.
        eapply AM.R_exposed_res_r; eauto.
  Qed.

  Lemma case_nil_compat Γ x:
    (x \in Γ) ->
    trans_correct Γ (A0.Ecase x []) (A1.Ecase x w0 []).
  Proof.
    unfold trans_correct, E, AM.E, AM.VM.E, E'.
    intros.
    inv H2.
    - exists 0, A1.OOT; split; simpl; auto.
    - fcrush.
  Qed.

  Lemma case_cons_compat Γ x t e e' cl cl':
    (x \in Γ) ->
    trans_correct Γ e e' ->
    trans_correct Γ (A0.Ecase x cl) (A1.Ecase x w0 cl') ->
    trans_correct Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x w0 ((t, e') :: cl')).
  Proof.
    unfold trans_correct, E, AM.E, AM.VM.E, E'.
    intros.
    inv H4.
    - exists 0, OOT; split; simpl; eauto.
    - inv H5.
      edestruct (G_get H2) as [v2 [Heqv2 HV]]; eauto.
      destruct v2.
      destruct i.
      inv H3.
      destruct v; simpl in HV;
        destruct HV as [Hv2 HV]; subst;
        destruct (exposed_reflect w); try contradiction;
        destruct HV as [Hex HV];
        subst; try contradiction.
      destruct HV as [Heqt HFvs]; subst.
      assert (Hw : w = w0).
      {
        inv Hex.
        apply Exposed_singleton; eauto.
      }
      subst.

      inv H8.
      + edestruct (H0 ex i ρ1 ρ2) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
        eapply G_subset with (Γ2 := (A1.occurs_free (A1.Ecase x w0 ((c0, e') :: cl')))); eauto.
        eapply G_mono; eauto.
        apply Included_refl.
        apply A1.free_case_hd_subset.

        exists (S j2), r2; split; eauto.
        econstructor; eauto.
        destruct ex; auto.
        eapply AM.R_exposed_res_r; eauto.
      + edestruct (H1 ex (S i) ρ1 ρ2) with (j1 := S c) (r1 := r1) as [j2 [r2 [He' HR]]]; eauto; try lia.
        eapply G_subset; eauto.
        apply Included_refl.
        apply A1.free_case_tl_subset; auto.

        exists j2, r2; split; eauto.
        inv He'; auto.
        inv H4.
        rewrite Heqv2 in H10; inv H10; eauto.
  Qed.

  (* Fundamental Property *)
  Lemma fundamental_property {Γ e e'}:
    trans Γ e e' -> trans_correct Γ e e'.
  Proof.
    intros H.
    induction H.
    - eapply ret_compat; auto.
    - eapply fun_compat; eauto.
    - eapply app_compat; eauto.
    - eapply letapp_compat; eauto.
    - eapply constr_compat; eauto.
    - eapply proj_compat; eauto.
    - eapply case_nil_compat; eauto.
    - eapply case_cons_compat; eauto.
  Qed.

End Compat.

Section Top.

  (* Note AM is the top-level module. *)

  Lemma G_top_G :
    forall {i Γ1 ρ1 Γ2 ρ2},
      AM.G i Γ1 ρ1 Γ2 ρ2 ->
      G i Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold AM.G, G.
    intros.
    destruct H as [HΓ [Hρ HG]].
    unfold Ensembles.Included, Ensembles.In, Dom_map in *.
    split; auto; intros.
    edestruct HG as [v1' [v2 [Heqv1 [Heqv2 HV]]]]; eauto.
    rewrite Heqv1 in H0; inv H0; eauto.
  Qed.

  Theorem top etop etop':
    trans (A0.occurs_free etop) etop etop' ->
    AM.trans_correct etop etop'.
  Proof.
    unfold AM.trans_correct.
    intros H.
    specialize (fundamental_property H);
      unfold trans_correct; intros.
    split; intros.
    - eapply trans_exp_inv; eauto.
    - eapply H0; eauto.
      eapply G_top_G; eauto.
  Qed.

End Top.

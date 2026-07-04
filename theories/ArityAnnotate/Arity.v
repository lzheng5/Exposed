From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From LambdaANF Require Import ANF.
From LambdaWeb Require Import ANF.
From ArityAnnotate Require Import Base Annotate.

(* Trivial Web Annotation Based on Function Arities *)

(* We annotate function values with some Exposed web id based on their arities. *)
(* We annotate constructor values with a single Exposed web id. *)

(* Note this is basically annotating with `fun_tag`s in CertiCoq, but there are no internal webs. *)

Module A0 := LambdaANF.ANF.
Module A1 := LambdaWeb.ANF.

(* Specification *)
Inductive trans (Γ : vars) : A0.exp -> A1.exp -> Prop :=
| Trans_ret :
  forall {x},
    (x \in Γ) ->
    trans Γ (A0.Eret x) (A1.Eret x)

| Trans_fun :
  forall {f xs e k e' k'},
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->
    trans Γ (A0.Efun f xs e k) (A1.Efun f w xs e' k')

| Trans_app :
  forall {f xs},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    trans Γ (A0.Eapp f xs) (A1.Eapp f w xs)

| Trans_letapp :
  forall {x f xs k k'},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    trans (x |: Γ) k k' ->
    trans Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w xs k')

| Trans_constr :
  forall {x t xs k k'},
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (A0.Econstr x t xs k) (A1.Econstr x w_constr t xs k')

| Trans_proj :
  forall {x y k k' n},
    (y \in Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (A0.Eproj x n y k) (A1.Eproj x w_constr n y k')

| Trans_case_nil :
  forall {x},
    (x \in Γ) ->
    trans Γ (A0.Ecase x []) (A1.Ecase x w_constr [])

| Trans_case_cons :
  forall {x e e' t cl cl'},
    (x \in Γ) ->
    trans Γ e e' ->
    trans Γ (A0.Ecase x cl) (A1.Ecase x w_constr cl') ->
    trans Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x w_constr ((t, e') :: cl')).

Hint Constructors trans : core.

Lemma trans_exp_inv {Γ e e'} :
  trans Γ e e' ->
  (A1.occurs_free e') \subset (A0.occurs_free e).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros H.
  induction H; simpl; intros; auto.
  - inv H0; auto.
  - inv H2; auto.
  - inv H2; auto.
  - inv H3; auto.
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
  induction H; simpl; intros; auto; subst.
  - constructor; auto.
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
  - constructor; auto.
    + eapply Included_trans; eauto.
    + eapply IHtrans; eauto.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
  - constructor; auto.
    eapply IHtrans; eauto.
    eapply Included_Union_compat; eauto.
    apply Included_refl.
Qed.

Module AM := AnnotateTop.

Section Compat.

  Import AM.VM.

  Definition V := AM.V.
  Definition E := AM.E.
  Definition R := AM.R.
  Definition G := AM.G.

  (* Transformation Relation *)
  Definition trans_correct Γ e1 e2 :=
    forall ex i ρ1 ρ2,
      G i Γ ρ1 ρ2 ->
      E ex i ρ1 e1 ρ2 e2.

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
      edestruct (AM.G_get H0) as [v2 [Heqv2 HV]]; eauto.
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
    trans_correct Γ (A0.Econstr x t xs k) (A1.Econstr x w_constr t xs k').
  Proof.
    unfold trans_correct, E, AM.E, AM.VM.E, E'.
    intros.
    inv H3.
    - fcrush.
    - inv H4.
      destruct (AM.G_get_list H1 xs vs) as [vs' [Heqvs' Hvs]]; auto.
      + assert (length vs = length vs').
        {
          unfold wval in *.
          rewrite <- (get_list_length_eq _ _ _ H10).
          rewrite <- (get_list_length_eq _ _ _ Heqvs'); auto.
        }

        edestruct (H0 ex i (M.set x (A0.Vconstr t vs) ρ1) (M.set x (Tag w_constr (A1.Vconstr t vs')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk' Rr]]]; eauto; try lia.
        * eapply AM.G_set; eauto.
          -- eapply AM.Vconstr_V; eauto.
             eapply w_constr_exposed; eauto.
             eapply V_wf_val_Forall_r; eauto.
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
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
    forall i ρ1 ρ2,
      wf_env ρ2 ->
      G i Γ1 ρ1 ρ2 ->
      V i (A0.Vfun f ρ1 xs e) (Tag w (A1.Vfun f ρ2 xs e')).
  Proof.
    unfold trans_correct.
    intros Hw He i.
    induction i; simpl; intros; auto;
      repeat (split; auto); simpl;
      destruct (exposed_reflect (arity_to_web (length xs))); try contradiction;
      repeat (split; eauto); intros.

    apply (He true (i - (i - j)) ρ3 ρ4); auto.
    - eapply AM.G_set_lists; eauto.
      eapply AM.G_set; eauto.
      + apply AM.G_mono with (S i); eauto; lia.
      + apply V_mono with i; try lia.
        eapply IHi; eauto.
        apply AM.G_mono with (S i); eauto; lia.
  Qed.

  Lemma fun_compat Γ e e' k k' f xs :
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    trans_correct (FromList xs :|: (f |: Γ)) e e' ->
    trans_correct (f |: Γ) k k' ->
    trans_correct Γ (A0.Efun f xs e k) (A1.Efun f w xs e' k').
  Proof.
    unfold trans_correct, E, AM.E, AM.VM.E, E'.
    intross Hw.
    inv H3.
    - fcrush.
    - inv H4.
      edestruct (H0 ex (i - 1) (M.set f (A0.Vfun f ρ1 xs e) ρ1) (M.set f (Tag (arity_to_web (length xs)) (A1.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + eapply AM.G_set; eauto.
        apply AM.G_mono with i; eauto; lia.
        * eapply Vfun_V; eauto.
          -- eapply AM.G_wf_env_r; eauto.
          -- apply AM.G_mono with i; eauto; lia.
      + exists (S j2), r2; split; auto.
        constructor.
        econstructor; eauto.
        destruct ex; auto.
        eapply AM.R_exposed_res_r; eauto.
        eapply R_mono; eauto; lia.
  Qed.

  Lemma app_compat Γ xs f :
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct Γ (A0.Eapp f xs) (A1.Eapp f w xs).
  Proof.
    unfold trans_correct, G, E, AM.E, AM.VM.E, E'.
    intross Hw.
    inv H3.
    - fcrush.
    - inv H4.
      edestruct (AM.G_get H1 f) as [fv2 [Heqfv2 HV]]; eauto.
      destruct i.
      inv H2.
      destruct fv2; simpl in HV;
        destruct HV as [Hv1 HV];
        destruct (exposed_reflect w); try contradiction;
        destruct HV as [Hex HV];
        destruct v; try contradiction.
      destruct HV as [Heqw [Hlen HV]]; subst.

      assert (Hlenxs : length xs' = length xs).
      {
        unfold var in *.
        erewrite (set_lists_length_eq _ _ xs' vs); eauto.
        erewrite <- (get_list_length_eq xs vs); eauto.
      }
      rewrite_by (arity_to_web (length xs') = arity_to_web (length xs)) eauto.

      edestruct (AM.G_get_list H1 xs vs) as [vs2 [Heqvs2 Vvs]]; eauto.

      destruct (set_lists_length3 (M.set v (Tag (arity_to_web (length xs)) (A1.Vfun v t l e0)) t) l vs2) as [ρ4 Heqρ4].
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
      destruct (exposed_reflect (arity_to_web (length xs))); try contradiction; eauto.
      destruct ex; auto.
  Qed.

  Lemma letapp_compat Γ k k' xs x f :
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct (x |: Γ) k k' ->
    trans_correct Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w xs k').
  Proof.
    intross Hw.
    specialize (app_compat Γ xs f H H0 H1); intros Ha.
    unfold trans_correct, E, AM.E, AM.VM.E, E' in *.
    intros.

    inv H5.
    - fcrush.
    - inv H6.
      + destruct (Ha true i ρ1 ρ2) with (j1 := (S c0)) (r1 := (A0.Res v)) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
        * simpl in HR.
          destruct r2; try contradiction.
          rename w into v0.
          inv Hr1.

          edestruct (H2 ex (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
          -- eapply AM.G_set; eauto.
             apply AM.G_mono with i; try lia; eauto.
          -- exists ((S c) + j2), r2; split.
             ++ inv H5.
                rewrite_math ((S c + j2) = S (c + j2)).
                constructor; auto.
                ** eapply BStep_letapp_Res; eauto.
                   fcrush.
                ** destruct ex; auto.
                   eapply AM.R_exposed_res_r; eauto.
             ++ eapply R_mono; eauto; lia.
      + fcrush.
  Qed.

  Lemma proj_compat Γ x i y e e' :
    (y \in Γ) ->
    trans_correct (x |: Γ) e e' ->
    trans_correct Γ (A0.Eproj x i y e) (A1.Eproj x w_constr i y e').
  Proof.
    unfold trans_correct, E, AM.E, AM.VM.E, E'.
    intros.
    inv H3.
    - fcrush.
    - inv H4.
      edestruct (AM.G_get H1 y) as [v2 [Heqv2 HV]]; eauto.
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
      destruct HV as [Heqw [Heqt HFvs]]; subst.
      destruct (Forall2_nth_error H11 HFvs) as [v' [Heqv' HFv]].
      edestruct (H0 ex i0 (M.set x v ρ1) (M.set x v' ρ2)) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
      + eapply AM.G_set; eauto.
        eapply AM.G_mono; eauto; lia.
        eapply V_mono; eauto; lia.
      + exists (S j2), r2; split; eauto.
        constructor.
        econstructor; eauto.
        destruct ex; auto.
        eapply AM.R_exposed_res_r; eauto.
  Qed.

  Lemma case_nil_compat Γ x:
    (x \in Γ) ->
    trans_correct Γ (A0.Ecase x []) (A1.Ecase x w_constr []).
  Proof.
    unfold trans_correct, E, AM.E, AM.VM.E, E'.
    intros.
    inv H2; fcrush.
  Qed.

  Lemma case_cons_compat Γ x t e e' cl cl':
    (x \in Γ) ->
    trans_correct Γ e e' ->
    trans_correct Γ (A0.Ecase x cl) (A1.Ecase x w_constr cl') ->
    trans_correct Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x w_constr ((t, e') :: cl')).
  Proof.
    unfold trans_correct, E, AM.E, AM.VM.E, E'.
    intros.
    inv H4.
    - fcrush.
    - inv H5.
      edestruct (AM.G_get H2) as [v2 [Heqv2 HV]]; eauto.
      destruct v2.
      destruct i.
      inv H3.
      destruct v; simpl in HV;
        destruct HV as [Hv2 HV]; subst;
        destruct (exposed_reflect w); try contradiction;
        destruct HV as [Hex HV];
        subst; try contradiction.
      destruct HV as [Heqw [Heqt HFvs]]; subst.

      inv H8.
      + edestruct (H0 ex i ρ1 ρ2) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
        eapply AM.G_mono; eauto.

        exists (S j2), r2; split; eauto.
        econstructor; eauto.
        destruct ex; auto.
        eapply AM.R_exposed_res_r; eauto.
      + edestruct (H1 ex (S i) ρ1 ρ2) with (j1 := S c) (r1 := r1) as [j2 [r2 [He' HR]]]; eauto; try lia.

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
  Qed.

End Top.

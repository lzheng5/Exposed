From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF Exposed.

(* Reflexive/Identity Transformation with Exposed Framework *)

(* Specification *)
Inductive trans (Γ : Ensemble var) : exp -> exp -> Prop :=
| Trans_ret :
  forall {x},
    (x \in Γ) ->
    trans Γ (Eret x) (Eret x)

| Trans_fun :
  forall {f w xs e k e' k'},
    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->
    trans Γ (Efun f w xs e k) (Efun f w xs e' k')

| Trans_app :
  forall {f w xs},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans Γ (Eapp f w xs) (Eapp f w xs)

| Trans_letapp :
  forall {x f w xs k k'},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (Eletapp x f w xs k) (Eletapp x f w xs k')

| Trans_constr :
  forall {x w t xs k k'},
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (Econstr x w t xs k) (Econstr x w t xs k')

| Trans_proj :
  forall {x y w k k' n},
    (y \in Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (Eproj x w n y k) (Eproj x w n y k')

| Trans_case_nil :
  forall {x w},
    (x \in Γ) ->
    trans Γ (Ecase x w []) (Ecase x w [])

| Trans_case_cons :
  forall {x w e e' t cl cl'},
    (x \in Γ) ->
    trans Γ e e' ->
    trans Γ (Ecase x w cl) (Ecase x w cl') ->
    trans Γ (Ecase x w ((t, e) :: cl)) (Ecase x w ((t, e') :: cl')).

Hint Constructors trans : core.

Theorem trans_refl {Γ e e'} :
  trans Γ e e' -> e = e'.
Proof.
  intros H.
  induction H; subst; auto.
  inv IHtrans2; auto.
Qed.

Lemma trans_sub Γ1 Γ2 e1 e2 :
  Γ1 \subset Γ2 ->
  trans Γ1 e1 e2 ->
  trans Γ2 e1 e2.
Proof.
  intros.
  revert Γ2 H.
  induction H0; intros;
    econstructor; eauto.
  - eapply IHtrans1; eauto; intros.
    apply Included_Union_compat.
    apply Included_refl.
    apply Included_Union_compat; auto.
    apply Included_refl.
  - eapply IHtrans2; eauto; intros.
    apply Included_Union_compat; auto.
    apply Included_refl.
  - eapply Included_trans; eauto.
  - eapply Included_trans; eauto.
  - eapply IHtrans; eauto.
    apply Included_Union_compat; auto.
    apply Included_refl.
  - eapply Included_trans; eauto.
  - eapply IHtrans; eauto.
    apply Included_Union_compat; auto.
    apply Included_refl.
  - eapply IHtrans; eauto.
    apply Included_Union_compat; auto.
    apply Included_refl.
Qed.

Theorem refl_trans e :
  trans (occurs_free e) e e.
Proof.
  induction e using exp_ind'; constructor; eauto;
    unfold Ensembles.Included, Ensembles.In in *; auto.
  - apply (trans_sub (occurs_free e1)); auto.
    apply free_fun_e_subset.
  - apply (trans_sub (occurs_free e2)); auto.
    apply free_fun_k_subset.
  - apply (trans_sub (occurs_free e)); auto.
    apply free_letapp_k_subset.
  - apply (trans_sub (occurs_free e)); eauto.
    apply free_constr_k_subset.
  - apply (trans_sub (occurs_free e)); auto.
    apply free_case_hd_subset.
  - apply (trans_sub (occurs_free (Ecase x w cl))); auto.
    apply free_case_tl_subset.
  - apply (trans_sub (occurs_free e)); auto.
    apply free_proj_k_subset.
Qed.

(* Logical Relations *)
Module LM <: Exposed.LSig.

  Definition elt := unit.

  Definition L := M.empty elt.

  Lemma L_inv_None : forall w, w \in Exposed -> L ! w = None.
  Proof. unfold L. auto. Qed.

  Lemma L_inv_Some : forall w d, L ! w = Some d -> (~ (w \in Exposed)).
  Proof. unfold L. simpl; intros. inv H. Qed.

End LM.
Import LM.

Module VTransM <: Exposed.VTrans LM.

  Definition V_trans
    (V' : nat -> wval -> wval -> Prop)
    (E' : nat -> env -> exp -> env -> exp -> Prop)
    (i0 : nat) (d : LM.elt)
    (w1 : web) (v1 : val) (w2 : web) (v2 : val) := False.

  Lemma V_trans_mono V E i j d w1 v1 w2 v2 :
    (forall k : nat,
        k < S i ->
        forall (j : nat) (v1 v2 : wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
    V_trans (fun i' => V (i - (i - i'))) (fun i' => E (i - (i - i'))) i d w1 v1 w2 v2 ->
    j <= i ->
    V_trans (fun j' => V (j - (j - j'))) (fun j' => E (j - (j - j'))) j d w1 v1 w2 v2.
  Proof.
    unfold V_trans.
    intros; contradiction.
  Qed.

End VTransM.

Module EM := Exposed.Exposed LM VTransM.
Import EM.

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

Lemma fundamental_property' e :
  trans_correct (occurs_free e) e e.
Proof.
  eapply fundamental_property.
  apply refl_trans.
Qed.

(* Reflexivity of E *)
Import ExposedUtil.

Lemma refl_V_G :
  forall i,
    (forall k : nat, k < S i -> forall v : wval, wf_val v -> V k v v) ->
    forall Γ1 Γ2 ρ,
      wf_env ρ ->
      forall xs j vs1 vs2 ρ1 ρ2,
        j <= i ->
        Forall2 (V j) vs1 vs2 ->
        set_lists xs vs1 ρ = Some ρ1 ->
        set_lists xs vs2 ρ = Some ρ2 ->
        G j Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G.
  intros i HI Γ1 Γ2 ρ Henv xs.
  induction xs; simpl; intros.
  - destruct vs1; destruct vs2; try discriminate.
    inv H1; inv H2.
    repeat (split; auto); intros.
    eexists; split; eauto.
    eapply HI; eauto; try lia.
    eapply wf_env_get; eauto.
  - destruct vs1; destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ) eqn:Heq2; try discriminate.
    inv H0; inv H1; inv H2.

    split.
    eapply wf_env_set; eauto.
    eapply (wf_env_set_lists ρ) with (xs := xs) (vs := vs1); eauto.
    eapply V_wf_val_Forall_l; eauto.
    eapply V_wf_val_l; eauto.

    split.
    eapply wf_env_set; eauto.
    eapply (wf_env_set_lists ρ) with (xs := xs) (vs := vs2); eauto.
    eapply V_wf_val_Forall_r; eauto.
    eapply V_wf_val_r; eauto.

    intros.
    destruct (M.elt_eq a x); subst.
    + rewrite M.gss in *; auto.
      inv H1.
      eexists; split; eauto.
    + rewrite M.gso in *; auto.
      edestruct IHxs as [v2 [Heqv2 HV]]; eauto.
Qed.

Lemma refl_V_ForallV :
  forall i,
    (forall k : nat, k < S i -> forall v : wval, wf_val v -> V k v v) ->
    forall vs j,
      j <= i ->
      Forall wf_val vs ->
      Forall2 (V j) vs vs.
Proof.
  intros i HI vs.
  induction vs; simpl; intros; auto.
  inv H0.
  constructor; auto.
  eapply HI; eauto; try lia.
Qed.

Theorem refl_V :
  forall i v, wf_val v -> V i v v.
Proof.
  intros i.
  induction i using lt_wf_rec; intros.
  destruct i; simpl; intros;
    split; auto;
    destruct v;
    repeat (split; auto);
    destruct (L ! w) eqn:Heq1; try discriminate.
  - eapply refl_V_refl0.
  - destruct v; repeat (split; auto); intros.
    + rewrite normalize_step in *; try lia.
      assert (wf_env (M.set v (Tag w (Vfun v t l e)) t)).
      {
        eapply wf_env_set; eauto.
        inv H0.
        inv H10; auto.
      }

      specialize (fundamental_property' e); intros FP.
      unfold trans_correct in FP.
      apply FP.
      eapply refl_V_G; eauto.
    + repeat split; auto.
      destruct (wf_val_Vconstr_inv H0) as [HF HW]; auto.
      eapply refl_V_ForallV; eauto; lia.
Qed.

Corollary refl_V_Forall vs :
  Forall wf_val vs ->
  forall i, Forall2 (V i) vs vs.
Proof.
  intros H.
  induction H; simpl; auto; intros.
  constructor; auto.
  eapply refl_V; eauto.
Qed.

Corollary refl_R :
  forall i r, wf_res r -> R i r r.
Proof.
  unfold R'.
  intros.
  inv H; simpl; auto.
  apply refl_V; auto.
Qed.

Corollary refl_E :
  forall i ex ρ e,
    wf_env ρ ->
    E ex i ρ e ρ e.
Proof.
  unfold E, E'.
  intros.
  eexists; eexists; split; eauto.
  inv H1; simpl; auto.
  apply refl_R; auto.
  eapply bstep_wf_res; eauto.
Qed.

Corollary refl_G :
  forall i Γ ρ,
    wf_env ρ ->
    G i Γ ρ Γ ρ.
Proof.
  unfold G.
  intros.
  repeat (split; auto); intros.
  eexists; split; eauto.
  apply refl_V.
  eapply wf_env_get; eauto.
Qed.

(* Transitivity of E *)
Lemma trans_E_aux i :
  (forall m : nat,
      m <= i ->
      forall v1 v2 v3 : wval,
        V m v1 v2 ->
        (forall i : nat, V i v2 v3) ->
        V m v1 v3) ->
  forall {ex ρ1 e1 ρ2 e2 ρ3 e3},
    E ex i ρ1 e1 ρ2 e2 ->
    (forall i, E ex i ρ2 e2 ρ3 e3) ->
    E ex i ρ1 e1 ρ3 e3.
Proof.
  unfold E, E'.
  intros IH; intros.
  edestruct H as [j2 [r2 [Hr2 HR]]]; eauto.
  edestruct (H0 j2) as [j3 [r3 [Hr3 HR']]]; eauto; try lia.
  eexists; eexists; split; eauto.
  unfold R' in *.
  destruct r1; destruct r2; destruct r3; try contradiction; auto.
  eapply IH; eauto; try lia.
  intros.
  edestruct (H0 (i0 + j2) j2) as [j3' [r3' [Hr3' HR'']]]; eauto; try lia.
  simpl in *.
  destruct r3'; try contradiction.
  edestruct (bstep_fuel_deterministic w1 w2 Hr3 Hr3'); eauto; subst.
  eapply V_mono; eauto; try lia.
Qed.

Lemma trans_V_Forall_aux i :
  (forall m : nat,
      m <= i ->
      forall v1 v2 v3 : wval,
        V m v1 v2 ->
        (forall i : nat, V i v2 v3) ->
        V m v1 v3) ->
  forall {vs1},
    Forall wf_val vs1 ->
    forall {vs2 vs3},
      Forall2 (V i) vs1 vs2 ->
      (forall i, Forall2 (V i) vs2 vs3) ->
      Forall2 (V i) vs1 vs3.
Proof.
  intros IH vs1 H.
  induction H; simpl; intros.
  - inv H.
    eapply H0; eauto.
  - inv H1.
    pose proof (H2 i) as H2'.
    inv H2'.
    constructor.
    + eapply IH; eauto; try lia.
      intros.
      specialize (H2 i0).
      inv H2; auto.
    + eapply IHForall; eauto; try lia.
      intros.
      specialize (H2 i0).
      inv H2; auto.
Qed.

Theorem trans_V :
  forall {i v1 v2 v3},
    V i v1 v2 ->
    (forall i, V i v2 v3) ->
    V i v1 v3.
Proof.
  intros i.
  induction i using lt_wf_rec1; intros.
  destruct i.
  - specialize (H1 0).
    destruct v1; destruct v2; destruct v3;
      simpl in *;
      destruct H0 as [Hv1 [Hv2 [Hw HV0]]];
      destruct H1 as [Hv2' [Hv3 [Hw' HV0']]]; subst.
    repeat (split; auto).
    unfold V_refl0 in *.
    destruct v; destruct v0; destruct v1; try contradiction.
    + rewrite HV0; auto.
    + destruct HV0; destruct HV0'; subst.
      split; auto.
      rewrite H1; auto.
  - pose proof (H1 (S i)).
    simpl in *.
    destruct H0 as [Hv1 [Hv2 HV]].
    destruct H2 as [_ [Hv3 HV']].
    repeat (split; auto).
    destruct v1; destruct v2; destruct v3; simpl in *.
    destruct HV as [Hw HV].
    destruct HV' as [Hw' HV']; subst.
    unfold V_refl in *.
    split; auto.
    destruct v; destruct v0; destruct v1; try contradiction.
    + destruct HV as [Hlen HV].
      destruct HV' as [Hlen' HV'].
      split.
      rewrite Hlen; auto.
      intros.
      destruct (set_lists_length3 (M.set v0 (TAG val w1 (Vfun v0 t0 l0 e0)) t0) l0 vs2) as [ρ5 Heqρ5].
      unfold wval in *.
      rewrite <- (set_lists_length_eq _ _ _ _ H6); auto.
      eapply trans_E_aux; eauto.
      * intros; eapply H; eauto; lia.
      * eapply (HV j vs1 vs2 ρ3 ρ5); eauto.
      * clear HV'.
        intros k.
        specialize (H1 (S k)); simpl in H1.
        destruct H1 as [_ [_ [_ [_ HV']]]].
        assert (E (exposedb w1) (k - (k - k)) ρ5 e0 ρ4 e1).
        {
          eapply HV'; eauto; try lia.
          eapply refl_V_Forall; eauto.
          eapply V_wf_val_Forall_r; eauto.
        }
        eapply E_mono; eauto; try lia.
    + destruct HV as [Hc HV]; subst.
      destruct HV' as [Hc' HV']; subst.
      split; auto.
      eapply trans_V_Forall_aux; eauto; try lia.
      * intros; eapply H; eauto; lia.
      * destruct (wf_val_Vconstr_inv Hv1); auto.
      * clear HV'.
        intros.
        specialize (H1 (S i0)); simpl in H1.
        destruct H1 as [_ [_ [_ [_ HV']]]].
        eapply V_mono_Forall; eauto; lia.
Qed.

Corollary trans_R {i r1 r2 r3} :
  R i r1 r2 ->
  (forall k, R k r2 r3) ->
  R i r1 r3.
Proof.
  unfold R, R'.
  intros.
  destruct r1; destruct r2; destruct r3; try contradiction; auto.
  eapply trans_V; eauto.
Qed.

Corollary trans_E {i ex ρ1 e1 ρ2 e2 ρ3 e3}:
  E ex i ρ1 e1 ρ2 e2 ->
  (forall i, E ex i ρ2 e2 ρ3 e3) ->
  E ex i ρ1 e1 ρ3 e3.
Proof.
  intros.
  eapply trans_E_aux; eauto.
  intros.
  eapply trans_V; eauto.
Qed.

(* Top Level *)
Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  wf_env ρ1 /\
  wf_env ρ2 /\
  Γ2 \subset Γ1 /\
  (forall x,
    (x \in Γ1 ->
     exists v1 v2,
       M.get x ρ1 = Some v1 /\
       M.get x ρ2 = Some v2 /\
       exposed v1 /\
       V i v1 v2)).

Lemma G_top_G {i Γ1 ρ1 Γ2 ρ2} :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  G i Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G_top, G.
  intros.
  destruct H as [Hr1 [Hr2 [Hs HG]]].
  repeat (split; auto); intros.
  edestruct (HG x) as [v1' [v2 [Heqv1' [Heqv2 [Hex HV]]]]]; eauto.
  rewrite Heqv1' in H0; inv H0.
  eexists; split; eauto; intros.
Qed.

Definition trans_correct_top etop etop' :=
  (occurs_free etop') \subset (occurs_free etop) /\
  forall i ρ1 ρ2,
    G_top i (occurs_free etop) ρ1 (occurs_free etop') ρ2 ->
    E true i ρ1 etop ρ2 etop'.

Theorem top' etop etop':
  trans (occurs_free etop) etop etop' ->
  trans_correct_top etop etop'.
Proof.
  unfold trans_correct_top.
  intros H.
  specialize (fundamental_property H);
    unfold trans_correct.
  split.
  - erewrite <- trans_refl; eauto.
    apply Included_refl.
  - intros.
    eapply H0; eauto.
    eapply G_top_G; eauto.
Qed.

(* Reflexivity of [trans_correct_top] *)
Corollary refl_trans_correct_top :
  Reflexive trans_correct_top.
Proof.
  unfold trans_correct_top.
  intros e.
  split.
  apply Included_refl.
  intros.
  specialize (fundamental_property' e);
    unfold trans_correct.
  intros.
  eapply H0; eauto.
  eapply G_top_G; eauto.
Qed.

(* Transitivity of [trans_correct_top] *)
Theorem trans_trans_correct_top :
  Transitive trans_correct_top.
Proof.
  intros e1 e2 e3.
  unfold trans_correct_top, G_top.
  intros.
  destruct H.
  destruct H0.
  split; intros.
  - eapply Included_trans; eauto.
  - destruct H3 as [Hr1 [Hr2 [Hs HG]]].
    eapply trans_E; eauto.
    intros.
    eapply H2; eauto.
    repeat (split; auto); intros.
    unfold Ensembles.Included, Ensembles.In in *.
    edestruct (HG x) as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto.
    eexists; eexists; repeat (split; eauto).
    eapply V_exposed; eauto.
    eapply refl_V; eauto.
    eapply V_wf_val_r; eauto.
Qed.

(* Alternative Top Level Without Restricting The Free Variables To Decrease *)
Definition weak_G_top i Γ1 ρ1 Γ2 ρ2 :=
  wf_env ρ1 /\
  wf_env ρ2 /\
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

Lemma weak_G_top_G {i Γ1 ρ1 Γ2 ρ2}:
  weak_G_top i Γ1 ρ1 Γ2 ρ2 ->
  G i Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold weak_G_top, G.
  intros.
  destruct H as [Hr1 [Hr2 HG]].
  repeat (split; auto); intros.
  destruct (HG x) as [HG1 [HG2 HG3]].
  destruct HG3 as [v1' [v2 [Heqv1' [Heqv2 Hexv2]]]]; auto.
  rewrite Heqv1' in H0; inv H0.
  eexists; split; eauto; intros.
Qed.

Definition strong_trans_correct_top etop etop' :=
  forall i ρ1 ρ2,
    weak_G_top i (occurs_free etop) ρ1 (occurs_free etop') ρ2 ->
    E true i ρ1 etop ρ2 etop'.

Theorem top etop etop':
  trans (occurs_free etop) etop etop' ->
  strong_trans_correct_top etop etop'.
Proof.
  unfold strong_trans_correct_top.
  intros H.
  specialize (fundamental_property H);
    unfold trans_correct; intros.
  eapply H0; eauto.
  eapply weak_G_top_G; eauto.
Qed.

(* Reflexivity of [strong_trans_correct_top] *)
Corollary refl_strong_trans_correct_top etop :
  strong_trans_correct_top etop etop.
Proof.
  unfold strong_trans_correct_top.
  intros.
  specialize (fundamental_property' etop);
    unfold trans_correct.
  intros.
  eapply H0; eauto.
  eapply weak_G_top_G; eauto.
Qed.

(* However, [strong_trans_correct_top] is not transitive *)

(* Stronger [G_top] *)
Lemma G_top_weak_G_top {i Γ1 ρ1 Γ2 ρ2} :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  weak_G_top i Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold weak_G_top, G_top.
  intros.
  destruct H as [Hr1 [Hr2 [HS HG]]].
  repeat (split; auto); intros.
  - edestruct (HG x) as [v1' [v2 [Heqv1' [Heqv2 [Hex HV]]]]]; eauto.
  - unfold Ensembles.Included, Ensembles.In in *.
    edestruct (HG x) as [v1' [v2 [Heqv1' [Heqv2 [Hex HV]]]]]; eauto.
    eexists; split; eauto.
    eapply V_exposed; eauto.
  - inv H.
    edestruct (HG x) as [v1' [v2 [Heqv1' [Heqv2 [Hex HV]]]]]; eauto.
Qed.

(* Weaker [trans_correct_top] *)
Lemma strong_trans_correct_top_trans_correct_top etop etop' :
  strong_trans_correct_top etop etop' ->
  (occurs_free etop') \subset (occurs_free etop) ->
  trans_correct_top etop etop'.
Proof.
  unfold trans_correct_top, strong_trans_correct_top.
  intros.
  split; intros; auto.
  eapply H; eauto.
  eapply G_top_weak_G_top; eauto.
Qed.

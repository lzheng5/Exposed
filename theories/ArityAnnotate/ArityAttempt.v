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
From TrivialAnnotate Require Import Annotate.
From ArityAnnotate Require Import Base.

(* This file is used to illustrate that the trivial annotate functor is insufficient for arity-based annotations. *)

(* Trivial Web Annotation Based on Function Arities *)

(* We annotate function values with some Exposed web id based on their arities. *)
(* We annotate constructor values with a single Exposed web id. *)

(* Note this is basically annotating with `fun_tag`s in CertiCoq, but there are no internal webs. *)

Module A0 := LambdaANF.ANF.
Module A1 := LambdaWeb.ANF.
Module AM := AnnotateTop.

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

(* Cross-language Logical Relations *)

Import AM.VM.

Definition V := AM.V.
Definition E := AM.E.
Definition R := AM.R.
Definition G := AM.G.

(* Compatibility Lemmas *)
Definition trans_correct Γ e1 e2 :=
  forall i ρ1 ρ2,
    G i Γ ρ1 ρ2 ->
    E true i ρ1 e1 ρ2 e2.

Lemma ret_compat Γ x :
  (x \in Γ) ->
  trans_correct Γ (A0.Eret x) (A1.Eret x).
Proof.
  unfold trans_correct, E, AM.E, AM.VM.E, E'.
  intros.
  inv H2.
  - fcrush.
  - inv H3.
    edestruct (AM.G_get H0) as [v2 [Heqv2 HV]]; eauto.
    exists 1, (A1.Res v2); split; auto.
    + constructor.
      * constructor; auto.
      * eapply AM.V_exposed_res_r; eauto.
    + eapply V_mono; eauto; lia.
Qed.

Lemma Vfun_V Γ1 f xs e e' :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  forall {i ρ1 ρ2},
    wf_env ρ2 ->
    G i Γ1 ρ1 ρ2 ->
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    V i (A0.Vfun f ρ1 xs e) (Tag w (A1.Vfun f ρ2 xs e')).
Proof.
  unfold trans_correct.
  intros He i.
  induction i; simpl; intros; auto;
    repeat (split; auto); simpl;
    destruct (exposed_reflect (arity_to_web (length xs))); try contradiction;
    repeat (split; eauto);
    try (constructor; apply w0_exposed);
    intros.

  apply (He (i - (i - j)) ρ3 ρ4); auto.
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
  intros.
  inv H4.
  - exists 0, A1.OOT; split; simpl; eauto.
  - inv H5.
    edestruct (H1 (i - 1) (M.set f (A0.Vfun f ρ1 xs e) ρ1) (M.set f (Tag (arity_to_web (length xs)) (A1.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply AM.G_set; eauto.
      apply AM.G_mono with i; eauto; lia.
      * eapply Vfun_V; eauto.
        -- eapply AM.G_wf_env_r; eauto.
        -- apply AM.G_mono with i; eauto; lia.
    + exists (S j2), r2; split; auto.
      constructor.
      econstructor; eauto.
      eapply AM.R_exposed_res_r; eauto.
      eapply R_mono; eauto; lia.
Qed.

Lemma app_compat Γ xs f :
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  let w := arity_to_web (length xs) in
  (w \in Exposed) ->
  trans_correct Γ (A0.Eapp f xs) (A1.Eapp f w xs).
Proof.
  unfold trans_correct, G, E, AM.E, AM.VM.E, E'.
  intros.
  inv H4.
  - exists 0, A1.OOT; split; simpl; auto.
  - inv H5.
    edestruct (AM.G_get H2 f) as [fv2 [Heqfv2 HV]]; eauto.
    destruct i.
    fcrush.
    destruct fv2; simpl in HV;
      destruct HV as [Hv1 HV];
      destruct (exposed_reflect w); try contradiction;
      destruct HV as [Hex HV];
      destruct v; try contradiction.
    destruct HV as [Hlen HV].

    (* Stuck: need extra invariants between (arity_to_web (length xs)) and w *)
Abort.

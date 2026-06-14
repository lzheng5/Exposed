From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From LambdaANF Require Import ANF.
From LambdaWeb Require Import ANF.
From Annotate Require Import Annotate.

Module A0 := LambdaANF.ANF.
Module A1 := LambdaWeb.ANF.

Module AM := AnnotateTop.
Import AM.

(* Cross-language Compositionality *)

(* Adequacy *)
Theorem adequacy e1 e2:
  trans_correct e1 e2 ->
  forall ρ1 ρ2,
    wf_env ρ2 ->
    (forall k, G k (A0.occurs_free e1) ρ1 (A1.occurs_free e2) ρ2) ->
    forall j1 r1,
      A0.bstep_fuel ρ1 e1 j1 r1 ->
      exists j2 r2,
        A1.bstep_fuel true ρ2 e2 j2 r2 /\
        (forall k, R k r1 r2).
Proof.
  intros.
  unfold trans_correct in H.
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

  edestruct (A1.bstep_fuel_deterministic w w0 Hstep2 Hstep2'); subst; eauto.
Qed.

(* Behavioral Refinement *)
Inductive val_ref_ : A0.val -> A1.wval -> Prop :=
| Ref_Vfun :
  forall f1 ρ1 w xs1 e1 f2 ρ2 xs2 e2,
    val_ref_ (A0.Vfun f1 ρ1 xs1 e1) (Tag w (A1.Vfun f2 ρ2 xs2 e2))

| Ref_Vconstr_nil :
  forall w c,
    val_ref_ (A0.Vconstr c []) (Tag w (A1.Vconstr c []))

| Ref_Vconstr_cons :
  forall w c v1 v2 vs1 vs2,
    val_ref_ v1 v2 ->
    val_ref_ (A0.Vconstr c vs1) (Tag w (A1.Vconstr c vs2)) ->
    val_ref_ (A0.Vconstr c (v1 :: vs1)) (Tag w (A1.Vconstr c (v2 :: vs2))).

Hint Constructors val_ref_ : core.

Definition val_ref := val_ref_.

Hint Unfold val_ref : core.

Lemma val_ref_Vconstr c w vs1 vs2 :
  Forall2 val_ref vs1 vs2 ->
  val_ref (A0.Vconstr c vs1) (Tag w (A1.Vconstr c vs2)).
Proof.
  intros.
  induction H; simpl; auto.
Qed.

Theorem V_val_ref {v1 v2} :
  (forall i, V i v1 v2) ->
  val_ref v1 v2.
Proof.
  unfold val_ref.
  revert v2.
  induction v1 using val_ind'; intros; simpl.
  - specialize (H 0).
    destruct v2.
    simpl in H.
    destruct H as [Hwf HV].
    destruct (exposed_reflect w); inv HV.
    destruct v; try contradiction.
    inv H0.
    destruct l; try discriminate; auto.
  - destruct v2.
    pose proof (H 0) as H0; simpl in *.
    destruct H0 as [Hw HV].
    destruct (exposed_reflect w); inv HV.
    destruct v; try contradiction.
    destruct H1 as [Hc Hlen]; subst.

    destruct l0; simpl in *; inv Hlen.
    inv H0.

    assert (HV' : forall i, V i v1 t /\ V i (A0.Vconstr c l) (Tag w (A1.Vconstr c l0))).
    {
      intros.
      specialize (H (S i0)); simpl in *.
      destruct H as [_ HV]; subst.
      destruct (exposed_reflect w); try contradiction.
      destruct HV as [Hex [Hc HFV]]; subst; eauto.

      inv HFV.
      split.
      eapply V_mono; eauto; lia.

      assert (He' : exposed (Tag w (A1.Vconstr c l0))).
      {
        inv Hex; inv H6; auto.
      }

      assert (Hw' : wf_val (Tag w (A1.Vconstr c l0))).
      {
        constructor; intros; auto.
        inv Hw.
        inv H5; auto.
      }

      inv H6.
      inv Hw.
      inv H8.
      destruct i0; unfold V; simpl in *;
        destruct (exposed_reflect w); try contradiction;
        repeat (split; auto);
        simpl in *;
        rewrite_math (i0 - i0 = 0);
        rewrite_math (i0 - 0 = i0);
        try (eapply V_mono_Forall; eauto; lia).
    }

    assert (HV0 : forall i, V i v1 t) by (intros i0; destruct (HV' i0); auto).
    assert (HV1 : forall i, V i (A0.Vconstr c l) (Tag w (A1.Vconstr c l0))) by (intros i0; destruct (HV' i0); auto).
    auto.
  - specialize (H 0); simpl in *.
    destruct H as [Hw HV].
    destruct v2; try contradiction; auto.
    destruct (exposed_reflect w); inv HV.
    destruct v; try contradiction; auto.
Qed.

Corollary R_res_val_ref {v1 v2} :
  (forall i, R i (A0.Res v1) (A1.Res v2)) ->
  val_ref v1 v2.
Proof. intros; eapply V_val_ref; eauto. Qed.

(* Linking Preservation *)
(* Note the linking theorem is abstract so that it can work for any analyses. *)
Theorem preserves_linking f w x e1 e2 e1' e2' :
  (w \in Exposed) ->
  (forall w0, w0 \in Exposed -> w0 = w) ->
  trans_correct e1 e2 ->
  trans_correct e1' e2' ->
  trans_correct (A0.link f x e1 e1') (A1.link f w x e2 e2').
Proof.
  unfold A0.link, A1.link.
  intros.
  eapply fun_compat; eauto.
  eapply letapp_compat; eauto.
Qed.

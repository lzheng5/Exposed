From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From LambdaANF Require Import ANF.
From LambdaWeb Require Import ANF.
From ArityAnnotate Require Import Base Annotate.

Module AS := LambdaANF.ANF.
Module AT := LambdaWeb.ANF.

Module AM := AnnotateTop.
Import AM.

(* Cross-language Compositionality *)

(* Adequacy *)
Theorem adequacy e1 e2:
  trans_correct e1 e2 ->
  forall ρ1 ρ2,
    wf_env ρ2 ->
    (forall k, G k (AS.occurs_free e1) ρ1 ρ2) ->
    forall j1 r1,
      AS.bstep_fuel ρ1 e1 j1 r1 ->
      exists j2 r2,
        AT.bstep_fuel true ρ2 e2 j2 r2 /\
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

  edestruct (AT.bstep_fuel_deterministic w w0 Hstep2 Hstep2'); subst; eauto.
Qed.

(* Behavioral Refinement *)
Inductive val_ref : AS.val -> AT.wval -> Prop :=
| Ref_Vfun :
  forall f1 ρ1 xs1 e1 f2 ρ2 xs2 e2,
    length xs1 = length xs2 ->
    let w := arity_to_web (length xs2) in
    (w \in Exposed) ->
    val_ref (AS.Vfun f1 ρ1 xs1 e1) (Tag w (AT.Vfun f2 ρ2 xs2 e2))

| Ref_Vconstr_nil :
  forall c,
    (w_constr \in Exposed) ->
    val_ref (AS.Vconstr c []) (Tag w_constr (AT.Vconstr c []))

| Ref_Vconstr_cons :
  forall c v1 v2 vs1 vs2,
    (w_constr \in Exposed) ->
    val_ref v1 v2 ->
    val_ref (AS.Vconstr c vs1) (Tag w_constr (AT.Vconstr c vs2)) ->
    val_ref (AS.Vconstr c (v1 :: vs1)) (Tag w_constr (AT.Vconstr c (v2 :: vs2))).

Hint Constructors val_ref : core.

Lemma val_ref_Vconstr c vs1 vs2 :
  (w_constr \in Exposed) ->
  Forall2 val_ref vs1 vs2 ->
  val_ref (AS.Vconstr c vs1) (Tag w_constr (AT.Vconstr c vs2)).
Proof.
  intros.
  induction H0; simpl; auto.
Qed.

Theorem V_val_ref {v1 v2} :
  (forall i, V i v1 v2) ->
  val_ref v1 v2.
Proof.
  revert v2.
  induction v1 using val_ind'; intros; simpl.
  - specialize (H 0).
    destruct v2.
    simpl in H.
    destruct H as [Hwf HV].
    destruct (exposed_reflect w); inv HV.
    destruct v; try contradiction.
    simpl in *.
    destruct H0 as [Heqw [Heqc Hlen]]; subst.
    sauto.
  - destruct v2.
    pose proof (H 0) as H0; simpl in *.
    destruct H0 as [Hw HV].
    destruct (exposed_reflect w); inv HV.
    destruct v; try contradiction.
    simpl in *.
    destruct H1 as [Heqw [Hc Hlen]]; subst.

    destruct l0; simpl in *; inv Hlen.
    inv H0.
    inv H6.
    assert (HV' : forall i, V i v1 t /\ V i (AS.Vconstr c l) (Tag w_constr (AT.Vconstr c l0))).
    {
      intros.
      specialize (H (S i0)); simpl in *.
      destruct H as [_ HV]; subst.
      destruct (exposed_reflect w_constr); try contradiction.
      simpl in *.
      destruct HV as [Hex [Heqw [Hc HFV]]]; subst; eauto.

      inv HFV.
      split.
      eapply V_mono; eauto; lia.

      assert (He' : exposed (Tag w_constr (AT.Vconstr c l0))) by sauto.
      assert (Hw' : wf_val (Tag w_constr (AT.Vconstr c l0))) by sauto.

      destruct i0; unfold V; simpl in *;
        destruct (exposed_reflect w_constr); try contradiction;
        repeat (split; auto);
        simpl in *;
        rewrite_math (i0 - i0 = 0);
        rewrite_math (i0 - 0 = i0);
        try (eapply V_mono_Forall; eauto; lia).
    }

    assert (HV0 : forall i, V i v1 t) by sauto.
    assert (HV1 : forall i, V i (AS.Vconstr c l) (Tag w_constr (AT.Vconstr c l0))) by sauto.
    auto.
  - specialize (H 0); simpl in *.
    destruct H as [Hw HV].
    destruct v2; try contradiction; auto.
    destruct (exposed_reflect w); inv HV.
    destruct v; try contradiction; auto.
    simpl in *.
    sauto lq: on drew: off.
Qed.

Corollary R_res_val_ref {v1 v2} :
  (forall i, R i (AS.Res v1) (AT.Res v2)) ->
  val_ref v1 v2.
Proof. intros; eapply V_val_ref; eauto. Qed.

(* Linking Preservation *)

(* A dedicated link web *)
Definition w_link := arity_to_web 0.
Parameter w_link_exposed : w_link \in Exposed.

Theorem preserves_linking f x e1 e2 e1' e2' :
  trans_correct e1 e2 ->
  trans_correct e1' e2' ->
  trans_correct (AS.link f x e1 e1') (AT.link f w_link x e2 e2').
Proof.
  unfold AS.link, AT.link.
  intros.
  eapply fun_compat; eauto.
  eapply w_link_exposed; eauto.
  eapply letapp_compat; eauto.
  eapply w_link_exposed; eauto.
Qed.

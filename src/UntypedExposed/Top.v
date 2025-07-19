From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

Require Import UntypedExposed.Util.
Require Import UntypedExposed.ANF.
Require Import UntypedExposed.DPE.
Require Import UntypedExposed.Refl.
Require Import UntypedExposed.Refl2.

Module ReflTop.

(* A weaker top-level environment relation actually gives us
 * a stronger top-level correctness theorem *)

Lemma G_top_relate {i Γ1 ρ1 Γ2 ρ2}:
  Refl.G_top i Γ1 ρ1 Γ2 ρ2 ->
  Refl2.G_top i Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold Refl.G_top, Refl2.G_top.
  intros.
  destruct H as [H1 [H2 H3]].
  unfold Ensembles.Included, Ensembles.In, Dom_map in *.
  repeat split; intros.
  - edestruct H2 as [v1 Heqv1]; eauto.
    eexists; split; eauto.
    edestruct H3; eauto.
  - edestruct H2 as [v1 Heqv1]; eauto.
    edestruct H3 as [Hexv1 [v2 [Heqv2 HV]]]; eauto.
    eexists; split; eauto.
    eapply Refl.V_exposed; eauto.
  - inv H.
    edestruct H2 as [v1 Heqv1]; eauto.
    edestruct H3 as [Hexv1 [v2 [Heqv2 HV]]]; eauto.
Qed.

Theorem refl_relate {etop etop'} :
  Refl2.refl_correct_top etop etop' ->
  Refl.related_top etop etop'.
Proof.
  unfold Refl2.refl_correct_top, Refl.related_top.
  intros.
  apply H.
  apply G_top_relate; auto.
Qed.

End ReflTop.

Module DPETop.

Lemma Forall2_exposed_V_relate: forall i j vs1 vs2,
    Forall exposed vs1 ->
    j <= i ->
    (forall n : nat, n < S i -> forall v1 v2 : val, exposed v1 -> DPE.V n v1 v2 <-> Refl.V n v1 v2) ->
    Forall2 (DPE.V j) vs1 vs2 <-> Forall2 (Refl.V j) vs1 vs2.
Proof.
  intros.
  revert vs2 H1.
  induction vs1; intros.
  - split; intros; inv H2; auto.
  - inv H.
    split; intros; inv H; constructor; auto.
    + eapply H1; try lia; auto.
    + apply IHvs1; auto.
    + eapply H1; try lia; auto.
    + apply IHvs1; auto.
Qed.

Lemma exposed_V_relate :
  DPE.live_map_inv ->
  forall i v1 v2,
    exposed v1 ->
    DPE.V i v1 v2 <-> Refl.V i v1 v2.
Proof.
  intro HE.
  intro i.
  induction i using strong_induction; intros.
  destruct i.
  - unfold DPE.V, Refl.V.
    destruct v1; destruct v2; split; auto; destruct H2; auto.
  - split; simpl in *; intro.
    + destruct v1; destruct v2; auto.
      destruct H1.
      inv H0.
      erewrite (HE w0) in *; auto.
      destruct H2.
      repeat split; auto; intros.
      destruct H3; auto.

      assert (HE' : DPE.E' DPE.V (exposedb w0) (i - (i - j)) ρ3 e ρ4 e0).
      {
        eapply H1 with (vs1 := vs1) (vs2 := vs2); try lia; eauto.
        eapply Forall2_exposed_V_relate; eauto.
        intros.
        eapply H; eauto; try lia.
      }

      unfold Refl.E', Refl.R', DPE.E', DPE.R' in *.
      intros.
      destruct (HE' _ _ H9 H10) as [j2 [r2 [bstep_e0 HR']]].
      exists j2; exists r2; split; auto.
      destruct r1; destruct r2; auto.
      eapply H; try lia; auto.
      inv H10.
      destruct (exposed_reflect w0); try contradiction.
      inv H12; auto.
    + destruct v1; destruct v2; auto.
      destruct H1.
      inv H0.
      erewrite (HE w0) in *; auto.
      destruct H2.
      repeat split; auto.
      intros.
      destruct H3; auto.

      assert (HE' : Refl.E' Refl.V (exposedb w0) (i - (i - j)) ρ3 e ρ4 e0).
      {
        eapply H1 with (vs1 := vs1) (vs2 := vs2); try lia; eauto.
        eapply Forall2_exposed_V_relate; eauto.
        intros.
        eapply H; eauto; try lia.
      }

      unfold Refl.E', Refl.R', DPE.E', DPE.R' in *.
      intros.
      destruct (HE' _ _ H9 H10) as [j2 [r2 [bstep_e0 HR']]].
      exists j2; exists r2; split; auto.
      destruct r1; destruct r2; auto.
      eapply H; try lia; auto.
      inv H10.
      destruct (exposed_reflect w0); try contradiction.
      inv H12; auto.
Qed.

Lemma exposed_R_relate {i r1 r2}:
  DPE.live_map_inv ->
  exposed_res r1 ->
  DPE.R i r1 r2 <-> Refl.R i r1 r2.
Proof.
  intros HExp Hr1.
  unfold DPE.R, Refl.R.
  split; intros;
    destruct r1;
    destruct r2;
    auto; inv Hr1;
    apply exposed_V_relate; auto.
Qed.

Lemma exposed_E_relate {i ρ1 ρ2 e1 e2}:
  DPE.live_map_inv ->
  DPE.E true i ρ1 e1 ρ2 e2 <-> Refl.E true i ρ1 e1 ρ2 e2.
Proof.
  unfold DPE.E, Refl.E.
  intros HExp.
  split; intros;
    edestruct H as [j2 [r2 [He2 HR]]]; eauto;
    eexists; eexists; split; eauto;
    eapply exposed_R_relate; eauto;
    inv H1; auto.
Qed.

Lemma G_top_relate {i Γ1 ρ1 Γ2 ρ2}:
  DPE.live_map_inv ->
  Refl2.G_top i Γ1 ρ1 Γ2 ρ2 ->
  DPE.G_top i Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold DPE.G_top, Refl2.G_top, Ensembles.Included, Ensembles.In, Dom_map.
  intros.
  destruct (H0 x) as [G1 [G2 G3]].
  destruct G1 as [v1 [Heqv1 Hexv1]]; eauto.
  eexists; repeat split; eauto; intros.
  destruct G3 as [v1' [v2' [Heqv1' [Heqv2' HV]]]]; eauto.
  constructor; auto.
  rewrite Heqv1 in Heqv1'; inv Heqv1'.
  eexists; split; eauto.
  apply exposed_V_relate; auto.
Qed.

Theorem top {etop etop'} :
  DPE.live_map_inv ->
  DPE.trans (occurs_free etop) etop etop' ->
  Refl2.refl_correct_top etop etop'.
Proof.
  unfold Refl2.refl_correct_top.
  intros HExp HTrans.
  intros.
  specialize (DPE.fundamental_property HTrans);
    unfold trans_correct; intros.
  eapply exposed_E_relate; eauto.
  eapply H0; eauto.
  - apply Included_refl.
  - eapply DPE.free_trans_inv; eauto.
  - eapply DPE.G_top_G; eauto.
    eapply G_top_relate; eauto.
Qed.

Theorem top' {etop etop'} :
  DPE.live_map_inv ->
  DPE.trans (occurs_free etop) etop etop' ->
  Refl.related_top etop etop'.
Proof.
  intros.
  apply ReflTop.refl_relate.
  apply top; auto.
Qed.

End DPETop.

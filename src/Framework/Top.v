From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF Exposed Refl Id DPE ConstProp Defunc.

Lemma exposed_V_relate_Forall :
  forall i (V1 V2 : nat -> wval -> wval -> Prop),
    (forall n : nat, n < S i -> forall v1 v2, exposed v1 -> V1 n v1 v2 <-> V2 n v1 v2) ->
    forall j vs1 vs2,
      j <= i ->
      Forall exposed vs1 ->
      Forall2 (V1 j) vs1 vs2 <-> Forall2 (V2 j) vs1 vs2.
Proof.
  intros.
  revert vs2 j H0.
  induction H1; simpl; intros.
  - split; intros; inv H1; auto.
  - split; intros; inv H3; constructor; auto;
      solve [ apply H; try lia; auto |
              apply IHForall; auto ].
Qed.

Module ReflTop.

  (* Relate Id and Refl as Equivalence *)

  Import ExposedUtil.
  Import Id.EM.EG.EV.

  Lemma exposed_V_relate :
    forall i v1 v2,
      exposed v1 ->
      V i v1 v2 <-> Refl.V i v1 v2.
  Proof.
    intro i.
    induction i using lt_wf_rec; intros.
    destruct i.
    - destruct v1; destruct v2; split; simpl; intros; auto;
        destruct H1 as [Hv1 [Hv2 [Hw HV]]]; subst;
        repeat (split; auto);
        destruct v; destruct v0; try contradiction;
        simpl in *; tauto.
    - split; simpl in *; intro Hv;
        destruct Hv as [Hv1 [Hv2 HV]];
        repeat (split; auto);
        destruct v1; destruct v2; auto;
        destruct HV; subst; split; auto.
      + destruct v; destruct v0; try contradiction; simpl in *.
        * destruct H2.
          split; auto; intros.

          assert (HE' : E' V (exposedb w0) (i - (i - j)) ρ3 e ρ4 e0).
          {
            inv H0.
            eapply H2 with (vs1 := vs1) (vs2 := vs2); try lia; eauto;
              intros; destruct H4; auto.
            eapply exposed_V_relate_Forall; eauto; try lia.
          }

          unfold Refl.E', E', Refl.R', R' in *.
          intros.
          edestruct HE' as [j2 [r2 [He0 HR']]]; eauto.
          exists j2; exists r2; split; auto.
          destruct r1; destruct r2; auto.
          eapply H; try lia; auto.
          inv H9.
          destruct (exposed_reflect w0); try contradiction.
          inv H11; auto.
          inv H0; contradiction.
        * destruct H2 as [Hc HV]; subst.
          repeat split; auto.
          rewrite normalize_step in *; try lia.
          eapply exposed_V_relate_Forall with (V1 := V); eauto.
          inv H0; auto.

      + unfold V_refl in *.
        destruct v; destruct v0; try contradiction.
        * destruct H2.
          split; auto; intros.

          assert (HE' : Refl.E' Refl.V (exposedb w0) (i - (i - j)) ρ3 e ρ4 e0).
          {
            inv H0.
            eapply H2 with (vs1 := vs1) (vs2 := vs2); try lia; eauto.
            eapply exposed_V_relate_Forall with (V1 := V); eauto; try lia.
          }

          unfold Refl.E', E', Refl.R', R' in *.
          intros.
          edestruct HE' as [j2 [r2 [He0 HR']]]; eauto.
          exists j2; exists r2; split; auto.
          destruct r1; destruct r2; auto.
          eapply H; try lia; auto.
          inv H10.
          destruct (exposed_reflect w0); try contradiction.
          inv H12; auto.
          inv H0; contradiction.
        * destruct H2 as [Hc HV]; subst.
          repeat split; auto.
          rewrite normalize_step in *; try lia.
          eapply exposed_V_relate_Forall with (V1 := V); eauto.
          inv H0; auto.
  Qed.

  Lemma exposed_R_relate {i r1 r2}:
    exposed_res r1 ->
    R i r1 r2 <-> Refl.R i r1 r2.
  Proof.
    intros Hr1.
    unfold R, Refl.R.
    split; intros;
      destruct r1;
      destruct r2;
      auto; inv Hr1;
      apply exposed_V_relate; auto.
  Qed.

  Lemma exposed_E_relate {i ρ1 ρ2 e1 e2}:
    E true i ρ1 e1 ρ2 e2 <-> Refl.E true i ρ1 e1 ρ2 e2.
  Proof.
    unfold E, Refl.E, E', Refl.E'.
    split; intros;
    edestruct H as [j2 [r2 [He2 HR]]]; eauto;
      eexists; eexists; split; eauto;
      eapply exposed_R_relate; eauto;
      inv H1; auto.
  Qed.

  Lemma G_top_relate {i Γ1 ρ1 Γ2 ρ2}:
    Id.G_top i Γ1 ρ1 Γ2 ρ2 <-> Refl.G_top i Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold Id.G_top, Refl.G_top.
    split; intros;
      destruct H as [Hr1 [Hr2 [HS HG]]];
      repeat (split; auto); intros;
      edestruct HG as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto;
      eexists; eexists; repeat (split; eauto);
      eapply exposed_V_relate; eauto.
  Qed.

  Theorem top_relate {etop etop'} :
    Id.trans_correct_top etop etop' <-> Refl.related_top etop etop'.
  Proof.
    unfold Id.trans_correct_top, Refl.related_top.
    split; intros HR;
      destruct HR;
      split; auto; intros;
      eapply exposed_E_relate; eauto;
      apply H0; auto;
      apply G_top_relate; auto.
  Qed.

End ReflTop.

Module Top (LM : LSig) (VT : VTrans LM).

  (* Relate any logical relation derivable by ExposedV to Id at the top level *)

  Module EV := ExposedV LM VT.
  Import EV.
  Import LM.

  Module IV := Id.EM.EG.EV.
  Import ExposedUtil.

  Lemma exposed_V_relate :
    forall i v1 v2,
      exposed v1 ->
      IV.V i v1 v2 <-> EV.V i v1 v2.
  Proof.
    intro i.
    induction i using lt_wf_rec; intros.
    destruct i.
    - destruct v1; destruct v2; split; simpl; intros; auto;
        destruct H1 as [Hv1 [Hv2 HV]]; subst;
        repeat (split; auto);
        destruct (LM.L ! w) eqn:Heq1; auto.
      + apply LM.L_inv_Some in Heq1.
        inv H0; contradiction.
      + destruct HV; auto.
      + apply LM.L_inv_Some in Heq1.
        inv H0; contradiction.
      + destruct HV; auto.
    - split; simpl in *; intro Hv;
        destruct Hv as [Hv1 [Hv2 HV]];
        repeat (split; auto);
        destruct v1; destruct v2; auto.
      + destruct HV; subst.
        destruct (LM.L ! w0) eqn:Heq1.
        * apply LM.L_inv_Some in Heq1.
          inv H0; contradiction.
        * unfold V_refl in *.
          destruct v; destruct v0; try contradiction.
          -- destruct H2.
             repeat (split; auto); intros.

             assert (HE' : IV.E' IV.V (exposedb w0) (i - (i - j)) ρ3 e ρ4 e0).
             {
               inv H0.
               eapply H2 with (vs1 := vs1) (vs2 := vs2); try lia; eauto.
               eapply exposed_V_relate_Forall; eauto; try lia.
             }

             unfold EV.E', IV.E', EV.R', IV.R' in *.
             intros.
             edestruct HE' as [j2 [r2 [He0 HR']]]; eauto.
             exists j2; exists r2; split; auto.
             destruct r1; destruct r2; auto.
             eapply H; try lia; auto.
             inv H10.
             destruct (exposed_reflect w0); try contradiction.
             inv H12; auto.
             inv H0; contradiction.
          -- destruct H2 as [Hc HV]; subst.
             repeat split; auto.
             rewrite normalize_step in *; try lia.
             eapply exposed_V_relate_Forall with (V1 := IV.V); eauto.
             inv H0; auto.

      + destruct (LM.L ! w) eqn:Heq1.
        * apply LM.L_inv_Some in Heq1.
          inv H0; contradiction.
        * unfold V_refl in *.
          destruct HV as [Hw HV]; subst; split; auto.
          destruct v; destruct v0; try contradiction.
          -- destruct HV as [Hlen HV].
             split; auto; intros.

             assert (HE' : EV.E' EV.V (exposedb w0) (i - (i - j)) ρ3 e ρ4 e0).
             {
               inv H0.
               eapply HV with (vs1 := vs1) (vs2 := vs2); try lia; eauto.
               eapply exposed_V_relate_Forall with (V1 := IV.V); eauto; try lia.
             }

             unfold EV.E', IV.E', EV.R', IV.R' in *.
             intros.
             edestruct HE' as [j2 [r2 [He0 HR']]]; eauto.
             exists j2; exists r2; split; auto.
             destruct r1; destruct r2; auto.
             eapply H; try lia; auto.
             destruct (exposed_reflect w0); try contradiction.
             inv H8.
             inv H10; auto.
             inv H0; contradiction.
          -- destruct HV as [Hc HV]; subst.
             repeat split; auto.
             rewrite normalize_step in *; try lia.
             eapply exposed_V_relate_Forall with (V1 := IV.V); eauto.
             inv H0; auto.
  Qed.

  Lemma exposed_R_relate {i r1 r2}:
    exposed_res r1 ->
    IV.R i r1 r2 <-> EV.R i r1 r2.
  Proof.
    intros Hr1.
    unfold IV.R, EV.R.
    split; intros;
      destruct r1;
      destruct r2;
      auto; inv Hr1;
      apply exposed_V_relate; auto.
  Qed.

  Lemma exposed_E_relate {i ρ1 ρ2 e1 e2}:
    IV.E true i ρ1 e1 ρ2 e2 <-> EV.E true i ρ1 e1 ρ2 e2.
  Proof.
    unfold IV.E, EV.E, IV.E', EV.E'.
    split; intros;
    edestruct H as [j2 [r2 [He2 HR]]]; eauto;
      eexists; eexists; split; eauto;
      eapply exposed_R_relate; eauto;
      inv H1; auto.
  Qed.

End Top.

Module DPETop.

  (* Relate DPE to Id at the top level *)

  Module M := Top DPE.LM DPE.VTransM.
  Import M.

  Lemma G_top_relate {i Γ1 ρ1 Γ2 ρ2}:
    Id.weak_G_top i Γ1 ρ1 Γ2 ρ2 ->
    DPE.G_top i Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold DPE.G_top, Id.weak_G_top, Ensembles.Included, Ensembles.In, Dom_map.
    intros.
    destruct H as [Hr1 [Hr2 HG]].
    repeat (split; auto); intros.
    destruct (HG x) as [G1 [G2 G3]].
    destruct G1 as [v1 [Heqv1 Hexv1]]; eauto.
    eexists; repeat split; eauto; intros.
    destruct G3 as [v1' [v2' [Heqv1' [Heqv2' HV]]]]; eauto.
    constructor; auto.
    rewrite Heqv1 in Heqv1'; inv Heqv1'.
    eexists; split; eauto.
    apply exposed_V_relate; auto.
  Qed.

  Theorem top_relate {etop etop'} :
    DPE.trans_correct_top etop etop' ->
    Id.strong_trans_correct_top etop etop'.
  Proof.
    unfold DPE.trans_correct_top, Id.strong_trans_correct_top.
    intros.
    eapply exposed_E_relate; eauto.
    eapply H; eauto.
    eapply G_top_relate; eauto.
  Qed.

  Theorem top {etop etop'} :
    DPE.trans (occurs_free etop) etop etop' ->
    Id.strong_trans_correct_top etop etop'.
  Proof.
    intros.
    apply top_relate.
    apply DPE.top; auto.
  Qed.

  Theorem top' {etop etop'} :
    DPE.trans (occurs_free etop) etop etop' ->
    Id.trans_correct_top etop etop'.
  Proof.
    intros.
    apply strong_trans_correct_top_trans_correct_top.
    apply top; auto.
    eapply DPE.trans_exp_inv; eauto.
  Qed.

End DPETop.

Module DefuncTop.

  (* Relate Defunc to Id at the top level *)

  Module M := Top Defunc.LM Defunc.VTransM.
  Import M.

  Lemma G_top_relate {i Γ1 ρ1 Γ2 ρ2}:
    Id.weak_G_top i Γ1 ρ1 Γ2 ρ2 ->
    Defunc.G_top i Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold Defunc.G_top, Id.weak_G_top, Ensembles.Included, Ensembles.In, Dom_map.
    intros.
    destruct H as [Hr1 [Hr2 HG]].
    repeat (split; auto); intros.
    destruct (HG x) as [G1 [G2 G3]].
    destruct G1 as [v1 [Heqv1 Hexv1]]; eauto.
    eexists; repeat split; eauto; intros.
    destruct G3 as [v1' [v2' [Heqv1' [Heqv2' HV]]]]; eauto.
    constructor; auto.
    rewrite Heqv1 in Heqv1'; inv Heqv1'.
    eexists; split; eauto.
    apply exposed_V_relate; auto.
  Qed.

  Theorem top_relate {etop etop'} :
    Defunc.trans_correct_top etop etop' ->
    Id.strong_trans_correct_top etop etop'.
  Proof.
    unfold Defunc.trans_correct_top, Id.strong_trans_correct_top.
    intros.
    eapply exposed_E_relate; eauto.
    eapply H; eauto.
    eapply G_top_relate; eauto.
  Qed.

  Theorem top {etop etop'} :
    Defunc.trans (occurs_free etop) etop etop' ->
    Id.strong_trans_correct_top etop etop'.
  Proof.
    intros.
    apply top_relate.
    apply Defunc.top; auto.
  Qed.

  Theorem top' {etop etop'} :
    Defunc.trans (occurs_free etop) etop etop' ->
    Id.trans_correct_top etop etop'.
  Proof.
    intros.
    apply strong_trans_correct_top_trans_correct_top.
    apply top; auto.
    eapply Defunc.trans_exp_inv; eauto.
  Qed.

End DefuncTop.

Module ConstPropTop.

  (* Relate ConstProp to Id at the top level *)

  Module M := Top ConstProp.LM ConstProp.VTransM.
  Import M.

  Lemma G_top_relate {i Γ1 ρ1 Γ2 ρ2}:
    Id.weak_G_top i Γ1 ρ1 Γ2 ρ2 ->
    ConstProp.G_top i Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold ConstProp.G_top, Id.weak_G_top, Ensembles.Included, Ensembles.In, Dom_map.
    intros.
    destruct H as [Hr1 [Hr2 HG]].
    repeat (split; auto); intros.
    destruct (HG x) as [G1 [G2 G3]].
    destruct G1 as [v1 [Heqv1 Hexv1]]; eauto.
    eexists; repeat split; eauto; intros.
    destruct G3 as [v1' [v2' [Heqv1' [Heqv2' HV]]]]; eauto.
    constructor; auto.
    rewrite Heqv1 in Heqv1'; inv Heqv1'.
    eexists; split; eauto.
    apply exposed_V_relate; auto.
  Qed.

  Theorem top_relate {etop etop'} :
    ConstProp.trans_correct_top etop etop' ->
    Id.strong_trans_correct_top etop etop'.
  Proof.
    unfold ConstProp.trans_correct_top, Id.strong_trans_correct_top.
    intros.
    eapply exposed_E_relate; eauto.
    eapply H; eauto.
    eapply G_top_relate; eauto.
  Qed.

  Theorem top {etop etop'} :
    C_inv_top (occurs_free etop) ->
    ConstProp.trans (occurs_free etop) etop etop' ->
    Id.strong_trans_correct_top etop etop'.
  Proof.
    intros.
    apply top_relate.
    apply ConstProp.top; auto.
  Qed.

  Theorem top' {etop etop'} :
    C_inv_top (occurs_free etop) ->
    ConstProp.trans (occurs_free etop) etop etop' ->
    Id.trans_correct_top etop etop'.
  Proof.
    intros.
    apply strong_trans_correct_top_trans_correct_top.
    apply top; auto.
    eapply ConstProp.trans_exp_inv; eauto.
  Qed.

End ConstPropTop.

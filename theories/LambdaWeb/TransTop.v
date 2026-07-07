From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From LambdaWeb Require Import ANF Exposed Refl Id DPE ConstProp Defunc.

(* Relate all the transformation top-level relations to the identity transformation top-level relation *)

Lemma exposed_V_relate_Forall_aux :
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

Module Top (LM : WebSelSig) (VT : VTrans LM).

  (* Relate any logical relation derivable by ExposedV to Refl at the top level *)

  Module EV := ExposedV LM VT.
  Import EV.
  Import LM.

  Module RM := Refl.RM.EG.EV.
  Import ExposedUtil.

  Lemma exposed_V_relate :
    forall i v1 v2,
      exposed v1 ->
      RM.V i v1 v2 <-> EV.V i v1 v2.
  Proof.
    intro i.
    induction i using lt_wf_rec; intros.
    destruct i.
    - destruct v1; destruct v2; split; simpl; intros; auto;
        destruct H1 as [Hv1 [Hv2 HV]]; subst;
        repeat (split; auto);
        destruct (Refl.LM.L ! w) eqn:Heq1; auto.
      + apply Refl.LM.L_inv_Some in Heq1.
        inv H0; contradiction.
      + destruct HV; subst.
        destruct (L ! w0) eqn:Heq0; auto.
      + destruct (L ! w) eqn:Heq0; auto.
        apply LM.L_inv_Some in Heq0.
        inv H0; contradiction.
    - split; simpl in *; intro Hv;
        destruct Hv as [Hv1 [Hv2 HV]];
        repeat (split; auto);
        destruct v1; destruct v2; auto.
      + destruct (Refl.LM.L ! w) eqn:Heq1;
          destruct (L ! w) eqn:Heq2.
        * apply LM.L_inv_Some in Heq2.
          inv H0; contradiction.
        * apply Refl.LM.L_inv_Some in Heq1.
          inv H0; contradiction.
        * apply LM.L_inv_Some in Heq2.
          inv H0; contradiction.
        * destruct HV as [Heqw HV]; subst.
          split; auto.
          unfold V_refl in *.
          destruct v; destruct v0; try contradiction.
          -- destruct HV as [Hlen HV].
             repeat (split; auto); intros.

             assert (HE' : E' RM.V (exposedb w0) (i - (i - j)) ρ3 e ρ4 e0).
             {
               inv H0.
               eapply HV with (vs1 := vs1) (vs2 := vs2); try lia; eauto.
               eapply exposed_V_relate_Forall_aux; eauto; try lia.
             }

             unfold E', R' in *.
             intros.
             edestruct HE' as [j2 [r2 [He0 HR']]]; eauto.
             exists j2; exists r2; split; auto.
             destruct r1; destruct r2; auto.
             eapply H; try lia; auto.
             destruct (exposed_reflect w0); try contradiction.
             2 : { fcrush. }
             assert (Hexr : exposed_res (Res w)) by (eapply bstep_fuel_exposed_inv; eauto).
             inv Hexr; auto.
          -- destruct HV as [Hc HV]; subst.
             repeat split; auto.
             rewrite normalize_step in *; try lia.
             eapply exposed_V_relate_Forall_aux with (V1 := RM.V); eauto.
             inv H0; auto.
      + destruct (L ! w) eqn:Heq1;
          destruct (Refl.LM.L ! w) eqn:Heq2.
        * apply LM.L_inv_Some in Heq1.
          inv H0; contradiction.
        * apply LM.L_inv_Some in Heq1.
          inv H0; contradiction.
        * apply Refl.LM.L_inv_Some in Heq2.
          inv H0; contradiction.
        * unfold V_refl in *.
          destruct HV as [Hw HV]; subst; split; auto.
          destruct v; destruct v0; try contradiction.
          -- destruct HV as [Hlen HV].
             split; auto; intros.

             assert (HE' : E' EV.V (exposedb w0) (i - (i - j)) ρ3 e ρ4 e0).
             {
               inv H0.
               eapply HV with (vs1 := vs1) (vs2 := vs2); try lia; eauto.
               eapply exposed_V_relate_Forall_aux with (V1 := RM.V); eauto; try lia.
             }

             unfold E', R' in *.
             intros.
             edestruct HE' as [j2 [r2 [He0 HR']]]; eauto.
             exists j2; exists r2; split; auto.
             destruct r1; destruct r2; auto.
             eapply H; try lia; auto.
             destruct (exposed_reflect w0); try contradiction.
             fcrush.
             fcrush.
          -- destruct HV as [Hc HV]; subst.
             repeat split; auto.
             rewrite normalize_step in *; try lia.
             eapply exposed_V_relate_Forall_aux with (V1 := RM.V); eauto.
             fcrush.
  Qed.

  Lemma exposed_R_relate {i r1 r2}:
    exposed_res r1 ->
    RM.R i r1 r2 <-> EV.R i r1 r2.
  Proof.
    intros Hr1.
    unfold RM.R, EV.R.
    split; intros;
      destruct r1;
      destruct r2;
      auto; inv Hr1;
      apply exposed_V_relate; auto.
  Qed.

  Lemma exposed_E_relate {i ρ1 ρ2 e1 e2}:
    RM.E true i ρ1 e1 ρ2 e2 <-> EV.E true i ρ1 e1 ρ2 e2.
  Proof.
    unfold RM.E, EV.E, E'.
    split; intros;
    edestruct H as [j2 [r2 [He2 HR]]]; eauto;
      eexists; eexists; split; eauto;
      eapply exposed_R_relate; eauto;
      inv H1; auto.
  Qed.

End Top.

(* TODO: refactor the top-level further *)

Module IdTop.

  (* Relate Id to Id at the top level *)

  Module M := Top Id.LM Id.VTransM.
  Import M.

  Lemma G_top_relate {i Γ1 ρ1 ρ2}:
    Refl.G_top i Γ1 ρ1 ρ2 <-> Id.G_top i Γ1 ρ1 ρ2.
  Proof.
    unfold Refl.G_top, Id.G_top, Ensembles.Included, Ensembles.In, Dom_map.
    split; intros;
      destruct H as [Hr1 [Hr2 HG]];
      repeat (split; auto); intros;
      destruct (HG x) as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; auto;
      eexists; eexists; repeat (split; eauto); intros;
      apply exposed_V_relate; auto.
  Qed.

  Theorem top_relate {etop etop'} :
    Id.trans_correct_top etop etop' <-> Refl.related_top etop etop'.
  Proof.
    unfold Id.trans_correct_top, Refl.related_top.
    split; intros H;
      inv H;
      split; auto; intros;
      eapply exposed_E_relate; eauto;
      eapply H1; eauto;
      eapply G_top_relate; eauto.
  Qed.

  Theorem top {etop etop'} :
    Id.trans (occurs_free etop) etop etop' ->
    Refl.related_top etop etop'.
  Proof.
    intros.
    eapply Id.top in H; auto.
    apply top_relate; auto.
  Qed.

End IdTop.

Module DPETop.

  (* Relate DPE to Id at the top level *)

  Module M := Top DPE.LM DPE.VTransM.
  Import M.

  Lemma G_top_relate {i Γ1 ρ1 ρ2}:
    Refl.G_top i Γ1 ρ1 ρ2 <-> DPE.G_top i Γ1 ρ1 ρ2.
  Proof.
    unfold Refl.G_top, DPE.G_top, Ensembles.Included, Ensembles.In, Dom_map.
    split; intros;
      destruct H as [Hr1 [Hr2 HG]];
      repeat (split; auto); intros;
      destruct (HG x) as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; auto;
      eexists; eexists; repeat (split; eauto); intros;
      apply exposed_V_relate; auto.
  Qed.

  Theorem top_relate {etop etop'} :
    DPE.trans_correct_top etop etop' <-> Refl.related_top etop etop'.
  Proof.
    unfold DPE.trans_correct_top, Refl.related_top.
    split; intros H;
      inv H;
      split; auto; intros;
      eapply exposed_E_relate; eauto;
      eapply H1; eauto;
      eapply G_top_relate; eauto.
  Qed.

  Theorem top {etop etop'} :
    DPE.trans (occurs_free etop) etop etop' ->
    Refl.related_top etop etop'.
  Proof.
    intros.
    eapply DPE.top in H; auto.
    apply top_relate; auto.
  Qed.

End DPETop.

Module DefuncTop.

  (* Relate Defunc to Id at the top level *)

  Module M := Top Defunc.LM Defunc.VTransM.
  Import M.

  Lemma G_top_relate {i Γ1 ρ1 ρ2}:
    Refl.G_top i Γ1 ρ1 ρ2 <-> Defunc.G_top i Γ1 ρ1 ρ2.
  Proof.
    unfold Refl.G_top, Defunc.G_top, Ensembles.Included, Ensembles.In, Dom_map.
    split; intros;
      destruct H as [Hr1 [Hr2 HG]];
      repeat (split; auto); intros;
      destruct (HG x) as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; auto;
      eexists; eexists; repeat (split; eauto); intros;
      apply exposed_V_relate; auto.
  Qed.

  Theorem top_relate {etop etop'} :
    Defunc.trans_correct_top etop etop' <-> Refl.related_top etop etop'.
  Proof.
    unfold Defunc.trans_correct_top, Refl.related_top.
    split; intros H;
      inv H;
      split; auto; intros;
      eapply exposed_E_relate; eauto;
      eapply H1; eauto;
      eapply G_top_relate; eauto.
  Qed.

  Theorem top {etop etop'} :
    Defunc.trans (occurs_free etop) etop etop' ->
    Refl.related_top etop etop'.
  Proof.
    intros.
    eapply Defunc.top in H; eauto.
    apply top_relate; auto.
  Qed.

End DefuncTop.

Module ConstPropTop.

  (* Relate ConstProp to Id at the top level *)

  Module M := Top ConstProp.LM ConstProp.VTransM.
  Import M.

  Lemma G_top_relate {i Γ1 ρ1 ρ2}:
    Refl.G_top i Γ1 ρ1 ρ2 <-> ConstProp.G_top i Γ1 ρ1 ρ2.
  Proof.
    unfold Refl.G_top, ConstProp.G_top, Ensembles.Included, Ensembles.In, Dom_map.
    split; intros;
      destruct H as [Hr1 [Hr2 HG]];
      repeat (split; auto); intros;
      destruct (HG x) as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; auto;
      eexists; eexists; repeat (split; eauto); intros;
      apply exposed_V_relate; auto.
  Qed.

  Theorem top_relate {etop etop'} :
    ConstProp.trans_correct_top etop etop' <-> Refl.related_top etop etop'.
  Proof.
    unfold ConstProp.trans_correct_top, Refl.related_top.
    split; intros H;
      inv H;
      split; auto; intros;
      eapply exposed_E_relate; eauto;
      eapply H1; eauto;
      eapply G_top_relate; eauto.
  Qed.

  Theorem top {etop etop'} :
    C_inv_top (occurs_free etop) ->
    ConstProp.trans (occurs_free etop) etop etop' ->
    Refl.related_top etop etop'.
  Proof.
    intros.
    eapply ConstProp.top in H0; eauto.
    apply top_relate; auto.
  Qed.

End ConstPropTop.

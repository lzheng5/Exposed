From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util RelComp.
From LambdaANF Require Import ANF Comp.
From Annotate Require Import AnnotateComp.
From LambdaWeb Require Import W0 ANF Comp.

(* Compositionality of The Cross-language Pipeline

   Unannotated ANF -> Annotate ANF

   Assume unique exposed web id *)

(* Adequacy / Preservation of Termination *)
(* Behavioral Refinement *)
(* Linking Preservation *)

Module A0 := LambdaANF.ANF.
Module A1 := LambdaWeb.ANF.

Module C0 := LambdaANF.Comp.
Module C1 := LambdaWeb.Comp.

Module AC := AnnotateComp.
Module AM := AC.AM.

Section Comp_n.

  Definition Top_n n m := Cross (Cross (C0.Top_n n) (fun e1 e2 => AM.trans_correct e1 e2)) (C1.Top_n m).

  Definition V_n n m := Cross (Cross (C0.V_n n) (fun v1 v2 => forall k, AM.V k v1 v2)) (C1.V_n m).

  Definition R_n n m := Cross (Cross (C0.R_n n) (fun v1 v2 => forall k, AM.R k v1 v2)) (C1.R_n m).

  Definition G_n n m Γ1 Γ2 := Cross (Cross (C0.G_n n Γ1 Γ2) (fun ρ1 ρ2 => forall k, AM.G k Γ1 ρ1 Γ2 ρ2)) (C1.G_n m Γ1 Γ2).

  Lemma V_n_wf_val_r n m v1 v2:
    V_n n m v1 v2 ->
    wf_val v2.
  Proof.
    unfold V_n, Cross.
    intros H.
    destruct H as [v2' [[v1' [HC0 HA]] HC1]].
    specialize (HA 0).
    eapply AM.VM.V_wf_val_r in HA; eauto.
    edestruct C1.V_n_wf_val; eauto.
  Qed.

  Lemma R_res_inv_l v1 r2 :
    (forall i, AM.R i (A0.Res v1) r2) ->
    exists v2, r2 = A1.Res v2 /\ (forall i, AM.V i v1 v2).
  Proof.
    intros.
    pose proof (H 0) as H0.
    eapply AM.VM.R_res_inv_l in H0.
    destruct H0 as [v2 [Heqv2 _]]; subst.
    eexists; split; eauto.
  Qed.

  Lemma R_n_V_n n m v1 v2:
    R_n n m (A0.Res v1) (A1.Res v2) ->
    V_n n m v1 v2.
  Proof.
    unfold R_n, V_n, Cross.
    intros H.
    destruct H as [r2' [[r1' [HC0 HA]] HC1]].
    apply C0.R_n_Res_inv in HC0.
    destruct HC0 as [v1' [Heqv1' HC0]]; subst.
    edestruct R_res_inv_l as [v2' [Heqv2' HV]]; eauto; subst.
    eexists; split; eauto.
    eapply C1.R_n_V_n; eauto.
  Qed.

  Lemma R_n_Res_inv n m v1 r2 :
    R_n n m (A0.Res v1) r2 ->
    exists v2, r2 = A1.Res v2 /\ V_n n m v1 v2.
  Proof.
    unfold R_n, V_n, Cross.
    intros.
    destruct H as [r2' [[r1' [HC0 HA]] HC1]].
    apply C0.R_n_Res_inv in HC0.
    destruct HC0 as [v1' [Heqv1' HC0]]; subst.
    edestruct R_res_inv_l as [v2' [Heqv2' HV]]; eauto; subst.

    apply C1.R_n_Res_inv in HC1.
    2 : { specialize (HV 0).
          eapply AM.VM.V_wf_val_r; eauto. }
    destruct HC1 as [v2'' [Heqv2'' HC1]]; subst.
    eexists; split; eauto.
  Qed.

  Lemma Top_n_subset n m e1 e2 :
    Top_n n m e1 e2 ->
    A1.occurs_free e2 \subset A0.occurs_free e1.
  Proof.
    unfold Top_n, Cross.
    intros H.
    destruct H as [e2' [[e1' [HC0 HA]] HC1]].
    apply C0.Top_n_subset in HC0.
    apply C1.Top_n_subset in HC1.
    apply AM.trans_correct_subset in HA.
    eapply Included_trans; eauto.
    eapply Included_trans; eauto.
  Qed.

  Lemma G_n_wf_env { n m Γ1 Γ2 ρ1 ρ2 } :
    G_n n m Γ1 Γ2 ρ1 ρ2 ->
    wf_env ρ2.
  Proof.
    unfold G_n, Cross.
    intros H.
    destruct H as [ρ2' [[ρ1' [HC0 HA]] HC1]].
    specialize (HA 0).
    apply AM.G_wf_env_r in HA.
    eapply (C1.G_n_wf_env HC1); eauto.
  Qed.

  Lemma G_n_subset n m Γ1 Γ2 ρ1 Γ3 Γ4 ρ2 :
    G_n n m Γ1 Γ2 ρ1 ρ2 ->
    Γ3 \subset Γ1 ->
    Γ4 \subset Γ3 ->
    G_n n m Γ3 Γ4 ρ1 ρ2.
  Proof.
    unfold G_n, Cross.
    intros H.
    destruct H as [ρ2' [[ρ1' [HC0 HA]] HC1]].

    intros.
    eapply C0.G_n_subset in HC0; eauto.
    eapply C1.G_n_subset in HC1; eauto.
    eexists; split; eauto.
    eexists; split; eauto.
    intros.
    specialize (HA k).
    eapply AM.G_subset; eauto.
  Qed.

End Comp_n.

Section Adequacy.

  Lemma Top_n_R_n n m e1 e2:
    Top_n n m e1 e2 ->
    forall ρ1 ρ2,
      wf_env ρ2 ->
      G_n n m (A0.occurs_free e1) (A1.occurs_free e2) ρ1 ρ2 ->
      forall j1 r1,
        A0.bstep_fuel ρ1 e1 j1 r1 ->
        exists j2 r2,
          A1.bstep_fuel true ρ2 e2 j2 r2 /\
            R_n n m r1 r2.
  Proof.
    intros Hrel.
    unfold Top_n, G_n, R_n, Cross in *.
    destruct Hrel as [e2' [[e1' [HC0 HA]] HC1]].
    intros.

    destruct H0 as [ρ2' [[ρ1' [HG0 HAG]] HG1]].
    edestruct (C0.Top_n_R_n _ _ _ HC0) with (ρ2 := ρ1') as [j1' [r1' [Hstep1' HRn0]]]; eauto.

    assert (wf_env ρ2').
    {
      specialize (HAG 0).
      eapply AM.G_wf_env_r; eauto.
    }

    edestruct (AC.adequacy _ _ HA) with (ρ2 := ρ2') as [j2' [r2' [Hstep2' HAR]]]; eauto.
    - intros.
      eapply AM.G_subset; eauto.
      eapply C0.Top_n_subset; eauto.
      eapply AM.trans_correct_subset; eauto.
    - edestruct (C1.Top_n_R_n _ _ _ HC1) with (ρ2 := ρ2) as [j2 [r2 [Hstep2 HRn1]]]; eauto.
      + eapply C1.G_n_subset; eauto.
        * eapply AM.trans_correct_subset in HA; eauto.
          eapply Included_trans; eauto.
          eapply C0.Top_n_subset; eauto.
        * eapply C1.Top_n_subset; eauto.
      + eexists; eexists; split; eauto.
  Qed.

  (* Termination Preservation *)
  Theorem Top_n_preserves_termination n m e1 e2 :
    Top_n n m e1 e2 ->
    forall ρ1 ρ2,
      wf_env ρ2 ->
      G_n n m (A0.occurs_free e1) (A1.occurs_free e2) ρ1 ρ2 ->
      forall j1 v1,
        A0.bstep_fuel ρ1 e1 j1 (A0.Res v1) ->
        exists j2 v2,
          A1.bstep_fuel true ρ2 e2 j2 (A1.Res v2) /\
            V_n n m v1 v2.
  Proof.
    intros.
    edestruct Top_n_R_n with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
    edestruct R_n_Res_inv as [v2 [Heq HVn]]; eauto; subst.
    eexists; eexists; split; eauto.
  Qed.

End Adequacy.

Section Refinement.

  Definition val_ref := Cross (Cross C0.val_ref AC.val_ref) C1.val_ref.

  Lemma R_n_res_val_ref {n m v1 v2} :
    R_n n m (A0.Res v1) (A1.Res v2) ->
    val_ref v1 v2.
  Proof.
    unfold R_n, val_ref, Cross.
    intros.
    destruct H as [r2' [[r1' [HC0 HR]] HC1]].
    edestruct C0.R_n_Res_inv as [v1' [Heqv1' HV1]]; eauto; subst.
    eapply C0.R_n_res_val_ref in HC0; eauto.
    edestruct R_res_inv_l as [v2' [Heqv2' HV2]]; eauto; subst.
    eapply C1.R_n_res_val_ref in HC1; eauto.

    eexists; split; eauto.
    - eexists; split; eauto.
      eapply AC.V_val_ref; eauto.
    - specialize (HV2 0).
      eapply AM.VM.V_wf_val_r; eauto.
    - specialize (HV2 0).
      eapply AM.V_exposed_r; eauto.
  Qed.

  (* Behavioral Refinement *)
  Theorem Top_n_val_ref n m e1 e2 :
    Top_n n m e1 e2 ->
    forall ρ1 ρ2,
      wf_env ρ2 ->
      G_n n m (A0.occurs_free e1) (A1.occurs_free e2) ρ1 ρ2 ->
      forall j1 v1,
        A0.bstep_fuel ρ1 e1 j1 (A0.Res v1) ->
        exists j2 v2,
          A1.bstep_fuel true ρ2 e2 j2 (A1.Res v2) /\
            val_ref v1 v2.
  Proof.
    intros.
    edestruct Top_n_R_n with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
    edestruct R_n_Res_inv as [v2 [Heq HVn]]; eauto; subst.
    eexists; eexists; split; eauto.
    eapply R_n_res_val_ref; eauto.
  Qed.

End Refinement.

Section Linking.

  (* Linking Preservation *)
  Lemma Top_n_preserves_linking f w x n n' m m' e1 e2 e1' e2' :
    (w \in Exposed) ->
    Top_n n m e1 e2 ->
    Top_n n' m' e1' e2' ->
    Top_n (n + n') (m + m') (A0.link f x e1 e1') (A1.link f w x e2 e2').
  Proof.
    unfold Top_n, Cross.
    intros Hw.
    intros.
    destruct H as [e3 [[e4 [HC0 HA1]] HC1]].
    destruct H0 as [e3' [[e4' [HC0' HA1']] HC1']].

    eapply (C0.Top_n_preserves_linking f x n n') in HC0; eauto.
    eapply (AC.preserves_linking f w x e4 e3 e4' e3') in HA1; eauto.
    eapply (C1.Top_n_preserves_linking f w x m m') in HC1; eauto.
    eapply Exposed_unique; eauto.
  Qed.

End Linking.

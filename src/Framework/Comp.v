From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util RelComp ANF0 Refl0 Refl0Comp Annotate ANF Refl ReflComp.

Module A0 := ANF0.
Module A1 := ANF.

Module R0 := Refl0.
Module R1 := Refl.

Module C0 := Refl0Comp.
Module C1 := ReflComp.

(* Compositionality of the cross-language pipeline

   Unannotated ANF0 -> Annotate ANF
 *)

(* Adequacy / Preservation of Termination *)
(* Behavioral Refinement *)
(* Linking Preservation *)

Section Comp.

  Definition Top_n n m := Cross (Cross (C0.Top_n n) Annotate.trans_correct_top) (C1.Top_n m).

  Definition V_n n m := Cross (Cross (C0.V_n n) (fun v1 v2 => forall k, Annotate.V k v1 v2)) (C1.V_n m).

  Definition R_n n m := Cross (Cross (C0.R_n n) (fun v1 v2 => forall k, Annotate.R k v1 v2)) (C1.R_n m).

  Definition G_n n m Γ1 Γ2 := Cross (Cross (C0.G_n n Γ1 Γ2) (fun ρ1 ρ2 => forall k, Annotate.G_top k Γ1 ρ1 Γ2 ρ2)) (C1.G_n m Γ1 Γ2).

  Lemma R_n_V_n n m v1 v2:
    R_n n m (A0.Res v1) (A1.Res v2) ->
    V_n n m v1 v2.
  Proof.
    unfold R_n, V_n, Cross.
    intros H.
    destruct H as [r2' [[r1' [HC0 HA]] HC1]].
    apply C0.R_n_Res_inv in HC0.
    destruct HC0 as [v1' [Heqv1' HC0]]; subst.
    edestruct Annotate.R_res_inv_l as [v2' [Heqv2' _]]; eauto; subst.
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
    edestruct Annotate.R_res_inv_l as [v2' [Heqv2' HV]]; eauto; subst.

    apply C1.R_n_Res_inv in HC1.
    2 : { specialize (HV 0).
          eapply Annotate.V_wf_val_r; eauto. }
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
    apply Annotate.trans_correct_top_subset in HA.
    eapply Included_trans; eauto.
    eapply Included_trans; eauto.
  Qed.

End Comp.

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
    eapply C0.G_n_subset; eauto.
    apply Included_refl.
    eapply C0.Top_n_subset; eauto.

    assert (wf_env ρ2').
    {
      specialize (HAG 0).
      eapply Annotate.G_top_wf_env_r; eauto.
    }

    edestruct (Annotate.adequacy _ _ HA) with (ρ2 := ρ2') as [j2' [r2' [Hstep2' HAR]]]; eauto.
    - intros.
      specialize (HAG k).
      eapply Annotate.G_top_subset; eauto.
      eapply C0.Top_n_subset; eauto.
      eapply Annotate.trans_correct_top_subset; eauto.
    - edestruct (C1.Top_n_R_n _ _ _ HC1) with (ρ2 := ρ2) as [j2 [r2 [Hstep2 HRn1]]]; eauto.
      eapply C1.G_n_subset; eauto.
      + eapply Annotate.trans_correct_top_subset in HA; eauto.
        eapply Included_trans; eauto.
        eapply C0.Top_n_subset; eauto.
      + eapply C1.Top_n_subset; eauto.
      + eexists; eexists; split; eauto.
  Qed.

  (* Termination Perservation *)
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

  Definition val_ref := Cross (Cross C0.val_ref Annotate.val_ref) C1.val_ref.

  Lemma R_n_res_val_ref {n m v1 v2} :
    R_n n m (A0.Res v1) (A1.Res v2) ->
    val_ref v1 v2.
  Proof.
    unfold R_n, val_ref, Cross.
    intros.
    destruct H as [r2' [[r1' [HC0 HR]] HC1]].
    edestruct C0.R_n_Res_inv as [v1' [Heqv1' HV1]]; eauto; subst.
    eapply C0.R_n_res_val_ref in HC0; eauto.
    edestruct Annotate.R_res_inv_l as [v2' [Heqv2' HV2]]; eauto; subst.
    eapply C1.R_n_res_val_ref in HC1; eauto.
    eexists; split; eauto.
    - eexists; split; eauto.
      eapply Annotate.V_val_ref; eauto.
    - specialize (HV2 0).
      eapply Annotate.V_wf_val_r; eauto.
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

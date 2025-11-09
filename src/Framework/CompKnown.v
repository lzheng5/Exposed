From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util RelComp ANF0 Refl0 Refl0Comp KnownAnnotate ANF Refl ReflComp.

Module A0 := ANF0.
Module A1 := ANF.

Module R0 := Refl0.
Module R1 := Refl.

Module C0 := Refl0Comp.
Module C1 := ReflComp.

(* Compositionality of the cross-language pipeline

   Unannotated ANF -> Annotate ANF
 *)

(* Adequacy / Preservation of Termination *)
(* Behavioral Refinement *)
(* Linking Preservation *)

Module AM := KnownAnnotate.

Module M.

  Section Comp_n.

    Variable K : AM.known_map.

    Definition Top_n n m := Cross (Cross (C0.Top_n n) (fun e1 e2 => AM.trans_correct_top K e1 e2)) (C1.Top_n m).

    Definition V_n n m := Cross (Cross (C0.V_n n) (fun v1 v2 => forall k, AM.V K k v1 v2)) (C1.V_n m).

    Definition R_n n m := Cross (Cross (C0.R_n n) (fun v1 v2 => forall k, AM.R K k v1 v2)) (C1.R_n m).

    Definition G_n n m Γ1 Γ2 := Cross (Cross (C0.G_n n Γ1 Γ2) (fun ρ1 ρ2 => forall k, AM.G_top K k Γ1 ρ1 Γ2 ρ2)) (C1.G_n m Γ1 Γ2).

    Lemma V_n_wf_val_r n m v1 v2:
      V_n n m v1 v2 ->
      wf_val v2.
    Proof.
      unfold V_n, Cross.
      intros H.
      destruct H as [v2' [[v1' [HC0 HA]] HC1]].
      specialize (HA 0).
      eapply AM.V_wf_val_r in HA; eauto.
      edestruct C1.V_n_wf_val; eauto.
    Qed.

    Lemma R_res_inv_l v1 r2 :
      (forall i, AM.R K i (A0.Res v1) r2) ->
      exists v2, r2 = A1.Res v2 /\ (forall i, AM.V K i v1 v2).
    Proof.
      intros.
      pose proof (H 0) as H0.
      eapply AM.R_res_inv_l in H0.
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
            eapply AM.V_wf_val_r; eauto. }
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
      apply AM.trans_correct_top_subset in HA.
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
      apply AM.G_top_wf_env_r in HA.
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
      eapply AM.G_top_subset; eauto.
    Qed.

  End Comp_n.

  Section Adequacy.

    Lemma Top_n_R_n K n m e1 e2:
      AM.known_map_inv K ->
      Top_n K n m e1 e2 ->
      forall ρ1 ρ2,
        wf_env ρ2 ->
        G_n K n m (A0.occurs_free e1) (A1.occurs_free e2) ρ1 ρ2 ->
        forall j1 r1,
          A0.bstep_fuel ρ1 e1 j1 r1 ->
          exists j2 r2,
            A1.bstep_fuel true ρ2 e2 j2 r2 /\
            R_n K n m r1 r2.
    Proof.
      intros HK Hrel.
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
        eapply AM.G_top_wf_env_r; eauto.
      }

      edestruct (AM.adequacy K _ _ HK HA) with (ρ2 := ρ2') as [j2' [r2' [Hstep2' HAR]]]; eauto.
      - intros.
        eapply AM.G_top_subset; eauto.
        eapply C0.Top_n_subset; eauto.
        eapply AM.trans_correct_top_subset; eauto.
      - edestruct (C1.Top_n_R_n _ _ _ HC1) with (ρ2 := ρ2) as [j2 [r2 [Hstep2 HRn1]]]; eauto.
        + eapply C1.G_n_subset; eauto.
          * eapply AM.trans_correct_top_subset in HA; eauto.
            eapply Included_trans; eauto.
            eapply C0.Top_n_subset; eauto.
          * eapply C1.Top_n_subset; eauto.
        + eexists; eexists; split; eauto.
    Qed.

    (* Termination Perservation *)
    Theorem Top_n_preserves_termination K n m e1 e2 :
      AM.known_map_inv K ->
      Top_n K n m e1 e2 ->
      forall ρ1 ρ2,
        wf_env ρ2 ->
        G_n K n m (A0.occurs_free e1) (A1.occurs_free e2) ρ1 ρ2 ->
        forall j1 v1,
          A0.bstep_fuel ρ1 e1 j1 (A0.Res v1) ->
          exists j2 v2,
            A1.bstep_fuel true ρ2 e2 j2 (A1.Res v2) /\
            V_n K n m v1 v2.
    Proof.
      intros.
      edestruct Top_n_R_n with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
      edestruct R_n_Res_inv as [v2 [Heq HVn]]; eauto; subst.
      eexists; eexists; split; eauto.
    Qed.

  End Adequacy.

  Section Refinement.

    Definition val_ref := Cross (Cross C0.val_ref AM.val_ref) C1.val_ref.

    Lemma R_n_res_val_ref {K n m v1 v2} :
      R_n K n m (A0.Res v1) (A1.Res v2) ->
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
        eapply AM.V_val_ref; eauto.
      - specialize (HV2 0).
        eapply AM.V_wf_val_r; eauto.
    Qed.

    (* Behavioral Refinement *)
    Theorem Top_n_val_ref K n m e1 e2 :
      AM.known_map_inv K ->
      Top_n K n m e1 e2 ->
      forall ρ1 ρ2,
        wf_env ρ2 ->
        G_n K n m (A0.occurs_free e1) (A1.occurs_free e2) ρ1 ρ2 ->
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
    Lemma Top_n_preserves_linking K f w x n n' m m' e1 e2 e1' e2' :
      K ! f = None ->
      K ! x = None ->
      (w \in Exposed) ->
      Top_n K n m e1 e2 ->
      Top_n K n' m' e1' e2' ->
      Top_n K (n + n') (m + m') (A0.link f x e1 e1') (A1.link f w x e2 e2').
    Proof.
      unfold Top_n, Cross.
      intros HKf HKx Hw.
      intros.
      destruct H as [e3 [[e4 [HC0 HA1]] HC1]].
      destruct H0 as [e3' [[e4' [HC0' HA1']] HC1']].

      eapply (C0.Top_n_preserves_linking f x n n') in HC0; eauto.
      eapply (AM.preserves_linking K f w x e4 e3 e4' e3') in HA1; eauto.
      eapply (C1.Top_n_preserves_linking f w x m m') in HC1; eauto.
    Qed.

  End Linking.

End M.

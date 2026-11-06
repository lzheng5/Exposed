From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util RelComp.
From LambdaANF Require Import ANF Comp.
From SemAnnotate Require Import Comp.
From LambdaWeb Require Import ANF Comp.

(* Compositionality of The Cross-language Pipeline with Some Semantic Analysis

   Unannotated ANF -> Annotate ANF

   Assume unique exposed web id *)

(* Adequacy / Preservation of Termination *)
(* Behavioral Refinement *)
(* Linking Preservation *)

Module A0 := LambdaANF.ANF.
Module A1 := LambdaWeb.ANF.

Module C0 := LambdaANF.Comp.
Module C1 := LambdaWeb.Comp.

Module C := SemAnnotate.Comp.

Section Comp_n.

  Definition Top_n n m := Cross (Cross (C0.Top_n n) C.trans_correct_top) (C1.Top_n m).

  (* The relations are parameterized by the analysis context `θ` and the web map
     context `ω` of the semantic analysis component. *)
  Definition V_n θ ω n m := Cross (Cross (C0.V_n n) (C.V θ ω)) (C1.V_n m).

  Definition R_n θ ω n m := Cross (Cross (C0.R_n n) (C.R θ ω)) (C1.R_n m).

  Definition G_n θ ω n m Γ1 := Cross (Cross (C0.G_n n Γ1) (C.G θ ω Γ1)) (C1.G_n m Γ1).

  Lemma V_n_wf_val_r θ ω n m v1 v2:
    V_n θ ω n m v1 v2 ->
    wf_val v2.
  Proof.
    unfold V_n, Cross.
    intros [v2' [[v1' [HC0 HA]] HC1]].
    apply (proj1 (C1.V_n_wf_val _ _ _ HC1)).
    eapply C.V_wf_val_r; eauto.
  Qed.

  Lemma R_n_V_n θ ω n m v1 v2:
    R_n θ ω n m (A0.Res v1) (A1.Res v2) ->
    V_n θ ω n m v1 v2.
  Proof.
    unfold R_n, V_n, Cross.
    intros [r2' [[r1' [HC0 HA]] HC1]].
    destruct (C0.R_n_Res_inv _ _ _ HC0) as [v1' [-> HV0]].
    destruct (C.R_res_inv_l _ _ _ _ HA) as [v2' [-> HVA]].
    exists v2'; split; [exists v1'; split; assumption |].
    eapply C1.R_n_V_n; eauto.
  Qed.

  Lemma R_n_Res_inv θ ω n m v1 r2 :
    R_n θ ω n m (A0.Res v1) r2 ->
    exists v2, r2 = A1.Res v2 /\ V_n θ ω n m v1 v2.
  Proof.
    intros H.
    pose proof H as Hc.
    unfold R_n, Cross in Hc.
    destruct Hc as [r2' [[r1' [HC0 HA]] HC1]].
    destruct (C0.R_n_Res_inv _ _ _ HC0) as [v1' [-> HV0]].
    destruct (C.R_res_inv_l _ _ _ _ HA) as [v2' [-> HVA]].
    destruct (C1.R_n_Res_inv _ _ _ HC1
                (C.V_wf_val_r _ _ _ _ HVA) (C.V_exposed_r _ _ _ _ HVA))
      as [v2 [-> HV1]].
    exists v2; split; [reflexivity |].
    eapply R_n_V_n; exact H.
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
    apply C.trans_correct_top_subset in HA.
    eapply Included_trans; eauto.
    eapply Included_trans; eauto.
  Qed.

  Lemma G_n_wf_env {θ ω n m Γ1 ρ1 ρ2} :
    G_n θ ω n m Γ1 ρ1 ρ2 ->
    wf_env ρ2.
  Proof.
    unfold G_n, Cross.
    intros [ρ2' [[ρ1' [HC0 HA]] HC1]].
    apply (proj1 (C1.G_n_wf_env HC1)).
    exact (C.G_wf_env_r HA).
  Qed.

  Lemma G_n_subset θ ω n m Γ1 Γ2 ρ1 ρ2 :
    G_n θ ω n m Γ1 ρ1 ρ2 ->
    Γ2 \subset Γ1 ->
    G_n θ ω n m Γ2 ρ1 ρ2.
  Proof.
    unfold G_n, Cross.
    intros [ρ2' [[ρ1' [HC0 HA]] HC1]] Hsub.
    exists ρ2'; split; [exists ρ1'; split |].
    - eapply C0.G_n_subset; eauto.
    - eapply C.G_subset; eauto.
    - eapply C1.G_n_subset; eauto.
  Qed.

  (* The empty environments are related when there are no free variables. *)
  Lemma G_n_empty θ ω n m Γ :
    Γ \subset (Empty_set _) ->
    G_n θ ω n m Γ (M.empty _) (M.empty _).
  Proof.
    intros Hclosed.
    unfold G_n, Cross.
    exists (M.empty _); split; [exists (M.empty _); split |].
    - (* LambdaANF *)
      unfold C0.G_n.
      induction n as [| n IHn]; [constructor |].
      econstructor; [| exact IHn].
      intros k x Hx; apply Hclosed in Hx; inv Hx.
    - (* the semantic analysis component *)
      apply C.G_empty; exact Hclosed.
    - (* LambdaWeb *)
      unfold C1.G_n.
      induction m as [| m IHm]; [constructor |].
      econstructor; [| exact IHm].
      intros k; split; [| split].
      + constructor; intros x v Hget; rewrite M.gempty in Hget; discriminate.
      + constructor; intros x v Hget; rewrite M.gempty in Hget; discriminate.
      + intros x Hx; apply Hclosed in Hx; inv Hx.
  Qed.

End Comp_n.

Section Adequacy.

  Lemma Top_n_adequacy n m e1 e2:
    Top_n n m e1 e2 ->
    exists θ ω,
      C.An.analysis_context_escape_ok θ /\
      C.Aw.valid_web_map_context ω θ /\
        forall ρ1 ρ2,
          G_n θ ω n m (A0.occurs_free e1) ρ1 ρ2 ->
          forall j1 r1,
            A0.bstep_fuel ρ1 e1 j1 r1 ->
            exists j2 r2,
              A1.bstep_fuel true ρ2 e2 j2 r2 /\
                R_n θ ω n m r1 r2.
  Proof.
    unfold Top_n, Cross.
    intros [e2' [[e1' [HC0 HA]] HC1]].

    (* the contexts come from the semantic analysis component *)
    destruct (C.adequacy e1' e2' HA) as [θ [ω [Hesc [Hω Hrun]]]].
    exists θ, ω.
    split; [exact Hesc |].
    split; [exact Hω |].

    intros ρ1 ρ2 HG j1 r1 Hstep.
    unfold G_n, Cross in HG.
    destruct HG as [ρ2' [[ρ1' [HG0 HGA]] HG1]].

    (* LambdaANF *)
    destruct (C0.Top_n_adequacy _ _ _ HC0 ρ1 ρ1' HG0 j1 r1 Hstep)
      as [j1' [r1' [Hstep1' HR0]]].

    (* semantic analysis *)
    assert (HGA' : C.G θ ω (A0.occurs_free e1') ρ1' ρ2').
    { eapply C.G_subset; [exact HGA |].
      eapply C0.Top_n_subset; eauto. }
    destruct (Hrun ρ1' ρ2' HGA' j1' r1' Hstep1') as [j2' [r2' [Hstep2' HRA]]].

    (* LambdaWeb *)
    assert (Hwf2' : wf_env ρ2') by exact (C.G_wf_env_r HGA).
    assert (Hwf2 : wf_env ρ2) by exact (proj1 (C1.G_n_wf_env HG1) Hwf2').
    assert (HG1' : C1.G_n m (A1.occurs_free e2') ρ2' ρ2).
    { eapply C1.G_n_subset; [exact HG1 |].
      eapply Included_trans; [eapply C.trans_correct_top_subset; eauto |].
      eapply C0.Top_n_subset; eauto. }
    destruct (C1.Top_n_adequacy _ _ _ HC1 ρ2' ρ2 Hwf2' Hwf2 HG1' j2' r2' Hstep2')
      as [j2 [r2 [Hstep2 HR1]]].

    exists j2, r2; split; [exact Hstep2 |].
    unfold R_n, Cross.
    exists r2'; split; [exists r1'; split; assumption | exact HR1].
  Qed.

  Lemma Top_n_adequacy_closed n m e1 e2:
    Top_n n m e1 e2 ->
    A0.occurs_free e1 \subset (Empty_set _) ->
    exists θ ω,
      C.An.analysis_context_escape_ok θ /\
      C.Aw.valid_web_map_context ω θ /\
        forall j1 r1,
          A0.bstep_fuel (M.empty _) e1 j1 r1 ->
          exists j2 r2,
            A1.bstep_fuel true (M.empty _) e2 j2 r2 /\
              R_n θ ω n m r1 r2.
  Proof.
    intros Hrel Hclosed.
    destruct (Top_n_adequacy n m e1 e2 Hrel) as [θ [ω [Hesc [Hω Hrun]]]].
    exists θ, ω.
    split; [exact Hesc |].
    split; [exact Hω |].
    intros j1 r1 Hstep.
    eapply Hrun; [| exact Hstep].
    apply G_n_empty; exact Hclosed.
  Qed.

  (* Termination Preservation *)
  Theorem Top_n_preserves_termination n m e1 e2 :
    Top_n n m e1 e2 ->
    exists θ ω,
      C.An.analysis_context_escape_ok θ /\
      C.Aw.valid_web_map_context ω θ /\
        forall ρ1 ρ2,
          G_n θ ω n m (A0.occurs_free e1) ρ1 ρ2 ->
          forall j1 v1,
            A0.bstep_fuel ρ1 e1 j1 (A0.Res v1) ->
            exists j2 v2,
              A1.bstep_fuel true ρ2 e2 j2 (A1.Res v2) /\
                V_n θ ω n m v1 v2.
  Proof.
    intros Hrel.
    destruct (Top_n_adequacy n m e1 e2 Hrel) as [θ [ω [Hesc [Hω Hrun]]]].
    exists θ, ω.
    split; [exact Hesc |].
    split; [exact Hω |].
    intros ρ1 ρ2 HG j1 v1 Hstep.
    destruct (Hrun ρ1 ρ2 HG j1 _ Hstep) as [j2 [r2 [Hstep2 HR]]].
    destruct (R_n_Res_inv _ _ _ _ _ _ HR) as [v2 [-> HV]].
    exists j2, v2; split; assumption.
  Qed.

  Theorem Top_n_preserves_termination_closed n m e1 e2 :
    Top_n n m e1 e2 ->
    A0.occurs_free e1 \subset (Empty_set _) ->
    exists θ ω,
      C.An.analysis_context_escape_ok θ /\
      C.Aw.valid_web_map_context ω θ /\
        forall j1 v1,
          A0.bstep_fuel (M.empty _) e1 j1 (A0.Res v1) ->
          exists j2 v2,
            A1.bstep_fuel true (M.empty _) e2 j2 (A1.Res v2) /\
              V_n θ ω n m v1 v2.
  Proof.
    intros Hrel Hclosed.
    destruct (Top_n_adequacy_closed n m e1 e2 Hrel Hclosed) as [θ [ω [Hesc [Hω Hrun]]]].
    exists θ, ω.
    split; [exact Hesc |].
    split; [exact Hω |].
    intros j1 v1 Hstep.
    destruct (Hrun j1 _ Hstep) as [j2 [r2 [Hstep2 HR]]].
    destruct (R_n_Res_inv _ _ _ _ _ _ HR) as [v2 [-> HV]].
    exists j2, v2; split; assumption.
  Qed.

End Adequacy.

(*
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
      eapply C.VM.V_wf_val_r; eauto.
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
    edestruct Top_n_adequacy with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
    edestruct R_n_Res_inv as [v2 [Heq HVn]]; eauto; subst.
    eexists; eexists; split; eauto.
    eapply R_n_res_val_ref; eauto.
  Qed.

End Refinement.
 *)

Section Linking.

  (* Linking Preservation *)
  Lemma Top_n_preserves_linking f w x n n' m m' e1 e2 e1' e2' :
    (w \in Exposed) ->
    f <> x ->
    ~ (f \in A0.occurs_free e1) ->
    ~ (f \in A0.occurs_free e1') ->
    Top_n n m e1 e2 ->
    Top_n n' m' e1' e2' ->
    Top_n (n + n') (m + m') (A0.link f x e1 e1') (A1.link f w x e2 e2').
  Proof.
    unfold Top_n, Cross.
    intros Hw Hfx Hf1 Hf1'.
    intros.
    destruct H as [e3 [[e4 [HC0 HA1]] HC1]].
    destruct H0 as [e3' [[e4' [HC0' HA1']] HC1']].

    pose proof HC0 as HC0''.
    eapply (C0.Top_n_preserves_linking f x n n') in HC0''; eauto.

    assert (Hf4 : ~ Ensembles.In var (A0.occurs_free e4) f).
    {
      eapply C0.Top_n_subset in HC0; eauto.
    }

    assert (Hf4' :  ~ Ensembles.In var (C.AS.occurs_free e4') f).
    {
      eapply C0.Top_n_subset in HC0'; eauto.
    }

    eapply (C.preserves_linking f w x e4 e4' e3 e3') in HA1; eauto.
    eapply (C1.Top_n_preserves_linking f w x m m') in HC1; eauto.
  Qed.

End Linking.

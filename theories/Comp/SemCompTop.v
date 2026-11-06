From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util RelComp.
From LambdaANF Require Import ANF Comp.
From Comp Require Import SemComp.
From LambdaWeb Require Import UniqueExposed ANF Comp.
From Erase Require Import Erase Comp.

(* Compositionality of The Cross-language Pipeline with Erase

   Unannotated ANF -> Annotate ANF -> Unannotated ANF

   Assume unique exposed web id

   Note this is completely analysis independent

   The only difference between [SemCompTop.v] and [CompTop.v] is that the linking preservation theorem needs to have more premises *)

(* Adequacy / Preservation of Termination *)
(* Behavioral Refinement *)
(* Linking Preservation *)

Module A0 := LambdaANF.ANF.
Module A1 := LambdaWeb.ANF.

Module C0 := LambdaANF.Comp.
Module C1 := LambdaWeb.Comp.

Module C := SemComp.
Module EC := Erase.Comp.

Module An := SemAnnotate.ValueSetAnalysis.
Module Aw := SemAnnotate.SimpleWebAssign.

Section Comp_n.

  Definition Top_n n m p := Cross (Cross (C.Top_n n m) Erase.trans_correct_top) (C0.Top_n p).

  (* The relations are parameterized by the analysis context `θ` and the web map
     context `ω` of the semantic analysis component. *)
  Definition V_n θ ω n m p :=
    Cross (Cross (C.V_n θ ω n m) (fun v1 v2 => forall k, Erase.V k v1 v2)) (C0.V_n p).

  Definition R_n θ ω n m p :=
    Cross (Cross (C.R_n θ ω n m) (fun v1 v2 => forall k, Erase.R k v1 v2)) (C0.R_n p).

  Definition G_n θ ω n m p Γ1 :=
    Cross (Cross (C.G_n θ ω n m Γ1) (fun ρ1 ρ2 => forall k, Erase.G_top k Γ1 ρ1 ρ2)) (C0.G_n p Γ1).

  Lemma R_n_V_n θ ω n m p v1 v2:
    R_n θ ω n m p (A0.Res v1) (A0.Res v2) ->
    V_n θ ω n m p v1 v2.
  Proof.
    unfold R_n, V_n, Cross.
    intros [r2' [[r1' [HC HA]] HC1]].
    destruct (C.R_n_Res_inv _ _ _ _ _ _ HC) as [v1' [-> HV]].
    destruct (Erase.R_res_inv_l _ _ HA) as [v2' [-> HVE]].
    exists v2'; split; [exists v1'; split; assumption |].
    eapply C0.R_n_V_n; eauto.
  Qed.

  Lemma R_n_Res_inv θ ω n m p v1 r2 :
    R_n θ ω n m p (A0.Res v1) r2 ->
    exists v2, r2 = A0.Res v2 /\ V_n θ ω n m p v1 v2.
  Proof.
    intros H.
    pose proof H as Hc.
    unfold R_n, Cross in Hc.
    destruct Hc as [r2' [[r1' [HC HA]] HC1]].
    destruct (C.R_n_Res_inv _ _ _ _ _ _ HC) as [v1' [-> HV]].
    destruct (Erase.R_res_inv_l _ _ HA) as [v2' [-> HVE]].
    destruct (C0.R_n_Res_inv _ _ _ HC1) as [v2 [-> HV1]].
    exists v2; split; [reflexivity |].
    eapply R_n_V_n; exact H.
  Qed.

  Lemma Top_n_subset n m p e1 e2 :
    Top_n n m p e1 e2 ->
    A0.occurs_free e2 \subset A0.occurs_free e1.
  Proof.
    unfold Top_n, Cross.
    intros H.
    destruct H as [e2' [[e1' [HC0 HA]] HC1]].
    apply C.Top_n_subset in HC0.
    apply C0.Top_n_subset in HC1.
    apply Erase.trans_correct_top_subset in HA.
    eapply Included_trans; eauto.
    eapply Included_trans; eauto.
  Qed.

  (* The empty environments are related when there are no free variables. *)
  Lemma G_n_empty θ ω n m p Γ :
    Γ \subset (Empty_set _) ->
    G_n θ ω n m p Γ (M.empty _) (M.empty _).
  Proof.
    intros Hclosed.
    unfold G_n, Cross.
    exists (M.empty _); split; [exists (M.empty _); split |].
    - (* the semantic pipeline *)
      apply C.G_n_empty; exact Hclosed.
    - (* Erase *)
      intros k; split.
      + constructor; intros x v Hget; rewrite M.gempty in Hget; discriminate.
      + intros x Hx; apply Hclosed in Hx; inv Hx.
    - (* LambdaANF *)
      unfold C0.G_n.
      induction p as [| p IHp]; [constructor |].
      econstructor; [| exact IHp].
      intros k x Hx; apply Hclosed in Hx; inv Hx.
  Qed.

End Comp_n.

Section Adequacy.

  Lemma Top_n_adequacy n m p e1 e2:
    Top_n n m p e1 e2 ->
    exists θ ω,
      An.analysis_context_escape_ok θ /\
      Aw.valid_web_map_context ω θ /\
        forall ρ1 ρ2,
          G_n θ ω n m p (A0.occurs_free e1) ρ1 ρ2 ->
          forall j1 r1,
            A0.bstep_fuel ρ1 e1 j1 r1 ->
            exists j2 r2,
              A0.bstep_fuel ρ2 e2 j2 r2 /\
                R_n θ ω n m p r1 r2.
  Proof.
    unfold Top_n, Cross.
    intros [e2' [[e1' [HC0 HA]] HC1]].

    (* the contexts come from the semantic pipeline *)
    destruct (C.Top_n_adequacy _ _ _ _ HC0) as [θ [ω [Hesc [Hω Hrun]]]].
    exists θ, ω.
    split; [exact Hesc |].
    split; [exact Hω |].

    intros ρ1 ρ2 HG j1 r1 Hstep.
    unfold G_n, Cross in HG.
    destruct HG as [ρ2' [[ρ1' [HG0 HGE]] HG1]].

    (* the semantic pipeline *)
    destruct (Hrun ρ1 ρ1' HG0 j1 r1 Hstep) as [j1' [r1' [Hstep1' HR0]]].

    (* Erase *)
    assert (Hwf1' : A1.wf_env ρ1') by exact (C.G_n_wf_env HG0).
    assert (HGE' : forall k, Erase.G_top k (A1.occurs_free e1') ρ1' ρ2').
    { intros k; eapply Erase.G_top_subset; [exact (HGE k) |].
      eapply C.Top_n_subset; eauto. }
    destruct (EC.adequacy _ _ HA ρ1' ρ2' Hwf1' HGE' j1' r1' Hstep1')
      as [j2' [r2' [Hstep2' HRE]]].

    (* LambdaANF *)
    assert (HG1' : C0.G_n p (A0.occurs_free e2') ρ2' ρ2).
    { eapply C0.G_n_subset; [exact HG1 |].
      eapply Included_trans; [eapply Erase.trans_correct_top_subset; eauto |].
      eapply C.Top_n_subset; eauto. }
    destruct (C0.Top_n_adequacy _ _ _ HC1 ρ2' ρ2 HG1' j2' r2' Hstep2')
      as [j2 [r2 [Hstep2 HR1]]].

    exists j2, r2; split; [exact Hstep2 |].
    unfold R_n, Cross.
    exists r2'; split; [exists r1'; split; assumption | exact HR1].
  Qed.

  Lemma Top_n_adequacy_closed n m p e1 e2:
    Top_n n m p e1 e2 ->
    A0.occurs_free e1 \subset (Empty_set _) ->
    exists θ ω,
      An.analysis_context_escape_ok θ /\
      Aw.valid_web_map_context ω θ /\
        forall j1 r1,
          A0.bstep_fuel (M.empty _) e1 j1 r1 ->
          exists j2 r2,
            A0.bstep_fuel (M.empty _) e2 j2 r2 /\
              R_n θ ω n m p r1 r2.
  Proof.
    intros Hrel Hclosed.
    destruct (Top_n_adequacy n m p e1 e2 Hrel) as [θ [ω [Hesc [Hω Hrun]]]].
    exists θ, ω.
    split; [exact Hesc |].
    split; [exact Hω |].
    intros j1 r1 Hstep.
    eapply Hrun; [| exact Hstep].
    apply G_n_empty; exact Hclosed.
  Qed.

  (* Termination Preservation *)
  Theorem Top_n_preserves_termination n m p e1 e2 :
    Top_n n m p e1 e2 ->
    exists θ ω,
      An.analysis_context_escape_ok θ /\
      Aw.valid_web_map_context ω θ /\
        forall ρ1 ρ2,
          G_n θ ω n m p (A0.occurs_free e1) ρ1 ρ2 ->
          forall j1 v1,
            A0.bstep_fuel ρ1 e1 j1 (A0.Res v1) ->
            exists j2 v2,
              A0.bstep_fuel ρ2 e2 j2 (A0.Res v2) /\
                V_n θ ω n m p v1 v2.
  Proof.
    intros Hrel.
    destruct (Top_n_adequacy n m p e1 e2 Hrel) as [θ [ω [Hesc [Hω Hrun]]]].
    exists θ, ω.
    split; [exact Hesc |].
    split; [exact Hω |].
    intros ρ1 ρ2 HG j1 v1 Hstep.
    destruct (Hrun ρ1 ρ2 HG j1 _ Hstep) as [j2 [r2 [Hstep2 HR]]].
    destruct (R_n_Res_inv _ _ _ _ _ _ _ HR) as [v2 [-> HV]].
    exists j2, v2; split; assumption.
  Qed.

  Theorem Top_n_preserves_termination_closed n m p e1 e2 :
    Top_n n m p e1 e2 ->
    A0.occurs_free e1 \subset (Empty_set _) ->
    exists θ ω,
      An.analysis_context_escape_ok θ /\
      Aw.valid_web_map_context ω θ /\
        forall j1 v1,
          A0.bstep_fuel (M.empty _) e1 j1 (A0.Res v1) ->
          exists j2 v2,
            A0.bstep_fuel (M.empty _) e2 j2 (A0.Res v2) /\
              V_n θ ω n m p v1 v2.
  Proof.
    intros Hrel Hclosed.
    destruct (Top_n_adequacy_closed n m p e1 e2 Hrel Hclosed) as [θ [ω [Hesc [Hω Hrun]]]].
    exists θ, ω.
    split; [exact Hesc |].
    split; [exact Hω |].
    intros j1 v1 Hstep.
    destruct (Hrun j1 _ Hstep) as [j2 [r2 [Hstep2 HR]]].
    destruct (R_n_Res_inv _ _ _ _ _ _ _ HR) as [v2 [-> HV]].
    exists j2, v2; split; assumption.
  Qed.

End Adequacy.

(*
Section Refinement.

  Definition val_ref := Cross (Cross C.val_ref Erase.val_ref) C0.val_ref.

  Lemma R_n_res_val_ref {n m p v1 v2} :
    R_n n m p (A0.Res v1) (A0.Res v2) ->
    val_ref v1 v2.
  Proof.
    unfold R_n, val_ref, Cross.
    intros.
    destruct H as [r2' [[r1' [HC0 HR]] HC1]].
    edestruct C.R_n_Res_inv as [v1' [Heqv1' HV1]]; eauto; subst.
    eapply C.R_n_res_val_ref in HC0; eauto.
    edestruct Erase.R_res_inv_l as [v2' [Heqv2' HV2]]; eauto; subst.
    eapply C0.R_n_res_val_ref in HC1; eauto.
    eexists; split; eauto.
    - eexists; split; eauto.
      eapply Erase.V_val_ref; eauto.
      eapply C.V_n_wf_val_r; eauto.
  Qed.

  (* Behavioral Refinement *)
  Theorem Top_n_val_ref n m p e1 e2 :
    Top_n n m p e1 e2 ->
    forall ρ1 ρ2,
      G_n n m p (A0.occurs_free e1) (A0.occurs_free e2) ρ1 ρ2 ->
      forall j1 v1,
        A0.bstep_fuel ρ1 e1 j1 (A0.Res v1) ->
        exists j2 v2,
          A0.bstep_fuel ρ2 e2 j2 (A0.Res v2) /\
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
  Theorem Top_n_preserves_linking f x n n' m m' p p' e1 e2 e1' e2' :
    f <> x ->
    ~ (f \in A0.occurs_free e1) ->
    ~ (f \in A0.occurs_free e1') ->
    Top_n n m p e1 e2 ->
    Top_n n' m' p' e1' e2' ->
    Top_n (n + n') (m + m') (p + p') (A0.link f x e1 e1') (A0.link f x e2 e2').
  Proof.
    unfold Top_n, Cross.
    intros Hfx Hf1 Hf1'; intros.
    destruct H as [e3 [[e4 [HC0 HA1]] HC1]].
    destruct H0 as [e3' [[e4' [HC0' HA1']] HC1']].
    destruct Exposed_nonempty as [w0 Hw].

    eapply (C.Top_n_preserves_linking f w0 x n n') in HC0; eauto.
    eapply (EC.preserves_linking f w0 x e4 e3 e4' e3') in HA1; eauto.
    eapply (C0.Top_n_preserves_linking f x p p') in HC1; eauto.
  Qed.

  Corollary Top_n_preserves_linking_l f x n n' m p e1 e2 e1' e2' :
    f <> x ->
    ~ (f \in A0.occurs_free e1) ->
    ~ (f \in A0.occurs_free e1') ->
    Top_n n 0 0 e1 e2 ->
    Top_n n' m p e1' e2' ->
    Top_n (n + n') m p (A0.link f x e1 e1') (A0.link f x e2 e2').
  Proof. eapply Top_n_preserves_linking; eauto. Qed.

  Corollary Top_n_preserves_linking_r f x n n' m p e1 e2 e1' e2' :
    f <> x ->
    ~ (f \in A0.occurs_free e1) ->
    ~ (f \in A0.occurs_free e1') ->
    Top_n n m p e1 e2 ->
    Top_n n' 0 0 e1' e2' ->
    Top_n (n + n') m p (A0.link f x e1 e1') (A0.link f x e2 e2').
  Proof.
    intros.
    assert (Top_n (n + n') (m + 0) (p + 0) (A0.link f x e1 e1') (A0.link f x e2 e2')).
    eapply Top_n_preserves_linking; eauto.
    rewrite_math (m + 0 = m).
    rewrite_math (p + 0 = p); auto.
  Qed.

End Linking.

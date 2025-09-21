From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util RelComp ANF0 Refl0 Refl0Comp Annotate ANF Refl ReflComp Erase Comp.

Module A0 := ANF0.
Module A1 := ANF.

Module R0 := Refl0.
Module R1 := Refl.

Module C := Comp.
Module C0 := Refl0Comp.
Module C1 := ReflComp.

(* Compositionality of the cross-language pipeline

   Unannotated ANF -> Annotate ANF -> Unannotated ANF
 *)

(* Adequacy / Preservation of Termination *)
(* Behavioral Refinement *)
(* Linking Preservation *)

Section Comp.

  Definition Top_n n m p := Cross (Cross (C.Top_n n m) Erase.trans_correct_top) (C0.Top_n p).

  Definition V_n n m p := Cross (Cross (C.V_n n m) (fun v1 v2 => forall k, Erase.V k v1 v2)) (C0.V_n p).

  Definition R_n n m p := Cross (Cross (C.R_n n m) (fun v1 v2 => forall k, Erase.R k v1 v2)) (C0.R_n p).

  Definition G_n n m p Γ1 Γ2 := Cross (Cross (C.G_n n m Γ1 Γ2) (fun ρ1 ρ2 => forall k, Erase.G_top k Γ1 ρ1 Γ2 ρ2)) (C0.G_n p Γ1 Γ2).

  Lemma R_n_V_n n m p v1 v2:
    R_n n m p (A0.Res v1) (A0.Res v2) ->
    V_n n m p v1 v2.
  Proof.
    unfold R_n, V_n, Cross.
    intros H.
    destruct H as [r2' [[r1' [HC HA]] HC1]].
    apply C.R_n_Res_inv in HC.
    destruct HC as [v1' [Heqv1' HC]]; subst.
    edestruct Erase.R_res_inv_l as [v2' [Heqv2' _]]; eauto; subst.
    eexists; split; eauto.
    eapply C0.R_n_V_n; eauto.
  Qed.

  Lemma R_n_Res_inv n m p v1 r2 :
    R_n n m p (A0.Res v1) r2 ->
    exists v2, r2 = A0.Res v2 /\ V_n n m p v1 v2.
  Proof.
    unfold R_n, V_n, Cross.
    intros.
    destruct H as [r2' [[r1' [HC HA]] HC0]].
    apply C.R_n_Res_inv in HC.
    destruct HC as [v1' [Heqv1' HC]]; subst.
    edestruct Erase.R_res_inv_l as [v2' [Heqv2' HV]]; eauto; subst.

    apply C0.R_n_Res_inv in HC0.
    destruct HC0 as [v2'' [Heqv2'' HC1]]; subst.
    eexists; split; eauto.
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

End Comp.

Section Adequacy.

  Lemma Top_n_R_n n m p e1 e2:
    Top_n n m p e1 e2 ->
    forall ρ1 ρ2,
      G_n n m p (A0.occurs_free e1) (A0.occurs_free e2) ρ1 ρ2 ->
      forall j1 r1,
        A0.bstep_fuel ρ1 e1 j1 r1 ->
        exists j2 r2,
          A0.bstep_fuel ρ2 e2 j2 r2 /\
          R_n n m p r1 r2.
  Proof.
    intros Hrel.
    unfold Top_n, G_n, R_n, Cross in *.
    destruct Hrel as [e2' [[e1' [HC0 HA]] HC1]].
    intros.

    destruct H as [ρ2' [[ρ1' [HG0 HAG]] HG1]].
    edestruct (C.Top_n_R_n _ _ _ _ HC0) with (ρ2 := ρ1') as [j1' [r1' [Hstep1' HRn0]]]; eauto.
    eapply C.G_n_wf_env; eauto.
    eapply C.G_n_subset; eauto.
    apply Included_refl.
    eapply C.Top_n_subset; eauto.

    edestruct (Erase.adequacy _ _ HA) with (ρ2 := ρ2') as [j2' [r2' [Hstep2' HAR]]]; eauto.
    - eapply C.G_n_wf_env; eauto.
    - intros.
      specialize (HAG k).
      eapply Erase.G_top_subset; eauto.
      eapply C.Top_n_subset; eauto.
      eapply Erase.trans_correct_top_subset; eauto.
    - edestruct (C0.Top_n_R_n _ _ _ HC1) with (ρ2 := ρ2) as [j2 [r2 [Hstep2 HRn1]]]; eauto.
      eapply C0.G_n_subset; eauto.
      + eapply Erase.trans_correct_top_subset in HA; eauto.
        eapply Included_trans; eauto.
        eapply C.Top_n_subset; eauto.
      + eapply C0.Top_n_subset; eauto.
      + eexists; eexists; split; eauto.
  Qed.

  (* Termination Perservation *)
  Theorem Top_n_preserves_termination n m p e1 e2 :
    Top_n n m p e1 e2 ->
    forall ρ1 ρ2,
      G_n n m p (A0.occurs_free e1) (A0.occurs_free e2) ρ1 ρ2 ->
      forall j1 v1,
        A0.bstep_fuel ρ1 e1 j1 (A0.Res v1) ->
        exists j2 v2,
          A0.bstep_fuel ρ2 e2 j2 (A0.Res v2) /\
          V_n n m p v1 v2.
  Proof.
    intros.
    edestruct Top_n_R_n with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
    edestruct R_n_Res_inv as [v2 [Heq HVn]]; eauto; subst.
    eexists; eexists; split; eauto.
  Qed.

End Adequacy.

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
    edestruct Top_n_R_n with (ρ1 := ρ1) as [j2 [r2 [Hr2 HR]]]; eauto.
    edestruct R_n_Res_inv as [v2 [Heq HVn]]; eauto; subst.
    eexists; eexists; split; eauto.
    eapply R_n_res_val_ref; eauto.
  Qed.

End Refinement.

Section Linking.

  (* Linking Preservation *)
  Theorem Top_n_preserves_linking f x n n' m m' p p' e1 e2 e1' e2' :
    Top_n n m p e1 e2 ->
    Top_n n' m' p' e1' e2' ->
    Top_n (n + n') (m + m') (p + p') (A0.link f x e1 e1') (A0.link f x e2 e2').
  Proof.
    unfold Top_n, Cross.
    intros.
    destruct H as [e3 [[e4 [HC0 HA1]] HC1]].
    destruct H0 as [e3' [[e4' [HC0' HA1']] HC1']].

    eapply (C.Top_n_preserves_linking f x n n') in HC0; eauto.
    eapply (Erase.preserves_linking f Annotate.w0 x e4 e3 e4' e3') in HA1; eauto.
    eapply (C0.Top_n_preserves_linking f x p p') in HC1; eauto.
    apply Annotate.w0_exposed.
  Qed.

  Corollary Top_n_preserves_linking_l f x n n' m p e1 e2 e1' e2' :
    Top_n n 0 0 e1 e2 ->
    Top_n n' m p e1' e2' ->
    Top_n (n + n') m p (A0.link f x e1 e1') (A0.link f x e2 e2').
  Proof.
    eapply Top_n_preserves_linking; eauto.
  Qed.

  Corollary Top_n_preserves_linking_r f x n n' m p e1 e2 e1' e2' :
    Top_n n m p e1 e2 ->
    Top_n n' 0 0 e1' e2' ->
    Top_n (n + n') m p (A0.link f x e1 e1') (A0.link f x e2 e2').
  Proof.
    intros.
    assert (Top_n (n + n') (m + 0) (p + 0) (A0.link f x e1 e1') (A0.link f x e2 e2')).
    eapply Top_n_preserves_linking; eauto.
    assert (Hm : m + 0 = m) by lia; rewrite Hm in *.
    assert (Hp : p + 0 = p) by lia; rewrite Hp in *.
    auto.
  Qed.

  (* TODO: Try Unary *)
  (* Below definition is currently unused *)
  Definition not_stuck (e : A0.exp) :=
    (forall ρ,
        (forall x,
            (x \in (A0.occurs_free e)) ->
            exists v,
              ρ ! x = v) ->
        forall i, exists r, A0.bstep_fuel ρ e i r).

  Lemma Refl0_Top_n_perserves_not_stuck e1 n e2 :
    not_stuck e1 ->
    C0.Top_n n e1 e2 ->
    not_stuck e2.
  Proof.
    intros.
    induction H0; auto.
    apply IHComp.
    clear H1 IHComp.
    unfold not_stuck, Refl0.related_top in *.
    inv H0.
    intros.
    rename c1 into e1.
    rename c2 into e2.
  Abort.

  (* This should hold regardless of the actual Annotate pass *)
  Lemma Annotate_Erase_id e1 e2 e1' :
    Annotate.trans (A0.occurs_free e1) e1 e1' ->
    Erase.trans (A1.occurs_free e1') e1' e2 ->
    e1 = e2.
  Proof.
    intro H.
    revert e2.
    induction H; simpl; intros.
    - inv H0; auto.
    - inv H1; auto.
      erewrite IHtrans1 with (e2 := e'0); eauto.
      + erewrite IHtrans2 with (e2 := k'0); eauto.
        eapply Erase.trans_exp_strengthen; eauto.
        eapply A1.free_fun_k_subset; eauto.
      + eapply Erase.trans_exp_strengthen; eauto.
        eapply A1.free_fun_e_subset; eauto.
    - inv H1; auto.
    - inv H2; auto.
      erewrite IHtrans with (e2 := k'0); eauto.
      eapply Erase.trans_exp_strengthen; eauto.
      eapply A1.free_letapp_k_subset; eauto.
    - inv H1; auto.
      erewrite IHtrans with (e2 := k'0); eauto.
      eapply Erase.trans_exp_strengthen; eauto.
      eapply A1.free_constr_k_subset; eauto.
    - inv H1; auto.
      erewrite IHtrans with (e2 := k'0); eauto.
      eapply Erase.trans_exp_strengthen; eauto.
      eapply A1.free_proj_k_subset; eauto.
    - inv H0; auto.
    - inv H2; auto.
      erewrite IHtrans1 with (e2 := e'0); eauto.
      + assert (A0.Ecase x cl = A0.Ecase x cl'0).
        {
          erewrite IHtrans2 with (e2 := (A0.Ecase x cl'0)); eauto.
          eapply Erase.trans_exp_strengthen; eauto.
          eapply A1.free_case_tl_subset; eauto.
        }
        inv H2; auto.
      + eapply Erase.trans_exp_strengthen; eauto.
        eapply A1.free_case_hd_subset; eauto.
  Qed.

  Theorem Top_n_correlate n e1 e2 :
    (* not_stuck e1 -> *)
    C0.Top_n n e1 e2 ->
    Top_n n 0 0 e1 e2.
  Proof.
    unfold Top_n, Cross.
    intros.
    exists e2; split.
    - destruct (Annotate.trans_complete e2) as [e2' HA].
      (* + eapply Refl0_Top_n_perserves_not_stuck; eauto. *)
      + exists e2'; split.
        * unfold C.Top_n, Cross.
          exists e2'; split.
          -- exists e2; split; auto.
             eapply Annotate.top; eauto.
          -- eapply C1.Top_n_refl; eauto.
        * destruct (Erase.trans_complete e2') as [e2'' HE].
          erewrite Annotate_Erase_id; eauto.
          eapply Erase.top; eauto.
    - eapply C0.Top_n_refl; eauto.
  Qed.

  (* Cross Pipeline Linking Preservation *)
  Theorem Top_n_preserves_linking_cross_l f x n n' m p e1 e2 e1' e2' :
    C0.Top_n n e1 e2 ->
    Top_n n' m p e1' e2' ->
    Top_n (n + n') m p (A0.link f x e1 e1') (A0.link f x e2 e2').
  Proof.
    intros.
    eapply Top_n_preserves_linking_l; eauto.
    eapply Top_n_correlate; eauto.
  Qed.

  Theorem Top_n_preserves_linking_cross_r f x n n' m p e1 e2 e1' e2' :
    Top_n n m p e1 e2 ->
    C0.Top_n n' e1' e2' ->
    Top_n (n + n') m p (A0.link f x e1 e1') (A0.link f x e2 e2').
  Proof.
    intros.
    eapply Top_n_preserves_linking_r; eauto.
    eapply Top_n_correlate; eauto.
  Qed.

End Linking.

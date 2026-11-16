From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util RelComp.
From LambdaANF Require Import ANF.
From SemAnnotate Require Import LabeledANF Label SimpleCFA SimpleWebAssign Rewrite.
From LambdaWeb Require Import ANF.

(* Compositionality of The Analysis Pipeline *)

Module AS := LambdaANF.ANF.
Module L := Label.
Module AL := LabeledANF.
Module An := SimpleCFA.
Module Aw := SimpleWebAssign.
Module R := Rewrite.
Module AT := LambdaWeb.ANF.

Section Comp.

  Definition trans_correct_top := Cross L.trans_correct_top
                                    (Cross An.trans_correct_top
                                       (Cross Aw.trans_correct_top
                                          R.trans_correct_top)).

  (* The relations are parameterized by the analysis context `θ` and the web map
   c    ontext `ω`, as the middle of the pipeline works on colored objects. *)
  Definition V θ ω :=
    Cross (fun v1 v2 => forall k, L.V k v1 v2)
      (Cross (fun v1 v2 => forall k, An.V_top θ k v1 v2)
         (Cross (fun v1 v2 => forall k, Aw.V_top θ ω k v1 v2)
            (fun v1 v2 => forall k, R.V_top k v1 v2))).

  Definition R θ ω :=
    Cross (fun r1 r2 => forall k, L.R k r1 r2)
      (Cross (fun r1 r2 => forall k, An.R_top θ k r1 r2)
         (Cross (fun r1 r2 => forall k, Aw.R_top θ ω k r1 r2)
            (fun r1 r2 => forall k, R.R_top k r1 r2))).

  Definition G θ ω Γ1 :=
    Cross (fun ρ1 ρ2 => forall k, L.G k Γ1 ρ1 ρ2)
      (Cross (fun ρ1 ρ2 => forall k, An.G_top θ k Γ1 ρ1 ρ2)
         (Cross (fun ρ1 ρ2 => forall k, Aw.G_top θ ω k Γ1 ρ1 ρ2)
            (fun ρ1 ρ2 => forall k, R.G_top k Γ1 ρ1 ρ2))).

  Lemma V_wf_val_r θ ω v1 v2:
    V θ ω v1 v2 ->
    AT.wf_val v2.
  Proof.
    unfold V, Cross.
    intros [v3 [_ [v4 [_ [v5 [_ HR]]]]]].
    exact (R.V_top_wf_val_r (HR 0)).
  Qed.

  Lemma V_exposed_r θ ω v1 v2:
    V θ ω v1 v2 ->
    exposed v2.
  Proof.
    unfold V, Cross.
    intros [v3 [_ [v4 [_ [v5 [_ HR]]]]]].
    exact (R.V_top_exposed_r (HR 0)).
  Qed.

  Lemma R_V θ ω v1 v2:
    R θ ω (AS.Res v1) (AT.Res v2) ->
    V θ ω v1 v2.
  Proof.
    unfold R, V, Cross.
    intros [r3 [HL [r4 [HA [r5 [HW HR]]]]]].
    destruct r3 as [| v3]; [destruct (HL 0) |].
    destruct r4 as [| v4]; [destruct (HA 0) |].
    destruct r5 as [| v5]; [destruct (HW 0) |].
    exists v3; split; [exact HL |].
    exists v4; split; [exact HA |].
    exists v5; split; [exact HW | exact HR].
  Qed.

  Lemma R_res_inv_l θ ω v1 r2 :
    R θ ω (AS.Res v1) r2 ->
    exists v2, r2 = AT.Res v2 /\ V θ ω v1 v2.
  Proof.
    intros H.
    pose proof H as [r3 [HL [r4 [HA [r5 [HW HR]]]]]].
    destruct r3 as [| v3]; [destruct (HL 0) |].
    destruct r4 as [| v4]; [destruct (HA 0) |].
    destruct r5 as [| v5]; [destruct (HW 0) |].
    destruct r2 as [| v2]; [destruct (HR 0) |].
    exists v2; split; [reflexivity | apply R_V; exact H].
  Qed.

  Lemma G_wf_env_r {θ ω Γ1 ρ1 ρ2} :
    G θ ω Γ1 ρ1 ρ2 ->
    AT.wf_env ρ2.
  Proof.
    unfold G, Cross.
    intros [ρ3 [_ [ρ4 [_ [ρ5 [_ HR]]]]]].
    exact (R.G_top_wf_env_r _ _ _ _ (HR 0)).
  Qed.

  Lemma G_subset θ ω Γ1 Γ2 ρ1 ρ2 :
    G θ ω Γ1 ρ1 ρ2 ->
    Γ2 \subset Γ1 ->
    G θ ω Γ2 ρ1 ρ2.
  Proof.
    unfold G, Cross.
    intros [ρ3 [HL [ρ4 [HA [ρ5 [HW HR]]]]]] Hsub.
    exists ρ3; split; [intros k; eapply L.G_subset; eauto |].
    exists ρ4; split; [intros k; eapply An.G_top_subset; eauto |].
    exists ρ5; split; [intros k; eapply Aw.G_top_subset; eauto |].
    intros k; eapply R.G_top_subset; eauto.
  Qed.

  (* The empty environments are related along the pipeline when there are no
   free variables. *)
  Lemma G_empty θ ω Γ :
    Γ \subset (Empty_set _) ->
    G θ ω Γ (M.empty _) (M.empty _).
  Proof.
    intros Hclosed.
    unfold G, Cross.
    exists (M.empty _); split.
    { intros k x Hx; apply Hclosed in Hx; inv Hx. }
    exists (M.empty _); split.
    { intros k; split; [| split].
      - constructor.
        + intros x v Hget; rewrite M.gempty in Hget; discriminate.
        + intros x Hx; apply Hclosed in Hx; inv Hx.
      - constructor; intros x v Hget; rewrite M.gempty in Hget; discriminate.
      - intros x Hx; apply Hclosed in Hx; inv Hx. }
    exists (M.empty _); split.
    { intros k; split; [| split].
      - constructor; intros x v Hget; rewrite M.gempty in Hget; discriminate.
      - constructor; intros x v Hget; rewrite M.gempty in Hget; discriminate.
      - intros x Hx; apply Hclosed in Hx; inv Hx. }
    intros k; split; [| split].
    - constructor; intros x v Hget; rewrite M.gempty in Hget; discriminate.
    - constructor; intros x v Hget; rewrite M.gempty in Hget; discriminate.
    - intros x Hx; apply Hclosed in Hx; inv Hx.
  Qed.

  Lemma trans_correct_top_subset e1 e2 :
    trans_correct_top e1 e2 ->
    AT.occurs_free e2 \subset AS.occurs_free e1.
  Proof.
    unfold trans_correct_top, Cross.
    intros [e3 [HL [ce [HA [we [HW HR]]]]]].
    eapply Included_trans; [apply (proj1 HR) |].
    eapply Included_trans; [apply (proj1 HW) |].
    eapply Included_trans; [apply (proj1 HA) | apply (proj1 HL)].
  Qed.

End Comp.

Section Adequacy.

  (* Adequacy *)
  Theorem adequacy e we :
    trans_correct_top e we ->
    exists θ ω,
        forall ρ1 ρ2,
          G θ ω (AS.occurs_free e) ρ1 ρ2 ->
          forall j1 r1,
            AS.bstep_fuel ρ1 e j1 r1 ->
            exists j2 r2,
              AT.bstep_fuel true ρ2 we j2 r2 /\
                R θ ω r1 r2.
  Proof.
    unfold trans_correct_top, G, R, Cross.
    intros [e3 [HL1 [e4 [Ha1 [e5 [Hw1 HR1]]]]]].
    edestruct (Aw.adequacy2 e4 e5) as [θ [ω [cce [c1 [c2 [Hcolor [Hactx [Haesc [Hwctx [Hweb HAn]]]]]]]]]]; eauto.

    exists θ, ω.

    intros.
    edestruct H as [ρ1' [HGL [ρ2' [HGAn [ρ3 [HGAw HGR]]]]]]; eauto.
    edestruct (L.adequacy e e3) as [j1' [r1' [HLstep HRL]]]; eauto.

    edestruct (An.adequacy e3 e4) with (ρ2 := ρ2') as [j2' [r2' [I2' [HAnstep HRAn]]]]; eauto.
    intros.
    eapply An.G_top_subset; eauto.
    eapply L.trans_correct_top_subset; eauto.

    edestruct HAn with (ρ2 := ρ3) as [j3' [r3' [HAwstep HRAw]]]; eauto.
    intros.
    eapply Aw.G_top_subset; eauto.
    eapply Included_trans.
    eapply An.trans_correct_top_subset; eauto.
    eapply L.trans_correct_top_subset; eauto.

    edestruct (R.adequacy e5 we) with (ρ2 := ρ2) as [j4' [r4' [HRstep HRR]]]; eauto.
    intros.
    eapply R.G_top_subset; eauto.
    eapply Included_trans.
    eapply Aw.trans_correct_top_subset; eauto.
    eapply Included_trans.
    eapply An.trans_correct_top_subset; eauto.
    eapply L.trans_correct_top_subset; eauto.

    exists j4', r4'; split; eauto.
    exists r1'; split; eauto.
  Qed.

  Theorem adequacy_closed e we :
    trans_correct_top e we ->
    AS.occurs_free e \subset (Empty_set _) ->
    exists θ ω,
        forall j1 r1,
          AS.bstep_fuel (M.empty _) e j1 r1 ->
          exists j2 r2,
            AT.bstep_fuel true (M.empty _) we j2 r2 /\
              R θ ω r1 r2.
  Proof.
    intros Htc Hclosed.
    destruct (adequacy e we Htc) as [θ [ω Hrun]].
    exists θ, ω.

    intros j1 r1 Hstep.
    eapply Hrun; [| exact Hstep].
    apply G_empty; exact Hclosed.
  Qed.

End Adequacy.

Section BehaviorRefinement.

  (* Behavioral Refinement *)
  Definition val_ref := Cross L.val_ref
                          (Cross An.val_ref
                             (Cross Aw.val_ref
                                R.val_ref)).

  (* A list related by a composed relation is related through an
     intermediate list. *)
  Lemma Forall2_Cross {T1 T2 T3} {R1 : T1 -> T2 -> Prop} {R2 : T2 -> T3 -> Prop} {xs zs} :
    Forall2 (Cross R1 R2) xs zs ->
    exists ys, Forall2 R1 xs ys /\ Forall2 R2 ys zs.
  Proof.
    intros H.
    induction H as [| x z xs zs [y [Hxy Hyz]] _ [ys [Hxys Hyzs]]].
    - exists []; split; constructor.
    - exists (y :: ys); split; constructor; assumption.
  Qed.

  (* An analysis result for the intermediate constructors, which carry no
     information that the refinement looks at. *)
  Definition empty_analysis_result : An.analysis_result :=
    An.mk_analysis_result
      (fun _ => Empty_set _) (fun _ => Empty_set _) (fun _ => Empty_set _)
      (Empty_set _) (Empty_set _).

  Lemma V_val_ref {θ ω v1 v2} :
    V θ ω v1 v2 ->
    val_ref v1 v2.
  Proof.
    unfold V, val_ref, Cross.
    intros [v3 [HL [v4 [HA [v5 [HW HR]]]]]].
    exists v3; split; [exact (L.V_val_ref HL) |].
    exists v4; split; [exact (An.V_top_val_ref HA) |].
    exists v5; split; [exact (Aw.V_top_val_ref HW) | exact (R.V_top_val_ref HR)].
  Qed.

End BehaviorRefinement.

Section Linking.

  (* Linking Preservation *)
  Lemma preserves_linking f w x e1 e2 e1' e2' :
    (w \in Exposed) ->
    f <> x ->
    ~ (f \in AS.occurs_free e1) ->
    ~ (f \in AS.occurs_free e2) ->
    trans_correct_top e1 e1' ->
    trans_correct_top e2 e2' ->
    trans_correct_top (AS.link f x e1 e2) (AT.link f w x e1' e2').
  Proof.
    unfold trans_correct_top, Cross.
    intros Hw Hfx Hf1 Hf2.
    intros HT1 HT2.
    destruct HT1 as [e3 [HL1 [e4 [Ha1 [e5 [Hw1 HR1]]]]]].
    destruct HT2 as [e3' [HL2 [e4' [Ha2 [e5' [Hw2 HR2]]]]]].

    pose proof (L.preserves_linking_top f x _ _ _ _ HL1 HL2) as HL.
    eexists; split; eauto.

    assert (Hf3 : ~ Ensembles.In var (AL.occurs_free e3) f) by (inv HL1; fcrush).
    assert (Hf3' : ~ Ensembles.In var (AL.occurs_free e3') f) by (inv HL2; fcrush).
    pose proof Ha1 as Ha1'.
    eapply (An.preserves_linking f x e3 e4 e3' e4') in Ha1'; eauto.
    eexists; split; eauto.

    pose proof Hw1 as Hw1'.
    eapply (Aw.preserves_linking x e4 e5 e4' e5') in Hw1'; eauto.
    eexists; split; eauto.

    assert (Hf4 : ~ Ensembles.In var (R.Aw.occurs_free_top e5) f) by (inv Ha1; fcrush).
    assert (Hf4' : ~ Ensembles.In var (R.Aw.occurs_free_top e5') f) by (inv Ha2; fcrush).
    eapply R.preserves_linking; eauto.
  Qed.

End Linking.

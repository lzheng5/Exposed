From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From LambdaWeb Require Import ANF Id Exposed.

(* Reflexive Logical Relations for λWeb with Exposed Webs Only *)

(* Logical Relations *)

(* Set up the internal web selector so that every internal webs will be related to False. *)
Module LT <: Exposed.LTy. Definition t := unit. End LT.
Module LM := Exposed.DefaultL LT.
Import LM.

Module VTransM <: Exposed.VTrans LM.

  Definition V_trans
    (V' : nat -> wval -> wval -> Prop)
    (E' : nat -> env -> exp -> env -> exp -> Prop)
    (i0 : nat) (d : LM.elt)
    (w1 : web) (v1 : val) (w2 : web) (v2 : val) := False.

  Lemma V_trans_mono V E i j d w1 v1 w2 v2 :
    (forall k : nat,
        k < S i ->
        forall (j : nat) (v1 v2 : wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
    V_trans (fun i' => V (i - (i - i'))) (fun i' => E (i - (i - i'))) i d w1 v1 w2 v2 ->
    j <= i ->
    V_trans (fun j' => V (j - (j - j'))) (fun j' => E (j - (j - j'))) j d w1 v1 w2 v2.
  Proof.
    unfold V_trans.
    intros; contradiction.
  Qed.

End VTransM.

Module RM := Exposed.Exposed LM VTransM.
Import RM.

(* Correlations between Id and λWeb *)

Module IM := Id.EM.EG.EV.

Lemma V_V_Forall_aux :
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

Lemma V_V :
  forall i v1 v2,
    exposed v1 ->
    V i v1 v2 <-> IM.V i v1 v2.
Proof.
  intro i.
  induction i using lt_wf_rec; intros.
  destruct i.
  - destruct v1; destruct v2; split; simpl; intros; auto;
      assert (Hw : w \in Exposed) by (inv H0; auto);
      destruct H1 as [Hv1 [Hv2 HV]]; subst;
      destruct (L ! w) eqn:Heqw; try contradiction;
      repeat (split; auto);
      eapply L_inv_Some in Heqw; contradiction;
      simpl in *.
  - split; intro Hv;
      destruct Hv as [Hv1 [Hv2 HV]];
      repeat (split; auto);
      destruct v1; destruct v2; auto;
      destruct (L ! w) eqn:Heqw; try contradiction;
      simpl in *.
    + destruct HV as [Heqw0 HV]; split; auto.
      unfold V_refl in *.
      destruct v; destruct v0; try contradiction; simpl in *.
      * destruct HV as [Hlen HV].
        split; auto; intros.

        destruct (exposed_reflect w).
        2 : { fcrush. }

        assert (HE' : E' V true (i - (i - j)) ρ3 e ρ4 e0).
        {
          inv H0.
          eapply HV with (vs1 := vs1) (vs2 := vs2); try lia; eauto;
            intros; destruct H4; auto;
            eapply V_V_Forall_aux; eauto; try lia.
        }

        unfold E', R' in *.
        intros.
        edestruct HE' as [j2 [r2 [He0 HR']]]; eauto.
        exists j2; exists r2; split; auto.
        destruct r1; destruct r2; auto.
        eapply H; try lia; auto.
        inv H8; fcrush.
      * destruct HV as [Hc HV]; subst.
        repeat split; auto.
        rewrite normalize_step in *; try lia.
        eapply V_V_Forall_aux with (V1 := V); eauto.
        inv H0; auto.
    + destruct v; destruct v0; try contradiction; simpl in *;
        destruct HV as [Heqw0 _]; subst;
        eapply L_inv_Some in Heqw; fcrush.
    + destruct HV as [Heqw0 HV]; subst.
      split; auto.
      unfold V_refl in *.
      destruct v; destruct v0; try contradiction; simpl in *;
        destruct HV as [Hlen HV]; subst.
      split; auto; intros.

      destruct (exposed_reflect w0).
      2 : { fcrush. }

      assert (HE' : IM.E true (i - (i - j)) ρ3 e ρ4 e0).
      {
        inv H0.
        eapply HV with (vs1 := vs1) (vs2 := vs2); try lia; eauto;
          intros;
          eapply V_V_Forall_aux with (V1 := V); eauto; try lia.
      }

      unfold E', R' in *.
      intros.
      edestruct HE' as [j2 [r2 [He0 HR']]]; eauto.
      exists j2; exists r2; split; auto.
      destruct r1; destruct r2; auto.
      eapply H; try lia; auto.
      inv H8; fcrush.
      repeat split; auto.
      rewrite normalize_step in *; try lia.
      eapply V_V_Forall_aux with (V1 := V); eauto.
      inv H0; auto.
Qed.

Lemma R_R :
  forall i r1 r2,
    exposed_res r1 ->
    (R i r1 r2 <-> IM.R i r1 r2).
Proof.
  unfold R, R'.
  intros; split;
    destruct r1; destruct r2; try contradiction; auto;
    inv H;
    eapply V_V; eauto.
Qed.

Corollary E_E :
  forall i ρ1 e1 ρ2 e2,
    E true i ρ1 e1 ρ2 e2 <-> IM.E true i ρ1 e1 ρ2 e2.
Proof.
  unfold E, IM.E, E'.
  intros.
  split; intros;
    edestruct H as [j2 [r2 [Hbstep HR]]]; eauto;
    eexists; eexists; split; eauto;
    eapply R_R; eauto;
    eapply bstep_fuel_exposed_inv; eauto.
Qed.

Corollary refl_V :
  forall i v,
    wf_val v ->
    exposed v ->
    V i v v.
Proof.
  intros.
  eapply V_V; eauto.
  eauto using Id.refl_V.
Qed.

Corollary refl_R :
  forall i r,
    wf_res r ->
    exposed_res r ->
    R i r r.
Proof.
  intros.
  eapply R_R; eauto.
  eauto using Id.refl_R.
Qed.

Corollary refl_E :
  forall i ρ e,
    wf_env ρ ->
    E true i ρ e ρ e.
Proof.
  unfold E, E'.
  intros.
  eexists; eexists; split; eauto.
  inv H1; simpl; auto.
  apply refl_R; auto.
  eapply bstep_wf_res; eauto.
Qed.

Corollary trans_V :
  forall {i v1 v2 v3},
    exposed v1 ->
    V i v1 v2 ->
    (forall i, V i v2 v3) ->
    V i v1 v3.
Proof.
  intros.
  eapply V_V; eauto.
  eapply V_V in H0; eauto.
  assert (forall i, IM.V i v2 v3).
  {
    intros.
    eapply V_V; eauto.
    eapply IM.V_exposed; eauto.
  }
  eapply Id.trans_V; eauto.
Qed.

Corollary trans_R {i r1 r2 r3} :
  exposed_res r1 ->
  R i r1 r2 ->
  (forall k, R k r2 r3) ->
  R i r1 r3.
Proof.
  unfold R, R'.
  intros.
  destruct r1; destruct r2; destruct r3; try contradiction; auto.
  eapply trans_V; fcrush.
Qed.

Lemma trans_E_aux i :
  (forall m : nat,
      m <= i ->
      forall v1 v2 v3 : wval,
        exposed v1 ->
        V m v1 v2 ->
        (forall i : nat, V i v2 v3) ->
        V m v1 v3) ->
  forall {ρ1 e1 ρ2 e2 ρ3 e3},
    E true i ρ1 e1 ρ2 e2 ->
    (forall i, E true i ρ2 e2 ρ3 e3) ->
    E true i ρ1 e1 ρ3 e3.
Proof.
  unfold E, E'.
  intros IH; intros.
  edestruct H as [j2 [r2 [Hr2 HR]]]; eauto.
  edestruct (H0 j2) as [j3 [r3 [Hr3 HR']]]; eauto; try lia.
  eexists; eexists; split; eauto.
  unfold R' in *.
  destruct r1; destruct r2; destruct r3; try contradiction; auto.
  eapply IH; eauto; try lia.
  inv H2; fcrush.
  intros.
  edestruct (H0 (i0 + j2) j2) as [j3' [r3' [Hr3' HR'']]]; eauto; try lia.
  simpl in *.
  destruct r3'; try contradiction.
  edestruct (bstep_fuel_deterministic w1 w2 Hr3 Hr3'); eauto; subst.
  eapply V_mono; eauto; try lia.
Qed.

Corollary trans_E {i ρ1 e1 ρ2 e2 ρ3 e3}:
  E true i ρ1 e1 ρ2 e2 ->
  (forall i, E true i ρ2 e2 ρ3 e3) ->
  E true i ρ1 e1 ρ3 e3.
Proof.
  intros.
  eapply trans_E_aux; eauto.
  intros.
  eapply trans_V; eauto.
Qed.

(* Top level *)
Definition G_top i Γ1 ρ1 ρ2 :=
  wf_env ρ1 /\
  wf_env ρ2 /\
  (forall x,
    (x \in Γ1 ->
     exists v1 v2,
       M.get x ρ1 = Some v1 /\
       M.get x ρ2 = Some v2 /\
       exposed v1 /\
       V i v1 v2)).

Corollary G_top_G_top :
  forall i Γ1 ρ1 ρ2,
    G_top i Γ1 ρ1 ρ2 <-> Id.G_top i Γ1 ρ1 ρ2.
Proof.
  unfold G_top, Id.G_top.
  intros; split; intros;
    destruct H as [Hr1 [Hr2 HG]];
    repeat (split; auto); intros;
    edestruct HG as [v1 [v2 [Heqv1 [Heqv2 [Hexv1 HV]]]]]; eauto;
    eexists; eexists; repeat (split; eauto);
    eapply V_V; eauto.
Qed.

Definition related_top etop etop' :=
  (occurs_free etop') \subset (occurs_free etop) /\
  forall i ρ1 ρ2,
    G_top i (occurs_free etop) ρ1 ρ2 ->
    E true i ρ1 etop ρ2 etop'.

Lemma related_top_trans_correct_top e1 e2 :
  related_top e1 e2 <-> trans_correct_top e1 e2.
Proof.
  unfold related_top, trans_correct_top.
  split; intros H; inv H;
    split; auto; intros;
    eapply E_E; eauto;
    eapply H1; eauto;
    eapply G_top_G_top; eauto.
Qed.

(* Reflexivity of [trans_correct_top] *)
Theorem refl_related_top :
  Reflexive related_top.
Proof.
  intros e.
  eapply related_top_trans_correct_top; eauto.
  eapply Id.refl_trans_correct_top; eauto.
Qed.

(* Transitivity of [trans_correct_top] *)
Theorem trans_related_top :
  Transitive related_top.
Proof.
  intros e1 e2 e3.
  intros.
  eapply related_top_trans_correct_top; eauto.
  eapply related_top_trans_correct_top in H; eauto.
  eapply related_top_trans_correct_top in H0; eauto.
  eapply Id.trans_trans_correct_top; eauto.
Qed.

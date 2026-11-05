From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util RelComp.
From LambdaANF Require Import ANF.
From SemAnnotate Require Import LabeledANF Label ValueSetAnalysis SimpleWebAssign Reify.
From LambdaWeb Require Import ANF.

(* Compositionality of The Semantic Analysis Component *)

Module AS := LambdaANF.ANF.
Module L := Label.
Module AL := SemAnnotate.LabeledANF.
Module An := ValueSetAnalysis.
Module Aw := SimpleWebAssign.
Module R := Reify.
Module AT := LambdaWeb.ANF.

Definition trans_correct_top := Cross L.trans_correct_top
                                  (Cross An.trans_correct_top
                                     (Cross Aw.trans_correct_top
                                        R.trans_correct_top)).

(*
Definition V := Cross (fun v1 v2 => forall k, L.V k v1 v2)
                  (Cross (fun v1 v2 => exists θ, forall k, An.V_top θ k v1 v2)
                     (Cross (fun v1 v2 => exists θ ω, forall k, Aw.V_top θ ω k v1 v2)
                        (fun v1 v2 => forall k, R.V_top k v1 v2))).

Definition R := Cross (fun r1 r2 => forall k, L.R k r1 r2)
                  (Cross (fun r1 r2 => forall θ k, An.R_top θ k r1 r2)
                     (Cross (fun r1 r2 => forall θ ω k, Aw.R_top θ ω k r1 r2)
                        (fun r1 r2 => forall k, R.R_top k r1 r2))).

Definition G Γ1 := Cross (fun ρ1 ρ2 => forall k, L.G k Γ1 ρ1 ρ2)
                     (Cross (fun ρ1 ρ2 => forall θ k, An.G_top θ k Γ1 ρ1 ρ2)
                        (Cross (fun ρ1 ρ2 => forall θ ω k, Aw.G_top θ ω k Γ1 ρ1 ρ2)
                           (fun ρ1 ρ2 => forall k, R.G_top k Γ1 ρ1 ρ2))).

Lemma V_wf_val_r v1 v2:
  V v1 v2 ->
  wf_val v2.
Proof. unfold V, Cross. strivial using @R.V_top_wf_val_r. Qed.

Lemma V_exposed_r v1 v2:
  V v1 v2 ->
  exposed v2.
Proof. unfold V, Cross. strivial using @R.V_top_exposed_r. Qed.

Lemma R_V v1 v2:
  R (AS.Res v1) (AT.Res v2) ->
  V v1 v2.
Proof.
  unfold R, V, Cross.
Admitted.

Lemma R_res_inv_l v1 r2 :
  R (AS.Res v1) r2 ->
  exists v2, r2 = AT.Res v2 /\ V v1 v2.
Proof. unfold R, V, Cross. sauto. Qed.

Lemma trans_correct_top_subset e1 e2 :
  trans_correct_top e1 e2 ->
  AT.occurs_free e2 \subset AS.occurs_free e1.
Proof. unfold trans_correct_top, Cross. sfirstorder. Qed.

Lemma G_wf_env_r { Γ1 ρ1 ρ2 } :
  G Γ1 ρ1 ρ2 ->
  wf_env ρ2.
Proof. unfold G, Cross. hauto. Qed.

Lemma G_subset Γ1 Γ2 ρ1 ρ2 :
  G Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  G Γ2 ρ1 ρ2.
Proof.
  unfold G, Cross.
  intros.
  destruct H as [ρ3 [HL [ρ4 [HC HR]]]].
  exists ρ3; split.
  - sfirstorder.
  - exists ρ4; split; eauto using C.G_top_subset, R.G_top_subset.
Qed.
*)


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

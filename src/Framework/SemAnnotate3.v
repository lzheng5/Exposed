From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Util W0 ANF0 ANF1 ANF Label Checking Reify Annotate Erase RelComp.

Module AS := ANF0.
Module AI := ANF1.
Module AT := ANF.

Module L := Label.
Module C := Checking.
Module R := Reify.

Definition Top := Cross L.trans_correct_top
                    (Cross C.trans_correct_top R.trans_correct_top).

Definition V := Cross (fun v1 v2 => forall k, L.V k v1 v2)
                  (Cross (fun v1 v2 => forall k, C.V_top k v1 v2)
                     (fun v1 v2 => forall k, R.V_top k v1 v2)).

Definition R := Cross (fun r1 r2 => forall k, L.R k r1 r2)
                  (Cross (fun r1 r2 => forall k, C.R_top k r1 r2)
                     (fun r1 r2 => forall k, R.R_top k r1 r2)).

Definition G Γ1 Γ2 := Cross (fun ρ1 ρ2 => forall k, L.G_top k Γ1 ρ1 Γ2 ρ2)
                        (Cross (fun ρ1 ρ2 => forall k, C.G_top k Γ1 ρ1 Γ2 ρ2)
                           (fun ρ1 ρ2 => forall k, R.G_top k Γ1 ρ1 Γ2 ρ2)).

Lemma V_wf_val_r v1 v2:
  V v1 v2 ->
  wf_val v2.
Proof. unfold V, Cross. strivial using @R.V_top_wf_val_r. Qed.

Lemma R_V v1 v2:
  R (AS.Res v1) (AT.Res v2) ->
  V v1 v2.
Proof. unfold R, V, Cross. hauto. Qed.

Lemma R_res_inv_l v1 r2 :
  R (AS.Res v1) r2 ->
  exists v2, r2 = AT.Res v2 /\ V v1 v2.
Proof. unfold R, V, Cross. hauto. Qed.

Lemma Top_subset e1 e2 :
  Top e1 e2 ->
  AT.occurs_free e2 \subset AS.occurs_free e1.
Proof. unfold Top, Cross. sfirstorder. Qed.

Lemma G_wf_env_r { Γ1 Γ2 ρ1 ρ2 } :
  G Γ1 Γ2 ρ1 ρ2 ->
  wf_env ρ2.
Proof. unfold G, Cross. hauto. Qed.

Lemma G_n_subset Γ1 Γ2 ρ1 Γ3 Γ4 ρ2 :
  G Γ1 Γ2 ρ1 ρ2 ->
  Γ3 \subset Γ1 ->
  Γ4 \subset Γ3 ->
  G Γ3 Γ4 ρ1 ρ2.
Proof. unfold G, Cross. sfirstorder. Qed.

(* Linking Preservation *)
Lemma Top_preserves_linking f w x e1 e2 e1' e2' :
  (w \in Exposed) ->
  Top e1 e1' ->
  Top e2 e2' ->
  Top (AS.link f x e1 e2) (AT.link f w x e1' e2').
Proof.
  unfold Top, Cross.
  intros Hw.
  intros.
  destruct H as [e3 [HL1 [e4 [HC1 HR1]]]].
  destruct H0 as [e3' [HL2 [e4' [HC2 HR2]]]].

  pose proof (L.preserves_linking_top f x _ _ _ _ HL1 HL2) as HL.
  eexists; split; eauto.


(*
  destruct HC1 as [HC1 [W1 Heqe4]]; subst.
  destruct HC2 as [HC2 [W2 Heqe4']]; subst.

  assert (C.trans_correct_top (AS.link f x e3 e4) (C.link f x W1 e3' W2 e4'))

  eapply (C.preserves_linking f w x e4 e3 e4' e3') in HA1; eauto.
  eapply (C1.Top_n_preserves_linking f w x m m') in HC1; eauto.
  eapply Exposed_unique; eauto.
   *)
Admitted.

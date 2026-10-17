From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util RelComp.
From LambdaANF Require Import ANF.
From CFAAnnotate Require Import LabeledANF Label Base Annotate CFA.
From LambdaWeb Require Import ANF.

(* Compositionality of The 0CFA Annotation Component

              Label                 CFAAnnotate
   LambdaANF ---------> LabeledANF ---------------> LambdaWeb
*)

Module AS := LambdaANF.ANF.
Module AI := CFAAnnotate.LabeledANF.
Module AT := LambdaWeb.ANF.

Module L := Label.
Module C := CFA.
Module T := C.T.

Definition trans_correct_top := Cross L.trans_correct_top T.trans_correct.

Definition V := Cross (fun v1 v2 => forall k, L.V k v1 v2)
                  (fun v1 v2 => forall k, T.V k v1 v2).

Definition R := Cross (fun r1 r2 => forall k, L.R k r1 r2)
                  (fun r1 r2 => forall k, T.R k r1 r2).

Definition G Γ1 := Cross (fun ρ1 ρ2 => forall k, L.G k Γ1 ρ1 ρ2)
                     (fun ρ1 ρ2 => forall k, T.G k Γ1 ρ1 ρ2).

Lemma trans_correct_top_subset e1 e2 :
  trans_correct_top e1 e2 ->
  AT.occurs_free e2 \subset AS.occurs_free e1.
Proof.
  unfold trans_correct_top, Cross.
  intros [e' [HL HC]].
  eapply Included_trans.
  - eapply T.trans_correct_subset; eauto.
  - eapply L.trans_correct_top_subset; eauto.
Qed.

Lemma R_res_inv_l v1 r2 :
  R (AS.Res v1) r2 ->
  exists v2, r2 = AT.Res v2 /\ V v1 v2.
Proof.
  unfold R, V, Cross.
  intros [r' [HL HC]].
  destruct (L.R_res_inv_l_V _ _ HL) as [v' [Heq HLV]]; subst.
  destruct r2 as [| v2].
  - specialize (HC 0); contradiction.
  - exists v2; split; auto.
    exists v'; split; auto.
Qed.

(* Top Level *)
Theorem top l e l' e' A Rs :
  L.trans (AS.occurs_free e) l e l' e' ->
  C.check_top A Rs e' ->
  trans_correct_top e (C.annotate A e').
Proof.
  unfold trans_correct_top, Cross.
  intros HL HC.
  exists e'; split.
  - eapply L.top; eauto.
  - eapply C.top; eauto.
Qed.

(* Adequacy *)
Theorem adequacy e1 e3 :
  trans_correct_top e1 e3 ->
  forall ρ1 ρ3,
    G (AS.occurs_free e1) ρ1 ρ3 ->
    forall j1 r1,
      AS.bstep_fuel ρ1 e1 j1 r1 ->
      exists j3 r3,
        AT.bstep_fuel true ρ3 e3 j3 r3 /\
        R r1 r3.
Proof.
  unfold trans_correct_top, G, R, Cross.
  intros [e2 [HL HC]] ρ1 ρ3 [ρ2 [HLG HCG]] j1 r1 Hstep1.
  edestruct (L.adequacy _ _ HL ρ1 ρ2 HLG j1 r1 Hstep1) as [j2 [r2 [Hstep2 HLR]]].
  edestruct (C.adequacy _ _ HC ρ2 ρ3) with (j1 := j2) (r1 := r2) as [j3 [r3 [Hstep3 HCR]]]; eauto.
  - intros k.
    eapply T.G_subset; eauto.
    eapply L.trans_correct_top_subset; eauto.
  - exists j3, r3; split; auto.
    exists r2; split; auto.
Qed.

(* Linking Preservation *)
Theorem preserves_linking f x e1 e2 e1' e2' :
  trans_correct_top e1 e1' ->
  trans_correct_top e2 e2' ->
  trans_correct_top (AS.link f x e1 e2) (AT.link f w_ext x e1' e2').
Proof.
  unfold trans_correct_top, Cross.
  intros [e3 [HL1 HC1]] [e3' [HL2 HC2]].
  exists (AI.link f x e3 e3'); split.
  - eapply L.preserves_linking_top; eauto.
  - eapply C.preserves_linking; eauto.
Qed.

(* Separately labeled, analyzed and annotated compilation units can be linked. *)
Corollary top_preserves_linking f x l1 l1' l2 l2' e1 e2 e1' e2' An1 An2 R1 R2 :
  L.trans (AS.occurs_free e1) l1 e1 l1' e1' ->
  C.check_top An1 R1 e1' ->
  L.trans (AS.occurs_free e2) l2 e2 l2' e2' ->
  C.check_top An2 R2 e2' ->
  trans_correct_top (AS.link f x e1 e2) (AT.link f w_ext x (C.annotate An1 e1') (C.annotate An2 e2')).
Proof.
  intros HL1 HC1 HL2 HC2.
  eapply preserves_linking; eapply top; eauto.
Qed.

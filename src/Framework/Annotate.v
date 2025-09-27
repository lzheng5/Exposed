From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF0 ANF Refl0 Refl Erase.

Module A0 := ANF0.
Module A1 := ANF.

Module Type Annotate.

  (* For any Annotate pass, it should produce at least one exposed web ids *)
  Parameter Exposed_nonempty : exists w, w \in Exposed.

  Parameter trans : A0.vars -> A0.exp -> A1.exp -> Prop.

  (* For any Annotate passes, if e is an invalid program,
     we can always annotate the entire program with the trivial annotation to make trans complete. *)
  Parameter trans_complete :
    forall e1,
      exists e2,
        Annotate.trans (A0.occurs_free e1) e1 e2.

  (* Erase o Annotate = id *)
  Parameter Erase_Annotate_id :
    forall e1 e2 e1',
      Annotate.trans (A0.occurs_free e1) e1 e1' ->
      Erase.trans (A1.occurs_free e1') e1' e2 ->
      e1 = e2.

  (* Cross-language Logical Relations *)
  Parameter V : nat -> A0.val -> A1.wval -> Prop.

  Parameter V_wf_val_r :
    forall i v1 v2,
      V i v1 v2 ->
      wf_val v2.

  Parameter R : nat -> A0.res -> A1.res -> Prop.

  Parameter R_res_inv_l :
    forall i v1 r2,
      R i (A0.Res v1) r2 ->
      exists v2, r2 = A1.Res v2 /\ V i v1 v2.

  (* Top-level Logical Relations *)
  Parameter G_top : nat -> A0.vars -> A0.env -> A1.vars -> A1.env -> Prop.

  Parameter G_top_wf_env_r :
    forall i Γ1 ρ1 Γ2 ρ2,
      G_top i Γ1 ρ1 Γ2 ρ2 ->
      wf_env ρ2.

  Parameter G_top_subset :
    forall i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4,
      G_top i Γ1 ρ1 Γ2 ρ2 ->
      Γ3 \subset Γ1 ->
      Γ4 \subset Γ3 ->
      G_top i Γ3 ρ1 Γ4 ρ2.

  Parameter trans_correct_top : A0.exp -> A1.exp -> Prop.

  Parameter top :
    forall e1 e2,
      trans (A0.occurs_free e1) e1 e2 ->
      trans_correct_top e1 e2.

  Parameter trans_correct_top_subset :
    forall e1 e2,
      trans_correct_top e1 e2 ->
      A1.occurs_free e2 \subset A0.occurs_free e1.

  (* Adequacy *)
  Parameter adequacy :
    forall e1 e2,
      trans_correct_top e1 e2 ->
      forall ρ1 ρ2,
        wf_env ρ2 ->
        (forall k, G_top k (A0.occurs_free e1) ρ1 (A1.occurs_free e2) ρ2) ->
        forall j1 r1,
          A0.bstep_fuel ρ1 e1 j1 r1 ->
          exists j2 r2,
            A1.bstep_fuel true ρ2 e2 j2 r2 /\
            (forall k, R k r1 r2).

  (* Behavioral Refinement *)
  Parameter val_ref : A0.val -> A1.wval -> Prop.

  Parameter V_val_ref :
    forall v1 v2,
      (forall i, V i v1 v2) ->
      val_ref v1 v2.

  Parameter R_res_val_ref :
    forall v1 v2,
      (forall i, R i (A0.Res v1) (A1.Res v2)) ->
      val_ref v1 v2.

  (* Linking Preservation *)
  Parameter preserves_linking :
    forall f w x e1 e2 e1' e2',
      (w \in Exposed) ->
      trans_correct_top e1 e2 ->
      trans_correct_top e1' e2' ->
      trans_correct_top (A0.link f x e1 e1') (A1.link f w x e2 e2').

End Annotate.

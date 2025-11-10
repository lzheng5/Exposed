From CertiCoq.LambdaANF Require Import Ensembles_util.
From Framework Require Import Util ANF0 ANF Refl0 Refl Erase.

Module A0 := ANF0.
Module A1 := ANF.

Module Type Annotate.

  (* Analysis result type *)
  Parameter web_map : Type.

  (* Analysis result invariant used by transformation *)
  Parameter web_map_inv : web_map -> Prop.

  (* Analysis result specification *)
  Parameter analysis_spec : web_map -> A0.exp -> Prop.

  (* For any Annotate pass, it should produce at least one exposed web ids *)
  Parameter Exposed_nonempty : exists w, w \in Exposed.

  (* Specification *)
  Parameter trans : web_map -> A0.vars -> A0.exp -> A1.exp -> Prop.

  (* A successful analysis should always allow us to transform the program *)
  Parameter trans_total :
    forall W e1,
      web_map_inv W ->
      analysis_spec W e1 ->
      exists e2,
        trans W (A0.occurs_free e1) e1 e2.

  (* `Erase` is left inverse of `trans` *)
  (* `Erase o Annotate = id` *)
  Parameter trans_erase :
    forall W e1 e2 e1',
      Annotate.trans W (A0.occurs_free e1) e1 e1' ->
      Erase.trans (A1.occurs_free e1') e1' e2 ->
      e1 = e2.

  (* Cross-language Logical Relations *)
  Parameter V : web_map -> nat -> A0.val -> A1.wval -> Prop.

  Parameter V_wf_val_r :
    forall W i v1 v2,
      V W i v1 v2 ->
      wf_val v2.

  Parameter R : web_map -> nat -> A0.res -> A1.res -> Prop.

  Parameter R_res_inv_l :
    forall W i v1 r2,
      R W i (A0.Res v1) r2 ->
      exists v2, r2 = A1.Res v2 /\ V W i v1 v2.

  (* Top-level Logical Relations *)
  Parameter G_top : web_map -> nat -> A0.vars -> A0.env -> A1.vars -> A1.env -> Prop.

  Parameter G_top_wf_env_r :
    forall W i Γ1 ρ1 Γ2 ρ2,
      G_top W i Γ1 ρ1 Γ2 ρ2 ->
      wf_env ρ2.

  Parameter G_top_subset :
    forall W i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4,
      G_top W i Γ1 ρ1 Γ2 ρ2 ->
      Γ3 \subset Γ1 ->
      Γ4 \subset Γ3 ->
      G_top W i Γ3 ρ1 Γ4 ρ2.

  Parameter trans_correct_top : web_map -> A0.exp -> A1.exp -> Prop.

  Parameter top :
    forall W e1 e2,
      trans W (A0.occurs_free e1) e1 e2 ->
      trans_correct_top W e1 e2.

  Parameter trans_correct_top_subset :
    forall W e1 e2,
      trans_correct_top W e1 e2 ->
      A1.occurs_free e2 \subset A0.occurs_free e1.

  (* Adequacy *)
  Parameter adequacy :
    forall W e1 e2,
      web_map_inv W ->
      trans_correct_top W e1 e2 ->
      forall ρ1 ρ2,
        wf_env ρ2 ->
        (forall k, G_top W k (A0.occurs_free e1) ρ1 (A1.occurs_free e2) ρ2) ->
        forall j1 r1,
          A0.bstep_fuel ρ1 e1 j1 r1 ->
          exists j2 r2,
            A1.bstep_fuel true ρ2 e2 j2 r2 /\
            (forall k, R W k r1 r2).

  (* Behavioral Refinement *)
  Parameter val_ref : A0.val -> A1.wval -> Prop.

  Parameter V_val_ref :
    forall W v1 v2,
      (forall i, V W i v1 v2) ->
      val_ref v1 v2.

  Parameter R_res_val_ref :
    forall W v1 v2,
      (forall i, R W i (A0.Res v1) (A1.Res v2)) ->
      val_ref v1 v2.

  (* Preconditions for linking *)
  Parameter linking_inv : web_map -> var -> var -> Prop.

  (* Linking Preservation *)
  Parameter preserves_linking :
    forall W f w x e1 e2 e1' e2',
      linking_inv W f x ->
      (w \in Exposed) ->
      trans_correct_top W e1 e2 ->
      trans_correct_top W e1' e2' ->
      trans_correct_top W (A0.link f x e1 e1') (A1.link f w x e2 e2').

End Annotate.

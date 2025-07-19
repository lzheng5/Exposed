From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF.

Module ExposedUtil.

  Lemma V_mono_Forall :
    forall i j V vs1 vs2,
      (forall k : nat,
          k < S i ->
          forall (j : nat) (v1 v2 : wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
      Forall2 (V i) vs1 vs2 ->
      j <= i ->
      Forall2 (V j) vs1 vs2.
  Proof.
    intros.
    revert vs2 H0.
    induction vs1; intros; inv H0; auto.
    rename l' into vs2.
    constructor; auto.
    eapply H; eauto; lia.
  Qed.

End ExposedUtil.

Module Type LSig.

  Parameter elt : Type.

  Parameter L : M.t elt.

  Axiom L_inv_None : forall w, w \in Exposed -> L ! w = None.

  Axiom L_inv_Some : forall w d, L ! w = Some d -> (~ (w \in Exposed)).

End LSig.

Module Type LTy.

  Parameter t : Type.

End LTy.

Module DefaultL (LT : LTy) <: Exposed.LSig.

  Definition elt := LT.t.

  Parameter L : M.t elt.

  Axiom L_inv_None : forall w, w \in Exposed -> L ! w = None.

  Axiom L_inv_Some : forall w d, L ! w = Some d -> (~ (w \in Exposed)).

End DefaultL.

Module Type VTrans (LM : LSig).

  Parameter V_trans : (nat -> wval -> wval -> Prop) ->
                      (nat -> env -> exp -> env -> exp -> Prop) ->
                      nat -> LM.elt -> web -> val -> web -> val -> Prop.

  Axiom V_trans_mono :
    forall V E i j d w1 v1 w2 v2,
      (forall k : nat,
          k < S i ->
          forall (j : nat) (v1 v2 : wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
      V_trans (fun i' => V (i - (i - i'))) (fun i' => E (i - (i - i'))) i d w1 v1 w2 v2 ->
      j <= i ->
      V_trans (fun j' => V (j - (j - j'))) (fun j' => E (j - (j - j'))) j d w1 v1 w2 v2.

End VTrans.

Module ExposedV (LM : LSig) (VT : VTrans LM).

  Import VT.
  Import LM.

  (* Logical Relations with Exposed Webs *)
  Definition R' (P : nat -> wval -> wval -> Prop) (i : nat) (r1 : res) (r2 : res) :=
    match r1, r2 with
    | OOT, OOT => True
    | Res v1, Res v2 => P i v1 v2
    | _, _ => False
    end.

  Definition E' (P : nat -> wval -> wval -> Prop) (ex : bool) (i : nat) (ρ1 : env) (e1 :exp) (ρ2 : env) (e2 : exp) : Prop :=
    forall j1 r1,
      j1 <= i ->
      bstep_fuel ex ρ1 e1 j1 r1 ->
      exists j2 r2,
        bstep_fuel ex ρ2 e2 j2 r2 /\
        R' P (i - j1) r1 r2.

  Definition V_refl0 (v1 : val) (v2 : val) : Prop :=
    match v1, v2 with
    | Vconstr t1 vs1, Vconstr t2 vs2 => t1 = t2 /\ length vs1 = length vs2
    | Vfun f1 ρ1 xs1 e1, Vfun f2 ρ2 xs2 e2 => length xs1 = length xs2
    | _, _ => False
    end.

  Definition V_refl
    (V' : nat -> wval -> wval -> Prop)
    (E' : nat -> env -> exp -> env -> exp -> Prop)
    (i0 : nat) (w : web)
    (v1 : val) (v2 : val) :=
    match v1, v2 with
    | Vconstr t1 vs1, Vconstr t2 vs2 =>
        t1 = t2 /\
        Forall2 (V' i0) vs1 vs2

    | Vfun f1 ρ1 xs1 e1, Vfun f2 ρ2 xs2 e2 =>
        length xs1 = length xs2 /\
        forall j vs1 vs2 ρ3 ρ4,
          j <= i0 ->
          (w \in Exposed -> Forall exposed vs1) ->
          (w \in Exposed -> Forall exposed vs2) ->
          Forall2 (V' j) vs1 vs2 ->
          set_lists xs1 vs1 (M.set f1 (Tag w (Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
          set_lists xs2 vs2 (M.set f2 (Tag w (Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
          E' j ρ3 e1 ρ4 e2

    | _, _ => False
    end.

  Fixpoint V (i : nat) (wv1 : wval) (wv2 : wval) {struct i} : Prop :=
    wf_val wv1 /\
    wf_val wv2 /\
    match wv1, wv2 with
    | TAG _ w1 v1, TAG _ w2 v2 =>
        match i with
        | 0 =>
            match L ! w1 with
            | None => w1 = w2 /\ V_refl0 v1 v2
            | _ => True
            end

        | S i0 =>
            let V' := (fun j wv1 wv2 => V (i0 - (i0 - j)) wv1 wv2) in
            let E' b := (fun j ρ1 e1 ρ2 e2 => E' V b (i0 - (i0 - j)) ρ1 e1 ρ2 e2) in
            match L ! w1 with
            | None => w1 = w2 /\ V_refl V' (E' (exposedb w1)) i0 w1 v1 v2
            | Some d => V_trans V' (E' false) i0 d w1 v1 w2 v2
            end
        end
    end.

  Definition R := (R' V).

  Definition E := (E' V).

  (* Lemmas about V_refl0 *)
  Lemma V_refl_V_refl0 { V E i w v1 v2 }:
    V_refl V E i w v1 v2 -> V_refl0 v1 v2.
  Proof.
    unfold V_refl0.
    intros.
    destruct v1; destruct v2; simpl in H; try contradiction.
    - destruct H; auto.
    - destruct H as [Hc HF]; subst.
      split; auto.
      eapply Forall2_length; eauto.
  Qed.

  Lemma refl_V_refl0 v :
    V_refl0 v v.
  Proof.
    unfold V_refl0.
    destruct v; auto.
  Qed.

  (* Monotonicity Lemmas *)
  Lemma V_refl_mono :
    forall i V E j w v1 v2,
      (forall k : nat,
          k < S i ->
          forall (j : nat) (v1 v2 : wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
      V_refl (fun i' => V (i - (i - i'))) (fun i' => E (i - (i - i'))) i w v1 v2 ->
      j <= i ->
      V_refl (fun j' => V (j - (j - j'))) (fun j' => E (j - (j - j'))) j w v1 v2.
  Proof.
    intros.
    destruct v1; destruct v2; auto;
      simpl in *; try contradiction.
    - destruct H0.
      split; auto; intros.
      specialize (H2 j0 vs1 vs2 ρ3 ρ4).
      rewrite normalize_step in *; try lia.
      eapply H2; eauto; try lia.
    - destruct H0 as [Heqc HF];
        repeat split; auto.
      rewrite normalize_step in *; try lia.
      eapply ExposedUtil.V_mono_Forall; eauto; lia.
  Qed.

  Lemma V_mono i :
    forall {j v1 v2},
      V i v1 v2 ->
      j <= i ->
      V j v1 v2.
  Proof.
    induction i using lt_wf_rec; intros.
    destruct v1; destruct v2.
    destruct i; simpl in H0; destruct H0 as [Hv1 [Hv2 HV]]; subst.
    inv H1; simpl; split; auto.
    destruct j; simpl; repeat (split; auto);
      destruct (L ! w) eqn:Heq1; auto.
    - destruct HV; subst; split; auto.
      eapply V_refl_V_refl0; eauto.
    - eapply V_trans_mono; eauto; try lia.
    - destruct HV; subst; split; auto.
      eapply V_refl_mono; eauto; try lia.
  Qed.

  Lemma V_mono_Forall i j {vs1 vs2} :
    Forall2 (V i) vs1 vs2 ->
    j <= i ->
    Forall2 (V j) vs1 vs2.
  Proof.
    intros H.
    revert j.
    induction H; simpl; intros; auto.
    constructor; eauto.
    eapply V_mono; eauto.
  Qed.

  Lemma R_mono i j {r1 r2} :
    R i r1 r2 ->
    j <= i ->
    R j r1 r2.
  Proof.
    unfold R.
    intros.
    destruct r1; auto.
    destruct r2; auto.
    eapply V_mono; eauto.
  Qed.

  Lemma E_mono i j {ex ρ1 ρ2 e1 e2}:
    E ex i ρ1 e1 ρ2 e2 ->
    j <= i ->
    E ex j ρ1 e1 ρ2 e2.
  Proof.
    unfold E, E'.
    intros.
    destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
    exists j2, r2; split; eauto.
    apply R_mono with (i - j1); try lia; auto.
  Qed.

  (* Exposed Lemmas *)
  Lemma V_exposed v1 {i v2} :
    V i v1 v2 ->
    exposed v1 ->
    exposed v2.
  Proof.
    intros.
    destruct v1; destruct v2;
      destruct i; try contradiction; auto;
      simpl in *;
      destruct H as [Hv1 [Hv2 HV]]; subst;
      destruct (L ! w) eqn:Heqw.
    - apply L_inv_Some in Heqw.
      inv H0; contradiction.
    - destruct HV; subst.
      inv H0; inv Hv2; auto.
    - apply L_inv_Some in Heqw.
      inv H0; contradiction.
    - destruct HV; subst.
      inv H0; inv Hv2; auto.
  Qed.

  Lemma V_exposed_Forall : forall {i vs1 vs2},
      Forall2 (V i) vs1 vs2 ->
      Forall exposed vs1 ->
      Forall exposed vs2.
  Proof.
    intros.
    induction H; intros; auto.
    inv H0.
    constructor; auto.
    eapply V_exposed; eauto.
  Qed.

  Lemma V_exposed_res : forall {i v1 v2},
      V i v1 v2 ->
      exposed_res (Res v1) ->
      exposed_res (Res v2).
  Proof.
    intros.
    inv H0.
    constructor.
    eapply V_exposed; eauto.
  Qed.

  Lemma R_exposed : forall {i r1 r2},
      R i r1 r2 ->
      exposed_res r1 ->
      exposed_res r2.
  Proof.
    unfold R.
    intros.
    destruct r1;
      destruct r2;
      try contradiction; auto.
    eapply V_exposed_res; eauto.
  Qed.

  (* Lemmas about [wf_val] and [wf_res] *)
  Lemma V_wf_val_l {i v1 v2}:
    V i v1 v2 ->
    wf_val v1.
  Proof.
    intros HV.
    destruct i; simpl in *;
      destruct HV as [Hv1 [Hv2 _]]; auto.
  Qed.

  Lemma V_wf_val_r {i v1 v2}:
    V i v1 v2 ->
    wf_val v2.
  Proof.
    intros HV.
    destruct i; simpl in *;
      destruct HV as [Hv1 [Hv2 _]]; auto.
  Qed.

  Lemma V_wf_val_Forall_l {i vs1 vs2} :
    Forall2 (V i) vs1 vs2 ->
    Forall wf_val vs1.
  Proof.
    intros.
    induction H; auto.
    constructor; auto.
    eapply V_wf_val_l; eauto.
  Qed.

  Lemma V_wf_val_Forall_r {i vs1 vs2} :
    Forall2 (V i) vs1 vs2 ->
    Forall wf_val vs2.
  Proof.
    intros.
    induction H; auto.
    constructor; auto.
    eapply V_wf_val_r; eauto.
  Qed.

  Lemma V_wf_res_l {i v1 v2}:
    V i v1 v2 ->
    wf_res (Res v1).
  Proof.
    intros HV.
    constructor.
    eapply V_wf_val_l; eauto.
  Qed.

  Lemma V_wf_res_r {i v1 v2}:
    V i v1 v2 ->
    wf_res (Res v2).
  Proof.
    intros HV.
    constructor.
    eapply V_wf_val_r; eauto.
  Qed.

  Lemma R_wf_res_l {i r1 r2} :
    R i r1 r2 ->
    wf_res r1.
  Proof.
    unfold R.
    intros.
    destruct r1; destruct r2; try contradiction; auto.
    constructor.
    eapply V_wf_val_l; eauto.
  Qed.

  Lemma R_wf_res_r {i r1 r2} :
    R i r1 r2 ->
    wf_res r2.
  Proof.
    unfold R.
    intros.
    destruct r1; destruct r2; try contradiction; auto.
    constructor.
    eapply V_wf_val_r; eauto.
  Qed.

End ExposedV.

Module ExposedVG (LM : LSig) (VT : VTrans LM).

  Module EV := ExposedV LM VT.
  Export EV.

  (* Environment Relation *)
  Definition G i Γ1 ρ1 Γ2 ρ2 :=
    wf_env ρ1 /\
    wf_env ρ2 /\
    forall x,
      (x \in Γ1) ->
      forall v1,
        M.get x ρ1 = Some v1 ->
        ((x \in Γ2) ->
         exists v2,
           M.get x ρ2 = Some v2 /\
           V i v1 v2).

  (* Environment Lemmas *)
  Lemma G_empty i ρ1 Γ2 ρ2 :
    wf_env ρ1 ->
    wf_env ρ2 ->
    G i (Empty_set var) ρ1 Γ2 ρ2.
  Proof.
    unfold G; intros.
    repeat (split; auto); intros.
    inv H1.
  Qed.

  Lemma G_wf_env_l {i Γ1 ρ1 Γ2 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    wf_env ρ1.
  Proof.
    unfold G.
    intros H; destruct H; auto.
  Qed.

  Lemma G_wf_env_r {i Γ1 ρ1 Γ2 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    wf_env ρ2.
  Proof.
    unfold G.
    intros H; destruct H as [_ [H' _]]; auto.
  Qed.

  Lemma G_get {Γ1 Γ2 i ρ1 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall x v1,
      (x \in Γ1) ->
      (x \in Γ2) ->
      M.get x ρ1 = Some v1 ->
      exists v2,
        M.get x ρ2 = Some v2 /\
        V i v1 v2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hr1 [Hr2 HG]].
    eapply HG; eauto.
  Qed.

  Lemma G_get_list {i Γ1 ρ1 Γ2 ρ2} :
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall xs vs1,
      (FromList xs) \subset Γ1 ->
      (FromList xs) \subset Γ2 ->
      get_list xs ρ1 = Some vs1 ->
      exists vs2,
        get_list xs ρ2 = Some vs2 /\
        Forall2 (V i) vs1 vs2.
  Proof.
    unfold G.
    intros HG xs.
    induction xs; simpl; intros.
    - inv H1; eauto.
    - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
      destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
      inv H1.
      unfold Ensembles.Included, Ensembles.In, FromList in *.
      edestruct (G_get HG) as [v2 [Heqv2 HV]]; eauto.
      eapply (H a).
      apply in_eq.
      apply H0.
      apply in_eq.
      edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
      + intros.
        apply H.
        apply in_cons; auto.
      + intros.
        apply H0.
        apply in_cons; auto.
      + rewrite Heqvs2.
        exists (v2 :: vs2); split; auto.
        rewrite Heqv2; auto.
  Qed.

  Lemma G_set {i Γ1 ρ1 Γ2 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall {x v1 v2},
      V i v1 v2 ->
      G i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
  Proof.
    intros HG; intros.
    unfold G.
    split.

    eapply wf_env_set; eauto.
    eapply G_wf_env_l; eauto.
    eapply V_wf_val_l; eauto.

    split.
    eapply wf_env_set; eauto.
    eapply G_wf_env_r; eauto.
    eapply V_wf_val_r; eauto.

    intros.
    destruct (M.elt_eq x0 x); subst.
    - repeat rewrite M.gss in *.
      inv H1.
      eexists; split; eauto; intros.
    - rewrite M.gso in *; auto.
      edestruct (G_get HG) as [v2' [Heqv2' HV]]; eauto.
      + inv H0; auto.
        inv H3; contradiction.
      + inv H2; auto.
        inv H3; contradiction.
  Qed.

  Lemma G_set_lists {i Γ1 ρ1 Γ2 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall {xs vs1 vs2 ρ3 ρ4},
      Forall2 (V i) vs1 vs2 ->
      set_lists xs vs1 ρ1 = Some ρ3 ->
      set_lists xs vs2 ρ2 = Some ρ4 ->
      G i (FromList xs :|: Γ1) ρ3 (FromList xs :|: Γ2) ρ4.
  Proof.
    intros HG xs.
    induction xs; simpl; intros.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      inv H0; inv H1.
      unfold G.

      split.
      eapply G_wf_env_l; eauto.

      split.
      eapply G_wf_env_r; eauto.

      intros.
      eapply (G_get HG); eauto.
      inv H0; auto.
      inv H3.

      inv H2; auto.
      inv H3.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
      destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
      inv H; inv H0; inv H1.
      unfold G.

      split.
      eapply wf_env_set; eauto.
      eapply (wf_env_set_lists ρ1) with (xs := xs) (vs := vs1); eauto.
      eapply G_wf_env_l; eauto.
      eapply V_wf_val_Forall_l; eauto.
      eapply V_wf_val_l; eauto.

      split.
      eapply wf_env_set; eauto.
      eapply (wf_env_set_lists ρ2) with (xs := xs) (vs := vs2); eauto.
      eapply G_wf_env_r; eauto.
      eapply V_wf_val_Forall_r; eauto.
      eapply V_wf_val_r; eauto.

      intros.
      destruct (M.elt_eq x a); subst.
      + repeat rewrite M.gss in *; eauto.
        inv H0.
        eexists; split; eauto.
      + rewrite M.gso in *; auto.
        eapply IHxs; eauto.
        eapply not_In_cons_Union; eauto.
        eapply not_In_cons_Union; eauto.
  Qed.

  Lemma G_subset Γ1 Γ2 {i ρ1 Γ3 ρ2 Γ4}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    Γ3 \subset Γ1 ->
    Γ4 \subset Γ2 ->
    G i Γ3 ρ1 Γ4 ρ2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hr1 [Hr2 HG]].
    repeat (split; auto); intros.
  Qed.

  (* Monotonicity Lemmas *)
  Lemma G_mono {Γ1 Γ2 ρ1 ρ2} i j:
    G i Γ1 ρ1 Γ2 ρ2 ->
    j <= i ->
    G j Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hr1 [Hr2 HG]].
    repeat (split; auto); intros.
    edestruct HG as [v2 [Heqv2 HV]]; eauto.
    eexists; eexists; repeat split; eauto.
    apply V_mono with i; eauto.
  Qed.

End ExposedVG.

Module Exposed (LM : LSig) (VT : VTrans LM).

  Module EG := ExposedVG LM VT.
  Export EG.
  Import VT.
  Import LM.

  Definition trans_correct Γ e1 e2 :=
    forall ex i ρ1 ρ2,
      G i Γ ρ1 (occurs_free e2) ρ2 ->
      E ex i ρ1 e1 ρ2 e2.

  (* Compatibility Lemmas *)
  Lemma ret_compat Γ x :
    (x \in Γ) ->
    trans_correct Γ (Eret x) (Eret x).
  Proof.
    unfold trans_correct, E, E', R, R', Ensembles.Included, Ensembles.In, Dom_map.
    intros.
    inv H2.
    - exists 0, OOT; split; auto.
    - inv H3.
      edestruct (G_get H0) as [v2 [Heqv2 HV]]; eauto.
      exists 1, (Res v2); split; auto.
      + constructor; auto.
        destruct ex; auto.
        eapply V_exposed_res; eauto.
      + apply V_mono with i; try lia; auto.
  Qed.

  Lemma constr_compat Γ x w t xs k k' :
    L ! w = None ->
    (FromList xs \subset Γ) ->
    trans_correct (x |: Γ) k k' ->
    trans_correct Γ (Econstr x w t xs k) (Econstr x w t xs k').
  Proof.
    unfold trans_correct, E, E', Ensembles.Included, Ensembles.In, FromList.
    intros.
    inv H4.
    - exists 0, OOT; split; simpl; auto.
    - inv H5.
      destruct (G_get_list H2 xs vs) as [vs' [Heqvs' Hvs]]; auto.
      + unfold Ensembles.Included, Ensembles.In, FromList in *.
        intros; auto.
      + assert (wf_val (Tag w (Vconstr t vs))).
        {
          apply wf_val_Vconstr; auto.
          eapply V_wf_val_Forall_l; eauto.
        }

        assert (wf_val (Tag w (Vconstr t vs'))).
        {
          apply wf_val_Vconstr; auto.
          eapply V_wf_val_Forall_r; eauto.
          intros.
          eapply V_exposed_Forall; eauto.
        }

        assert (length vs = length vs').
        {
          unfold wval in *.
          rewrite <- (get_list_length_eq _ _ _ H13).
          rewrite <- (get_list_length_eq _ _ _ Heqvs'); auto.
        }

        edestruct (H1 ex i (M.set x (Tag w (Vconstr t vs)) ρ1) (M.set x (Tag w (Vconstr t vs')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk' Rr]]]; eauto; try lia.
        * eapply G_subset; eauto.
          eapply G_set; eauto.
          -- destruct i; simpl; repeat (split; eauto);
               destruct (L ! w) eqn:Heq1; try discriminate;
               repeat split; auto.
             eapply V_mono_Forall; eauto; lia.
          -- apply Included_refl.
          -- apply free_constr_k_subset.
        * exists (S j2), r2; split; eauto.
          -- constructor; auto.
             econstructor; eauto.
             intros.
             eapply V_exposed_Forall; eauto.
             destruct ex; auto.
             eapply R_exposed; eauto.
          -- apply R_mono with (i - c); try lia; auto.
  Qed.

  Lemma Vfun_V Γ1 f xs e e' :
    trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
    forall {i Γ2 ρ1 ρ2 w},
      L ! w = None ->
      G i Γ1 ρ1 Γ2 ρ2 ->
      occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
      V i (Tag w (Vfun f ρ1 xs e)) (Tag w (Vfun f ρ2 xs e')).
  Proof.
    unfold trans_correct.
    intros He i.
    induction i; simpl; intros; auto;
      assert (wf_env ρ1) by (eapply G_wf_env_l; eauto);
      assert (wf_env ρ2) by (eapply G_wf_env_r; eauto);
      repeat (split; auto); intros;
      destruct (L ! w) eqn:Heq1; try discriminate; auto.
    repeat (split; auto); intros.
    apply (He (exposedb w) (i - (i - j)) ρ3 ρ4); auto.
    eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))).
    eapply G_set_lists; eauto.
    eapply G_set; eauto.
    apply G_mono with (S i); eauto; lia.
    - apply V_mono with i; try lia.
      eapply IHi with (Γ2 := Γ2); eauto.
      apply G_mono with (S i); eauto; lia.
    - apply Included_refl.
    - auto.
  Qed.

  Lemma fun_compat Γ e e' k k' f w xs :
    L ! w = None ->
    trans_correct (FromList xs :|: (f |: Γ)) e e' ->
    trans_correct (f |: Γ) k k' ->
    trans_correct Γ (Efun f w xs e k) (Efun f w xs e' k').
  Proof.
    unfold trans_correct, E, E'.
    intros.
    inv H4.
    - exists 0, OOT; split; simpl; eauto.
    - inv H5.
      edestruct (H1 ex (i - 1) (M.set f (Tag w (Vfun f ρ1 xs e)) ρ1) (M.set f (Tag w (Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + eapply G_subset with (Γ2 := (f |: occurs_free (Efun f w xs e' k'))).
        eapply G_set; eauto.
        apply G_mono with i; eauto; lia.
        * eapply Vfun_V; eauto.
          -- apply G_mono with i; eauto; lia.
          -- apply free_fun_e_subset.
        * apply Included_refl.
        * apply free_fun_k_subset.
      + exists (S j2), r2; split; auto.
        * constructor; auto.
          destruct ex; auto.
          eapply R_exposed; eauto.
        * apply R_mono with ((i - 1) - c); try lia; auto.
  Qed.

  Lemma app_compat Γ xs f w :
    L ! w = None ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct Γ (Eapp f w xs) (Eapp f w xs).
  Proof.
    unfold trans_correct, G, E, E'.
    intros.
    inv H4.
    - exists 0, OOT; split; simpl; auto.
    - inv H5.
      unfold Ensembles.Included, Ensembles.In, Dom_map in *.
      edestruct (G_get H2) as [fv2 [Heqfv2 HV]]; eauto.
      destruct fv2.
      destruct i.
      inv H3.
      simpl in HV.
      destruct HV as [Hv1 [Hv2 HVv]]; subst.
      destruct (L ! w) eqn:Heqw; try discriminate.
      destruct HVv as [Hw HVv]; subst.
      destruct v; try contradiction.
      destruct HVv as [Hlen HVv].

      edestruct (G_get_list H2 xs vs) as [vs2 [Heqvs2 Vvs]]; eauto.
      {
        unfold Ensembles.Included, Ensembles.In, FromList, Dom_map.
        intros; auto.
      }

      destruct (set_lists_length3 (M.set v (Tag w0 (Vfun v t l e0)) t) l vs2) as [ρ4 Heqρ4].
      unfold wval in *.
      rewrite <- (Forall2_length _ _ _ Vvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H11); auto.

      assert (HE : E (exposedb w0) (i - (i - i)) ρ'' e ρ4 e0).
      {
        eapply (HVv i vs vs2); eauto.
        - intros.
          destruct H15; auto.
        - intros.
          destruct H15; auto.
          eapply V_exposed_Forall; eauto.
        - apply V_mono_Forall with (S i); auto; lia.
      }

      apply (E_mono _ i) in HE; try lia.
      unfold E in HE.
      destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
      exists (S j2), r2; split; eauto.
      constructor; auto.
      + eapply BStep_app; eauto.
        intros.
        destruct H15; auto.
        split.
        eapply V_exposed_Forall; eauto.
        eapply R_exposed; eauto.
      + destruct ex; auto.
        eapply R_exposed; eauto.
  Qed.

  Lemma letapp_compat Γ k k' w xs x f :
    L ! w = None ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct (x |: Γ) k k' ->
    trans_correct Γ (Eletapp x f w xs k) (Eletapp x f w xs k').
  Proof.
    intros.
    specialize (app_compat Γ xs f w H H0 H1); intros Ha.
    unfold trans_correct, E, E' in *.
    intros.

    assert (HG' : G i Γ ρ1 (occurs_free (Eapp f w xs)) ρ2).
    {
      eapply G_subset with (Γ2 := (occurs_free (Eletapp x f w xs k'))); eauto.
      apply Included_refl.
      eapply free_app_letapp; eauto.
    }

    inv H5.
    - exists 0, OOT; split; simpl; auto.
    - inv H6.
      + destruct (Ha (exposedb w) i ρ1 ρ2) with (j1 := (S c0)) (r1 := (Res v)) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
        * constructor; auto.
          eapply BStep_app; eauto.
          intros.
          destruct H18; auto.
          destruct (exposed_reflect w); try contradiction; auto.
          destruct H18; auto.
        * simpl in HR.
          destruct r2; try contradiction.
          rename w0 into v0.
          inv Hr1.
          edestruct (H2 ex (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
          -- eapply G_subset with (Γ2 := (x |: (occurs_free (Eletapp x f w xs k')))).
             eapply G_set; eauto.
             apply G_mono with i; try lia; eauto.
             apply Included_refl.
             apply free_letapp_k_subset.
          -- exists ((S c) + j2), r2; split.
             ++ inv H5.
                assert (Hc : (S c + j2) = S (c + j2)) by lia.
                rewrite Hc.
                constructor; auto.
                ** eapply BStep_letapp_Res; eauto.
                   intros.
                   destruct H23; auto.
                   inv H9.
                   split; auto.
                ** destruct ex; auto.
                   eapply R_exposed; eauto.
             ++ apply R_mono with (i - S c0 - c'); try lia; auto.
      + destruct (Ha (exposedb w) i ρ1 ρ2) with (j1 := (S c)) (r1 := OOT) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
        constructor; eauto.
        destruct (exposed_reflect w); try contradiction; auto.
        exists j2, r2.
        destruct r2; try contradiction.
        split; auto.
        inv Hr1; eauto.
        inv H5; eauto.
        constructor; auto.
        eapply BStep_letapp_OOT; eauto.
        * intros.
          destruct H22; auto.
  Qed.

  Lemma proj_compat Γ x w i y e e' :
    L ! w = None ->
    (y \in Γ) ->
    trans_correct (x |: Γ) e e' ->
    trans_correct Γ (Eproj x w i y e) (Eproj x w i y e').
  Proof.
    unfold trans_correct, E, E'.
    intros.
    inv H4.
    - exists 0, OOT; split; simpl; auto.
    - inv H5.
      edestruct (G_get H2) as [v2 [Heqv2 HV]]; eauto.
      destruct v2.
      destruct v0; destruct i0;
        simpl in HV;
        destruct HV as [Hv1 [Hv2 HV]]; subst;
        destruct (L ! w) eqn:Heq1; try discriminate;
        destruct HV as [Hw HV]; subst; try contradiction.
      inv H3.
      rename l into vs'.
      rename c0 into t'.
      destruct HV as [Heqt HFvs]; subst.
      destruct (Forall2_nth_error H14 HFvs) as [v' [Heqv' HFv]].
      edestruct (H1 ex i0 (M.set x v ρ1) (M.set x v' ρ2)) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
      + eapply G_subset with (Γ2 := (x |: (occurs_free (Eproj x w0 i y e')))).
        eapply G_set.
        eapply G_mono with (S i0); eauto; try lia.
        rewrite normalize_step in *; try lia; auto.
        apply Included_refl.
        apply free_proj_k_subset.
      + exists (S j2), r2; split.
        * constructor; eauto.
          destruct ex; auto.
          eapply R_exposed; eauto.
        * eapply R_mono; eauto; lia.
  Qed.

  Lemma case_nil_compat Γ x w:
    (x \in Γ) ->
    trans_correct Γ (Ecase x w []) (Ecase x w []).
  Proof.
    unfold trans_correct, E, E'.
    intros.
    inv H2.
    - exists 0, OOT; split; simpl; auto.
    - inv H3.
      inv H10.
  Qed.

  Lemma case_cons_compat Γ x w t e e' cl cl':
    L ! w = None ->
    (x \in Γ) ->
    trans_correct Γ e e' ->
    trans_correct Γ (Ecase x w cl) (Ecase x w cl') ->
    trans_correct Γ (Ecase x w ((t, e) :: cl)) (Ecase x w ((t, e') :: cl')).
  Proof.
    unfold trans_correct, E, E'.
    intros.
    inv H5.
    - exists 0, OOT; split; simpl; eauto.
    - inv H6.
      edestruct (G_get H3) as [v2 [Heqv2 HV]]; eauto.
      destruct v2.
      destruct i.
      inv H4.
      destruct v; simpl in HV;
        destruct HV as [Hv1 [Hv2 HV]]; subst;
        destruct (L ! w) eqn:Heq1; try discriminate;
        destruct HV as [Hw HV]; subst; try contradiction.
      destruct HV as [Heqt HFvs]; subst.
      inv H13.
      + edestruct (H1 ex i ρ1 ρ2) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
        eapply G_subset with (Γ2 := (occurs_free (Ecase x w0 ((c0, e') :: cl')))); eauto.
        eapply G_mono; eauto.
        apply Included_refl.
        apply free_case_hd_subset.
        exists (S j2), r2; split.
        * constructor; eauto.
          destruct ex; auto.
          eapply R_exposed; eauto.
        * eapply R_mono; eauto; lia.
      + edestruct (H2 ex (S i) ρ1 ρ2) with (j1 := S c) (r1 := r1) as [j2 [r2 [He' HR]]]; eauto; try lia.
        eapply G_subset; eauto.
        apply Included_refl.
        apply free_case_tl_subset; auto.
        exists j2, r2; split; eauto.
        inv He'; auto.
        inv H5.
        rewrite Heqv2 in H13; inv H13; eauto.
Qed.

End Exposed.

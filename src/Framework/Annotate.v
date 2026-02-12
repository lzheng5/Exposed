From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Util ANF0 ANF Refl0 Refl Erase.

Module A0 := ANF0.
Module A1 := ANF.

Module AnnotateUtil.

  Lemma V_mono_Forall_aux :
    forall i j V vs1 vs2,
      (forall k : nat,
          k < S i ->
          forall (j : nat) (v1 : A0.val) (v2 : A1.wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
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

  Lemma V_mono_Forall_mono (V : nat -> A0.val -> A1.wval -> Prop) :
    (forall i j v1 v2, V i v1 v2 -> j <= i -> V j v1 v2) ->
    forall i j {vs1 vs2},
      Forall2 (V i) vs1 vs2 ->
      j <= i ->
      Forall2 (V j) vs1 vs2.
  Proof.
    intros V_mono. intros.
    revert j H0.
    induction H; simpl; intros; auto.
    constructor; eauto.
  Qed.

  Definition V_ex0 (v1 : A0.val) (v2 : A1.val) : Prop :=
    match v1, v2 with
    | A0.Vconstr t1 vs1, A1.Vconstr t2 vs2 => t1 = t2 /\ length vs1 = length vs2
    | A0.Vfun f1 ρ1 xs1 e1, A1.Vfun f2 ρ2 xs2 e2 => length xs1 = length xs2
    | _, _ => False
    end.

  Definition V_ex
    (V' : nat -> A0.val -> A1.wval -> Prop)
    (E' : nat -> A0.env -> A0.exp -> A1.env -> A1.exp -> Prop)
    (i0 : nat) (v1 : A0.val) (w2 : web) (v2 : A1.val) :=
    match v1, v2 with
    | A0.Vconstr t1 vs1, A1.Vconstr t2 vs2 =>
        t1 = t2 /\
        Forall2 (V' i0) vs1 vs2

    | A0.Vfun f1 ρ1 xs1 e1, A1.Vfun f2 ρ2 xs2 e2 =>
        length xs1 = length xs2 /\
        forall j vs1 vs2 ρ3 ρ4,
          j <= i0 ->
          Forall exposed vs2 ->
          Forall2 (V' j) vs1 vs2 ->
          set_lists xs1 vs1 (M.set f1 (A0.Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
          set_lists xs2 vs2 (M.set f2 (Tag w2 (A1.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
          E' j ρ3 e1 ρ4 e2
    | _, _ => False
    end.

  Lemma V_ex_V_ex0 { V E i v1 w2 v2 }:
    V_ex V E i v1 w2 v2 -> V_ex0 v1 v2.
  Proof.
    unfold V_ex, V_ex0.
    intros.
    destruct v1; destruct v2; simpl in H; try contradiction.
    - fcrush.
    - destruct H as [Hc HF]; subst.
      split; auto.
      eapply Forall2_length; eauto.
  Qed.

  Definition R' (P : nat -> A0.val -> A1.wval -> Prop) (i : nat) (r1 : A0.res) (r2 : A1.res) :=
    match r1, r2 with
    | A0.OOT, A1.OOT => True
    | A0.Res v1, A1.Res v2 => P i v1 v2
    | _, _ => False
    end.

  Definition E' (P : nat -> A0.val -> A1.wval -> Prop) (ex : bool) (i : nat) (ρ1 : A0.env) (e1 :A0.exp) (ρ2 : A1.env) (e2 : A1.exp) : Prop :=
    forall j1 r1,
      j1 <= i ->
      A0.bstep_fuel ρ1 e1 j1 r1 ->
      exists j2 r2,
        A1.bstep_fuel ex ρ2 e2 j2 r2 /\
        R' P (i - j1) r1 r2.

End AnnotateUtil.

Module Type VAnn.

  Parameter V_ann0 : A0.val -> A1.val -> Prop.

  Parameter V_ann : (nat -> A0.val -> A1.wval -> Prop) ->
                    (bool -> nat -> A0.env -> A0.exp -> A1.env -> A1.exp -> Prop) ->
                    nat -> A0.val -> web -> A1.val -> Prop.

  Parameter V_ann_V_ann0 :
    forall V E i v1 w2 v2,
      V_ann V E i v1 w2 v2 ->
      V_ann0 v1 v2.

  Parameter V_ann_mono :
    forall V E i j v1 w2 v2,
      (forall k : nat,
          k < S i ->
          forall (j : nat) (v1 : A0.val) (v2 : A1.wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
      V_ann (fun i' => V (i - (i - i'))) (fun b i' => E b (i - (i - i'))) i v1 w2 v2 ->
      j <= i ->
      V_ann (fun j' => V (j - (j - j'))) (fun b j' => E b (j - (j - j'))) j v1 w2 v2.

End VAnn.

Module AnnotateV (VA : VAnn).

  Import VA.
  Export AnnotateUtil.

  (* Cross-language Logical Relations *)
  Fixpoint V (i : nat) (v1 : A0.val) (wv2 : A1.wval) {struct i} : Prop :=
    wf_val wv2 /\
    match wv2 with
    | A1.TAG _ w2 v2 =>
        match i with
        | 0 =>
            match exposedb w2 with
            | true => exposed wv2 /\ V_ex0 v1 v2
            | false => V_ann0 v1 v2
            end

        | S i0 =>
            let V' := (fun j v1 wv2 => V (i0 - (i0 - j)) v1 wv2) in
            let E' b := (fun j ρ1 e1 ρ2 e2 => E' V b (i0 - (i0 - j)) ρ1 e1 ρ2 e2) in
            match exposedb w2 with
            | true => exposed wv2 /\ V_ex V' (E' true) i0 v1 w2 v2
            | false => V_ann V' E' i0 v1 w2 v2
            end
        end
    end.

  Definition R := (R' V).

  Definition E := (E' V).

  (* Lemmas about [wf_val], [wf_res], and [wf_env] *)
  Lemma V_wf_val_r {i v1 v2}:
    V i v1 v2 ->
    wf_val v2.
  Proof.
    intros HV.
    destruct i; simpl in *;
      destruct HV as [Hv2 _]; auto.
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
    wf_res r2.
  Proof.
    unfold R.
    intros.
    destruct r1; destruct r2; try contradiction; auto.
    constructor.
    eapply V_wf_val_r; eauto.
  Qed.

  (* Inversion Lemmas *)
  Lemma R_res_inv_l i v1 r2 :
    R i (A0.Res v1) r2 ->
    exists v2, r2 = A1.Res v2 /\ V i v1 v2.
  Proof.
    intros.
    destruct r2; simpl in *; try contradiction.
    eexists; split; eauto.
  Qed.

  (* Monotonicity Lemmas *)
  Lemma V_ex_mono :
    forall i V E j v1 w2 v2,
      (forall k : nat,
          k < S i ->
          forall (j : nat) (v1 : A0.val) (v2 : wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
      V_ex (fun i' => V (i - (i - i'))) (fun i' => E (i - (i - i'))) i v1 w2 v2 ->
      j <= i ->
      V_ex (fun j' => V (j - (j - j'))) (fun j' => E (j - (j - j'))) j v1 w2 v2.
  Proof.
    unfold V_ex.
    intros.
    destruct v1; destruct v2; auto;
      simpl in *; try contradiction.
    - destruct H0 as [Hlen HV].
      repeat (split; auto); intros.
      specialize (HV j0 vs1 vs2 ρ3 ρ4).
      rewrite normalize_step in *; try lia.
      eapply HV; eauto; try lia.
    - destruct H0 as [Heqc HF];
        repeat split; auto.
      rewrite normalize_step in *; try lia.
      eapply V_mono_Forall_aux; eauto; lia.
  Qed.

  Lemma V_mono i :
      forall {j v1 v2},
        V i v1 v2 ->
        j <= i ->
        V j v1 v2.
    Proof.
      induction i using lt_wf_rec; intros.
      destruct v2.
      destruct i; simpl in H0;
        destruct j; simpl; intros;
        destruct H0 as [Hv1 HV]; subst.
      - repeat (split; auto).
      - inv H1.
      - repeat (split; auto).
        destruct (exposed_reflect w).
        + inv HV; split; auto.
          eapply V_ex_V_ex0; eauto.
        + eapply V_ann_V_ann0; eauto.
      - repeat (split; auto).
        destruct (exposed_reflect w).
        + inv HV; split; auto.
          eapply V_ex_mono; eauto; lia.
        + eapply V_ann_mono; eauto; lia.
    Qed.

  Lemma V_mono_Forall i j {vs1 vs2} :
    Forall2 (V i) vs1 vs2 ->
    j <= i ->
    Forall2 (V j) vs1 vs2.
  Proof.
    intros.
    eapply V_mono_Forall_mono; eauto.
    eapply V_mono; eauto.
  Qed.

  Lemma R_mono {r1 r2} i j :
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

  Lemma E_mono {ex ρ1 ρ2 e1 e2} i j:
    E ex i ρ1 e1 ρ2 e2 ->
    j <= i ->
    E ex j ρ1 e1 ρ2 e2.
  Proof.
    unfold E, R, E', R'.
    intros.
    destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
    exists j2, r2; split; eauto.
    apply R_mono with (i - j1); try lia; auto.
  Qed.

End AnnotateV.

Module AnnotateTop.

  (* The top-level exposed relation is exactly the relation induced by the trivial analysis *)
  Module VTrivM <: VAnn.

    Definition V_ann0 (v1 : A0.val) (v2 : A1.val) : Prop := False.

    Definition V_ann
      (V' : nat -> A0.val -> A1.wval -> Prop)
      (E' : bool -> nat -> A0.env -> A0.exp -> A1.env -> A1.exp -> Prop)
      (i0 : nat) (v1 : A0.val) (w2 : web) (v2 : A1.val) := False.

    Lemma V_ann_V_ann0 :
      forall V E i v1 w2 v2,
        V_ann V E i v1 w2 v2 ->
        V_ann0 v1 v2.
    Proof. unfold V_ann, V_ann0; auto. Qed.

    Lemma V_ann_mono V E i j v1 w2 v2 :
      (forall k : nat,
          k < S i ->
          forall (j : nat) (v1 : A0.val) (v2 : A1.wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
      V_ann (fun i' => V (i - (i - i'))) (fun b i' => E b (i - (i - i'))) i v1 w2 v2 ->
      j <= i ->
      V_ann (fun j' => V (j - (j - j'))) (fun b j' => E b (j - (j - j'))) j v1 w2 v2.
    Proof. unfold V_ann. intros; fcrush. Qed.

  End VTrivM.

  Module VM := AnnotateV VTrivM.
  Export VM.

  (* Top-level Exposed Lemmas *)
  Lemma V_exposed_r {i v1 v2}:
    V i v1 v2 ->
    exposed v2.
  Proof.
    intros.
    destruct i; destruct v2;
      simpl in *; fcrush.
  Qed.

  Lemma V_exposed_Forall_r {i vs1 vs2} :
    Forall2 (V i) vs1 vs2 ->
    Forall exposed vs2.
  Proof.
    intros.
    induction H; auto.
    constructor; auto.
    eapply V_exposed_r; eauto.
  Qed.

  (* Top-level Environment Relation *)
  Definition G i Γ1 ρ1 Γ2 ρ2 :=
    wf_env ρ2 /\
    Γ2 \subset Γ1 /\
    forall x,
      (x \in Γ1) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
        M.get x ρ2 = Some v2 /\
        V i v1 v2.

  Lemma G_wf_env_r i Γ1 ρ1 Γ2 ρ2 :
    G i Γ1 ρ1 Γ2 ρ2 ->
    wf_env ρ2.
  Proof. unfold G. intros; tauto. Qed.

  Lemma G_subset_inv i Γ1 ρ1 Γ2 ρ2 :
    G i Γ1 ρ1 Γ2 ρ2 ->
    Γ2 \subset Γ1.
  Proof. unfold G; intros; tauto. Qed.

  Lemma G_subset i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4 :
    G i Γ1 ρ1 Γ2 ρ2 ->
    Γ3 \subset Γ1 ->
    Γ4 \subset Γ3 ->
    G i Γ3 ρ1 Γ4 ρ2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hr [Hs HG]].
    repeat (split; auto).
  Qed.

  (* Top-level Monotonicity Lemma *)
  Lemma G_mono {Γ1 Γ2 ρ1 ρ2} i j:
      G i Γ1 ρ1 Γ2 ρ2 ->
      j <= i ->
      G j Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hwf [HS HG]].
    split; auto.
    split; auto; intros.
    edestruct HG as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto.
    eexists; eexists; repeat (split; eauto).
    apply V_mono with i; eauto.
  Qed.

  (* Top-level Relation *)
  Definition trans_correct etop etop' :=
    A1.occurs_free etop' \subset A0.occurs_free etop /\
    forall i ρ1 ρ2,
      G i (A0.occurs_free etop) ρ1 (A1.occurs_free etop') ρ2 ->
      E true i ρ1 etop ρ2 etop'.

  Lemma trans_correct_subset e1 e2 :
    trans_correct e1 e2 ->
    A1.occurs_free e2 \subset A0.occurs_free e1.
  Proof.
    unfold trans_correct.
    intros.
    inv H; auto.
  Qed.

  (* Cross-language Compositionality *)

  (* Adequacy *)
  Theorem adequacy e1 e2:
    trans_correct e1 e2 ->
    forall ρ1 ρ2,
      wf_env ρ2 ->
      (forall k, G k (A0.occurs_free e1) ρ1 (A1.occurs_free e2) ρ2) ->
      forall j1 r1,
        A0.bstep_fuel ρ1 e1 j1 r1 ->
        exists j2 r2,
          A1.bstep_fuel true ρ2 e2 j2 r2 /\
          (forall k, R k r1 r2).
  Proof.
    intros.
    unfold trans_correct in H.
    destruct H as [HS HT].

    assert (HE : E true j1 ρ1 e1 ρ2 e2) by (eapply (HT j1); eauto).
    edestruct (HE j1) as [j2 [r2 [Hstep2 HR]]]; eauto.
    eexists; eexists; split; eauto.

    intros.
    assert (HE' : E true (j1 + k) ρ1 e1 ρ2 e2) by (eapply HT; eauto).
    edestruct (HE' j1) as [j2' [r2' [Hstep2' HR']]]; eauto; try lia.

    rewrite_math (j1 + k - j1 = k).
    rewrite_math (j1 - j1 = 0).

    destruct r2; destruct r2'; destruct r1;
      simpl in *; auto; try contradiction.

    edestruct (A1.bstep_fuel_deterministic w w0 Hstep2 Hstep2'); subst; eauto.
  Qed.

  (* Behavioral Refinement *)
  Inductive val_ref_ : A0.val -> A1.wval -> Prop :=
  | Ref_Vfun :
    forall f1 ρ1 w xs1 e1 f2 ρ2 xs2 e2,
      val_ref_ (A0.Vfun f1 ρ1 xs1 e1) (Tag w (A1.Vfun f2 ρ2 xs2 e2))

  | Ref_Vconstr_nil :
    forall w c,
      val_ref_ (A0.Vconstr c []) (Tag w (A1.Vconstr c []))

  | Ref_Vconstr_cons :
    forall w c v1 v2 vs1 vs2,
      val_ref_ v1 v2 ->
      val_ref_ (A0.Vconstr c vs1) (Tag w (A1.Vconstr c vs2)) ->
      val_ref_ (A0.Vconstr c (v1 :: vs1)) (Tag w (A1.Vconstr c (v2 :: vs2))).

  Hint Constructors val_ref_ : core.

  Definition val_ref := val_ref_.

  Hint Unfold val_ref : core.

  Lemma val_ref_Vconstr c w vs1 vs2 :
    Forall2 val_ref vs1 vs2 ->
    val_ref (A0.Vconstr c vs1) (Tag w (A1.Vconstr c vs2)).
  Proof.
    intros.
    induction H; simpl; auto.
  Qed.

  Theorem V_val_ref {v1 v2} :
    (forall i, V i v1 v2) ->
    val_ref v1 v2.
  Proof.
    unfold val_ref.
    revert v2.
    induction v1 using val_ind'; intros; simpl.
    - specialize (H 0).
      destruct v2.
      simpl in H.
      destruct H as [Hwf HV].
      destruct (exposed_reflect w); inv HV.
      destruct v; try contradiction.
      inv H0.
      destruct l; try discriminate; auto.
    - destruct v2.
      pose proof (H 0) as H0; simpl in *.
      destruct H0 as [Hw HV].
      destruct (exposed_reflect w); inv HV.
      destruct v; try contradiction.
      destruct H1 as [Hc Hlen]; subst.

      destruct l0; simpl in *; inv Hlen.
      inv H0.

      assert (HV' : forall i, V i v1 t /\ V i (A0.Vconstr c l) (Tag w (A1.Vconstr c l0))).
      {
        intros.
        specialize (H (S i0)); simpl in *.
        destruct H as [_ HV]; subst.
        destruct (exposed_reflect w); try contradiction.
        destruct HV as [Hex [Hc HFV]]; subst; eauto.

        inv HFV.
        split.
        eapply V_mono; eauto; lia.

        assert (He' : exposed (Tag w (A1.Vconstr c l0))).
        {
          inv Hex; inv H6; auto.
        }

        assert (Hw' : wf_val (Tag w (A1.Vconstr c l0))).
        {
          constructor; intros; auto.
          inv Hw.
          inv H5; auto.
        }

        inv H6.
        inv Hw.
        inv H8.
        destruct i0; simpl in *;
          destruct (exposed_reflect w); try contradiction;
          repeat (split; auto);
          simpl in *;
          rewrite_math (i0 - i0 = 0);
          rewrite_math (i0 - 0 = i0);
          try (eapply V_mono_Forall; eauto; lia).
      }

      assert (HV0 : forall i, V i v1 t) by (intros i0; destruct (HV' i0); auto).
      assert (HV1 : forall i, V i (A0.Vconstr c l) (Tag w (A1.Vconstr c l0))) by (intros i0; destruct (HV' i0); auto).
      auto.
    - specialize (H 0); simpl in *.
      destruct H as [Hw HV].
      destruct v2; try contradiction; auto.
      destruct (exposed_reflect w); inv HV.
      destruct v; try contradiction; auto.
  Qed.

  Corollary R_res_val_ref {v1 v2} :
    (forall i, R i (A0.Res v1) (A1.Res v2)) ->
    val_ref v1 v2.
  Proof. intros; eapply V_val_ref; eauto. Qed.

  (* Linking Compat Lemmas *)

  (* Top-level Environment Lemmas *)
  Lemma G_get {Γ1 Γ2 i ρ1 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall x,
      (x \in Γ1) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
        M.get x ρ2 = Some v2 /\
        V i v1 v2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hr1 [HΓ HG]].
    eapply (HG x); eauto.
  Qed.

  Lemma G_get_list {i Γ1 ρ1 Γ2 ρ2} :
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall xs,
      (FromList xs) \subset Γ1 ->
      exists vs1 vs2,
        get_list xs ρ1 = Some vs1 /\
        get_list xs ρ2 = Some vs2 /\
        Forall2 (V i) vs1 vs2.
  Proof.
    intros HG xs.
    intros.
    induction xs; simpl; intros.
    - eexists; eexists; repeat split; eauto.
    - rewrite FromList_cons in H.
      edestruct (G_get HG) as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto.

      edestruct IHxs as [vs1 [vs2 [Heqvs1 [Heqvs2 HVs]]]]; eauto.
      eapply Included_trans; eauto.
      apply Included_Union_r.

      rewrite Heqv1.
      rewrite Heqvs1.
      rewrite Heqv2.
      rewrite Heqvs2.
      exists (v1 :: vs1), (v2 :: vs2); repeat (split; auto).
  Qed.

  Lemma G_set {i Γ1 ρ1 Γ2 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall {x v1 v2},
      V i v1 v2 ->
      G i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
  Proof.
    intros.
    unfold G; intros.

    split.
    eapply wf_env_set; eauto.
    eapply G_wf_env_r; eauto.
    eapply V_wf_val_r; eauto.

    split.
    apply Included_Union_compat; auto.
    apply Included_refl.
    eapply G_subset_inv; eauto.

    intros.
    destruct (M.elt_eq x0 x); subst.
    - repeat rewrite M.gss.
      eexists; eexists; repeat split; eauto.
    - repeat (rewrite M.gso; auto).
      assert (x0 \in Γ1) by fcrush.
      eapply G_get; eauto.
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
    assert (HΓ : Γ2 \subset Γ1) by (eapply G_subset_inv; eauto).
    induction xs; simpl; intros.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      inv H0; inv H1.
      eapply G_subset; eauto.
      normalize_sets.
      rewrite Union_Empty_set_neut_l; eauto.
      apply Included_refl.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
      destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
      inv H; inv H0; inv H1.
      eapply G_subset with (Γ1 := (a |: (FromList xs :|: Γ1))) (Γ2 := (a |: (FromList xs :|: Γ2))); eauto.
      eapply G_set; eauto.
      normalize_sets.
      rewrite Union_assoc.
      apply Included_refl.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
  Qed.

  (* Compatibility Lemmas *)
  Lemma Vfun_V w e e' :
    trans_correct e e' ->
    (w \in Exposed) ->
    forall i f xs Γ1 Γ2 ρ1 ρ2,
      G i Γ1 ρ1 Γ2 ρ2 ->
      A0.occurs_free e \subset (FromList xs :|: (f |: Γ1)) ->
      A1.occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
      V i (A0.Vfun f ρ1 xs e) (Tag w (A1.Vfun f ρ2 xs e')).
  Proof.
    unfold trans_correct.
    intros [HS He] Hw i.

    induction i; simpl; intros; auto;
      assert (Hρ2 : wf_env ρ2) by (eapply G_wf_env_r; eauto);
      destruct (exposed_reflect w); try contradiction;
      repeat (split; auto); intros.

    apply (He (i - (i - j)) ρ3 ρ4); auto.
    eapply G_subset with (Γ1 := FromList xs :|: (f |: Γ1)) (Γ2 := FromList xs :|: (f |: Γ2)); eauto.
    eapply G_set_lists; eauto.
    eapply G_set; eauto.
    eapply G_mono; eauto; try lia.
    apply V_mono with i; try lia.
    eapply IHi with (Γ2 := Γ2); eauto.
    apply G_mono with (S i); eauto; lia.
  Qed.

  Lemma free_fun_compat e e' w f k k' xs :
    A1.occurs_free e' \subset A0.occurs_free e ->
    A1.occurs_free k' \subset A0.occurs_free k ->
    A1.occurs_free (A1.Efun f w xs e' k') \subset A0.occurs_free (A0.Efun f xs e k).
  Proof.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H1; auto.
  Qed.

  Lemma fun_compat w e e' k k' f xs :
    (w \in Exposed) ->
    trans_correct e e' ->
    trans_correct k k' ->
    trans_correct (A0.Efun f xs e k) (Efun f w xs e' k').
  Proof.
    unfold trans_correct, E, E'.
    intro Hw; intros.

    inv H.
    inv H0.
    split; intros.
    eapply free_fun_compat; eauto.

    inv H5.
    - exists 0, OOT; split; simpl; eauto.
    - inv H6.
      edestruct (H3 (i - 1) (M.set f (A0.Vfun f ρ1 xs e) ρ1) (M.set f (Tag w (A1.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + eapply G_subset with (Γ1 := (f |: (A0.occurs_free (A0.Efun f xs e k)))) (Γ2 := (f |: (A1.occurs_free (A1.Efun f w xs e' k')))); eauto.
        * eapply G_set; eauto.
          eapply G_mono; eauto; try lia.

          eapply Vfun_V with (Γ1 := (A0.occurs_free (A0.Efun f xs e k))) (Γ2 := (A1.occurs_free (A1.Efun f w xs e' k'))); eauto.
          -- unfold trans_correct.
             split; auto.
          -- eapply G_mono; eauto; try lia.
          -- eapply A0.free_fun_e_subset; eauto.
          -- eapply A1.free_fun_e_subset; eauto.
        * eapply A0.free_fun_k_subset; eauto.
      + exists (S j2), r2; split; auto.
        * constructor; auto.
          eapply bstep_fuel_exposed_inv; eauto.
        * apply R_mono with ((i - 1) - c); try lia; auto.
  Qed.

  Lemma free_letapp_compat w k k' f x xs :
    A1.occurs_free k' \subset A0.occurs_free k ->
    A1.occurs_free (A1.Eletapp x f w xs k') \subset A0.occurs_free (A0.Eletapp x f xs k).
  Proof.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H0; auto.
  Qed.

  (* Need [Exposed] to be a singleton set *)
  Lemma letapp_compat w k k' xs x f :
    (w \in Exposed) ->
    (forall w0, w0 \in Exposed -> w0 = w) ->
    trans_correct k k' ->
    trans_correct (A0.Eletapp x f xs k) (A1.Eletapp x f w xs k').
  Proof.
    unfold trans_correct, E, E'.
    intros Hw HEx; intros.
    destruct H.
    split; intros.
    eapply free_letapp_compat; eauto.

    inv H3.
    - exists 0, OOT; split; simpl; auto.
    - inv H4.
      + edestruct (G_get H1) as [fv1 [fv2 [Heqfv1 [Heqfv2 HVf]]]]; eauto.
        invc.
        destruct fv2.
        destruct i.
        fcrush.
        simpl in HVf.
        destruct HVf as [Hfv2 HV]; subst.
        destruct (exposed_reflect w); try contradiction.
        destruct (exposed_reflect w0); inv HV.
        assert (Heqw : w0 = w) by (eapply HEx; eauto); inv Heqw.
        destruct v0; try contradiction.
        destruct H4 as [Hlen HV]; subst.
        edestruct (G_get_list H1 xs) as [vs1 [vs2 [Heqvs1 [Heqvs2 HVvs]]]]; eauto.
        eapply A0.free_letapp_xs_subset; eauto.
        invc.

        destruct (set_lists_length3 (M.set v0 (Tag w (Vfun v0 t l e0)) t) l vs2) as [ρ4 Heqρ4].
        unfold wval in *.
        rewrite <- (Forall2_length _ _ _ HVvs).
        rewrite <- (set_lists_length_eq _ _ _ _ H12); auto.

        unfold E' in HV.
        edestruct (HV i vs1 vs2 ρ'' ρ4) with (j1 := c0) as [j2 [r2 [He0 HR]]]; eauto; try lia.
        * eapply V_exposed_Forall_r; eauto.
        * eapply V_mono_Forall; eauto; lia.
        * destruct r2; simpl in HR; try contradiction.
          edestruct (H0 (i - c0) (M.set x v ρ1) (M.set x w0 ρ2)) with (j1 := c') as [j3 [r3 [He1 HR']]]; eauto; try lia.
          eapply G_subset with (Γ1 := x |: (A0.occurs_free (A0.Eletapp x f xs k))) (Γ2 := x |: (A1.occurs_free (A1.Eletapp x f w xs k'))); eauto.
          eapply G_set; eauto.
          eapply G_mono; eauto; lia.
          -- eapply V_mono; eauto; try lia.
          -- eapply A0.free_letapp_k_subset; eauto.
          -- exists (S (j2 + j3)), r3; split; eauto.
             2 : { eapply R_mono; eauto; lia. }

             constructor; auto.
             eapply BStep_letapp_Res with (v := w0); eauto.
             destruct (exposed_reflect w); try contradiction; auto.

             intros.
             split; auto.
             eapply V_exposed_Forall_r; eauto.
             assert (Hr : exposed_res (A1.Res w0)) by (eapply bstep_fuel_exposed_inv; eauto); inv Hr; auto.

             eapply bstep_fuel_exposed_inv; eauto.
      + eexists; exists OOT; split; simpl; eauto.
  Qed.

  (* Linking Preservation *)
  Lemma preserves_linking f w x e1 e2 e1' e2' :
    (w \in Exposed) ->
    (forall w0, w0 \in Exposed -> w0 = w) ->
    trans_correct e1 e2 ->
    trans_correct e1' e2' ->
    trans_correct (A0.link f x e1 e1') (A1.link f w x e2 e2').
  Proof.
    unfold A0.link, A1.link.
    intros.
    eapply fun_compat; eauto.
    eapply letapp_compat; eauto.
  Qed.

End AnnotateTop.

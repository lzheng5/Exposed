From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF0 ANF Refl0 Refl Id.

Module A0 := ANF0.
Module A1 := ANF.

(* Web Annotation Erasure *)

(* Specification *)
Inductive trans (Γ : Ensemble var) : A1.exp -> A0.exp -> Prop :=
| Trans_ret :
  forall {x},
    (x \in Γ) ->
    trans Γ (A1.Eret x) (A0.Eret x)

| Trans_fun :
  forall {f w xs e k e' k'},
    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->
    trans Γ (A1.Efun f w xs e k) (A0.Efun f xs e' k')

| Trans_app :
  forall {f w xs},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans Γ (A1.Eapp f w xs) (A0.Eapp f xs)

| Trans_letapp :
  forall {x f w xs k k'},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (A1.Eletapp x f w xs k) (A0.Eletapp x f xs k')

| Trans_constr :
  forall {x w t xs k k'},
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (A1.Econstr x w t xs k) (A0.Econstr x t xs k')

| Trans_proj :
  forall {x y w k k' n},
    (y \in Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (A1.Eproj x w n y k) (A0.Eproj x n y k')

| Trans_case_nil :
  forall {x w},
    (x \in Γ) ->
    trans Γ (A1.Ecase x w []) (A0.Ecase x [])

| Trans_case_cons :
  forall {x w e e' t cl cl'},
    (x \in Γ) ->
    trans Γ e e' ->
    trans Γ (A1.Ecase x w cl) (A0.Ecase x cl') ->
    trans Γ (A1.Ecase x w ((t, e) :: cl)) (A0.Ecase x ((t, e') :: cl')).

Hint Constructors trans : core.

(* Cross-language Logical Relations *)
Definition R' (P : nat -> A1.wval -> A0.val -> Prop) (i : nat) (r1 : A1.res) (r2 : A0.res) :=
  match r1, r2 with
  | A1.OOT, A0.OOT => True
  | A1.Res v1, A0.Res v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> A1.wval -> A0.val -> Prop) (ex : bool) (i : nat) (ρ1 : A1.env) (e1 :A1.exp) (ρ2 : A0.env) (e2 : A0.exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    A1.bstep_fuel ex ρ1 e1 j1 r1 ->
    exists j2 r2,
      A0.bstep_fuel ρ2 e2 j2 r2 /\
      R' P (i - j1) r1 r2.

Fixpoint V (i : nat) (wv1 : A1.wval) (v2 : A0.val) {struct i} : Prop :=
  wf_val wv1 /\
  match wv1 with
  | A1.TAG _ w1 v1 =>
      match v1, v2 with
      | A1.Vconstr c1 vs1, A0.Vconstr c2 vs2 =>
          c1 = c2 /\
          match i with
          | 0 => length vs1 = length vs2
          | S i0 => Forall2 (V i0) vs1 vs2
          end

      | A1.Vfun f1 ρ1 xs1 e1, A0.Vfun f2 ρ2 xs2 e2 =>
          length xs1 = length xs2 /\
          match i with
          | 0 => True
          | S i0 =>
              forall j vs1 vs2 ρ3 ρ4,
                j <= i0 ->
                (w1 \in Exposed -> Forall exposed vs1) ->
                Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                set_lists xs1 vs1 (M.set f1 (Tag w1 (A1.Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                set_lists xs2 vs2 (M.set f2 (A0.Vfun f2 ρ2 xs2 e2) ρ2) = Some ρ4 ->
                E' V (exposedb w1) (i0 - (i0 - j)) ρ3 e1 ρ4 e2
          end

      | _, _ => False
      end
  end.

Notation R := (R' V).

Notation E := (E' V).

Lemma trans_exp_inv {Γ e e'} :
  trans Γ e e' ->
  (A0.occurs_free e') \subset (A1.occurs_free e).
Proof.
Admitted.

(* Lemmas about [wf_val], [wf_res], and [wf_env] *)
Lemma V_wf_val_l {i v1 v2}:
  V i v1 v2 ->
  wf_val v1.
Proof.
  intros HV.
  destruct i; simpl in *;
    destruct HV as [Hv1 _]; auto.
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

Lemma V_wf_res_l {i v1 v2}:
  V i v1 v2 ->
  wf_res (Res v1).
Proof.
  intros HV.
  constructor.
  eapply V_wf_val_l; eauto.
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

(* Environment Relation *)
Definition G i Γ1 ρ1 Γ2 ρ2 :=
  wf_env ρ1 /\
  forall x,
    (x \in Γ1) ->
    forall v1,
      M.get x ρ1 = Some v1 ->
      ((x \in Γ2) ->
       exists v2,
         M.get x ρ2 = Some v2 /\
         V i v1 v2).

Definition trans_correct Γ e1 e2 :=
  forall ex i ρ1 ρ2,
    G i Γ ρ1 (A0.occurs_free e2) ρ2 ->
    E ex i ρ1 e1 ρ2 e2.

(* Environment Lemmas *)
Lemma G_wf_env_l {i Γ1 ρ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  wf_env ρ1.
Proof.
  unfold G.
  intros H; destruct H; auto.
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
  destruct H as [Hr1 HG].
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
  unfold G.
  intros.

  inv H.
  split.
  eapply wf_env_set; eauto.
  eapply V_wf_val_l; eauto.

  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss in *.
    inv H3.
    eexists; split; eauto; intros.
  - rewrite M.gso in *; auto.
    inv H.
    inv H5; try contradiction.
    inv H4.
    inv H; try contradiction.
    edestruct H2 as [v1' [Heqv1' Hv2]]; eauto.
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
    split; intros.
    eapply G_wf_env_l; eauto.

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
  inv H; split; auto.
Qed.

(* Monotonicity Lemmas *)
Lemma V_mono_Forall_aux :
  forall i j (V : nat -> A1.wval -> A0.val -> Prop) vs1 vs2,
    (forall k : nat,
        k < S i ->
        forall (j : nat) v1 v2, V k v1 v2 -> j <= k -> V j v1 v2) ->
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

Lemma V_mono i :
  forall {j v1 v2},
    V i v1 v2 ->
    j <= i ->
    V j v1 v2.
Proof.
  induction i using lt_wf_rec; intros.
  destruct v1.
  destruct i; simpl in H0;
    destruct j; simpl; intros;
    destruct H0 as [Hv1 HV]; subst.
  - repeat (split; auto).
  - inv H1.
  - repeat (split; auto).
    destruct v; destruct v2; try contradiction.
    + destruct HV.
      split; auto.
    + destruct HV as [Hc HV]; subst.
      repeat split; auto.
      eapply Forall2_length; eauto.
  - repeat (split; auto).
    destruct v; destruct v2; try contradiction;
      destruct HV as [Hlen HV]; subst.
    + split; auto; intros.
      specialize (HV j0 vs1 vs2 ρ3 ρ4).
      rewrite normalize_step in *; try lia.
      apply HV; eauto; lia.
    + repeat split; auto.
      eapply V_mono_Forall_aux; eauto; lia.
Qed.

Lemma V_mono_Forall {vs1 vs2} i j :
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
  unfold E.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; eauto.
  apply R_mono with (i - j1); try lia; auto.
Qed.

Lemma G_mono {Γ1 Γ2 ρ1 ρ2} i j:
  G i Γ1 ρ1 Γ2 ρ2 ->
  j <= i ->
  G j Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G.
  intros.
  inv H.
  split; auto; intros.
  edestruct H2 as [v2 [Heqv2 HV]]; eauto.
  eexists; eexists; repeat split; eauto.
  apply V_mono with i; eauto.
Qed.

(* Compatibility Lemmas *)
Lemma ret_compat Γ x :
  (x \in Γ) ->
  trans_correct Γ (A1.Eret x) (A0.Eret x).
Proof.
  unfold trans_correct, G, E, E', R, R', Ensembles.Included, Ensembles.In, Dom_map.
  intros.
  inv H2.
  - exists 0, A0.OOT; split; auto.
  - inv H3.
    inv H0.
    edestruct H3 as [v2 [Heqv2 HV]]; eauto.
    exists 1, (A0.Res v2); split; auto.
    apply V_mono with i; try lia; auto.
Qed.

Lemma constr_compat Γ x w t xs k k' :
  (FromList xs \subset Γ) ->
  trans_correct (x |: Γ) k k' ->
  trans_correct Γ (A1.Econstr x w t xs k) (A0.Econstr x t xs k').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H3.
  - exists 0, A0.OOT; split; simpl; auto.
  - inv H4.
    destruct (G_get_list H1 xs vs) as [vs' [Heqvs' Hvs]]; auto.
    + eapply A0.free_constr_xs_subset; eauto.
    + assert (wf_val (Tag w (Vconstr t vs))).
      {
        apply wf_val_Vconstr; auto.
        eapply V_wf_val_Forall_l; eauto.
      }

      assert (length vs = length vs').
      {
        unfold wval in *.
        rewrite <- (get_list_length_eq _ _ _ H12).
        rewrite <- (get_list_length_eq _ _ _ Heqvs'); auto.
      }

      edestruct (H0 ex i (M.set x (Tag w (A1.Vconstr t vs)) ρ1) (M.set x (A0.Vconstr t vs') ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk' Rr]]]; eauto; try lia.
      * eapply G_subset with (Γ2 := (x |: (A0.occurs_free (A0.Econstr x t xs k')))).
        eapply G_set; eauto.
        -- destruct i; simpl; repeat (split; eauto).
           eapply V_mono_Forall; eauto; lia.
        -- apply Included_refl.
        -- apply A0.free_constr_k_subset.
      * exists (S j2), r2; split; eauto.
        apply R_mono with (i - c); try lia; auto.
Qed.

Lemma Vfun_V Γ1 f xs e e' :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  forall {i Γ2 ρ1 ρ2 w},
    wf_env ρ1 ->
    G i Γ1 ρ1 Γ2 ρ2 ->
    A0.occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
    V i (Tag w (A1.Vfun f ρ1 xs e)) (A0.Vfun f ρ2 xs e').
Proof.
  unfold trans_correct.
  intros He i.
  induction i; simpl; intros; auto;
    repeat (split; auto); intros.
  apply (He (exposedb w) (i - (i - j)) ρ3 ρ4); auto.
  - eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))).
    eapply G_set_lists; eauto.
    eapply G_set; eauto.
    + apply G_mono with (S i); eauto; lia.
    + apply V_mono with i; try lia.
      eapply IHi with (Γ2 := Γ2); eauto.
      apply G_mono with (S i); eauto; lia.
    + apply Included_refl.
    + auto.
Qed.

Lemma fun_compat Γ e e' k k' f w xs :
  trans_correct (FromList xs :|: (f |: Γ)) e e' ->
  trans_correct (f |: Γ) k k' ->
  trans_correct Γ (A1.Efun f w xs e k) (A0.Efun f xs e' k').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H3.
  - exists 0, A0.OOT; split; simpl; eauto.
  - inv H4.
    edestruct (H0 ex (i - 1) (M.set f (Tag w (A1.Vfun f ρ1 xs e)) ρ1) (M.set f (A0.Vfun f ρ2 xs e') ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_subset with (Γ2 := (f |: A0.occurs_free (A0.Efun f xs e' k'))).
      eapply G_set; eauto.
      apply G_mono with i; eauto; lia.
      * eapply Vfun_V; eauto.
        -- eapply G_wf_env_l; eauto.
        -- apply G_mono with i; eauto; lia.
        -- apply A0.free_fun_e_subset.
      * apply Included_refl.
      * apply A0.free_fun_k_subset.
    + exists (S j2), r2; split; auto.
      apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma app_compat Γ xs f w :
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  trans_correct Γ (A1.Eapp f w xs) (A0.Eapp f xs).
Proof.
  unfold trans_correct, G, E, E'.
  intros.
  inv H3.
  - exists 0, A0.OOT; split; simpl; auto.
  - inv H4.
    edestruct (G_get H1 f) as [fv2 [Heqfv2 HV]]; eauto.
    destruct i.
    inv H2.
    destruct fv2; simpl in HV;
      destruct HV as [Hv1 HV];
      try contradiction.
    destruct HV as [Hlen HV].

    edestruct (G_get_list H1 xs vs) as [vs2 [Heqvs2 Vvs]]; eauto.
    eapply A0.free_app_xs_subset; eauto.

    destruct (set_lists_length3 (M.set v (A0.Vfun v t l e0) t) l vs2) as [ρ4 Heqρ4].
    unfold wval in *.
    rewrite <- (Forall2_length _ _ _ Vvs).
    rewrite <- (set_lists_length_eq _ _ _ _ H10); auto.

    assert (HE : E (exposedb w) (i - (i - i)) ρ'' e ρ4 e0).
    {
      eapply (HV i vs vs2); eauto.
      - intros.
        destruct H14; auto.
      - apply V_mono_Forall with (S i); auto; lia.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E in HE.
    destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
    exists (S j2), r2; split; eauto.
Qed.

Lemma proj_compat Γ x w i y e e' :
  (y \in Γ) ->
  trans_correct (x |: Γ) e e' ->
  trans_correct Γ (A1.Eproj x w i y e) (A0.Eproj x i y e').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H3.
  - exists 0, A0.OOT; split; simpl; auto.
  - inv H4.
    edestruct (G_get H1 y) as [v2 [Heqv2 HV]]; eauto.
    destruct i0.
    inv H2.
    destruct v2;
      simpl in HV;
      destruct HV as [Hv1 HV]; subst; try contradiction.
    rename l into vs'.
    rename c0 into t'.
    destruct HV as [Heqt HFvs]; subst.
    destruct (Forall2_nth_error H13 HFvs) as [v' [Heqv' HFv]].
    edestruct (H0 ex i0 (M.set x v ρ1) (M.set x v' ρ2)) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
    + eapply G_subset with (Γ2 := (x |: (A0.occurs_free (A0.Eproj x i y e')))).
      eapply G_set; eauto.
      eapply G_mono with (S i0); eauto; try lia.
      apply Included_refl.
      apply A0.free_proj_k_subset.
    + exists (S j2), r2; split; eauto.
Qed.

Lemma case_nil_compat Γ x w:
  (x \in Γ) ->
  trans_correct Γ (A1.Ecase x w []) (A0.Ecase x []).
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H2.
  - exists 0, A0.OOT; split; simpl; auto.
  - inv H3.
    inv H10.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {Γ e e'}:
  trans Γ e e' -> trans_correct Γ e e'.
Proof.
  intros H.
  induction H.
  - eapply ret_compat; auto.
  - eapply fun_compat; eauto.
  - eapply app_compat; eauto.
  - admit.
  - eapply constr_compat; eauto.
  - eapply proj_compat; eauto.
  - eapply case_nil_compat; eauto.
  - admit.
Admitted.

(* Top Level *)
Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  wf_env ρ1 /\
  Γ2 \subset Γ1 /\
  forall x,
    (x \in Γ1) ->
    exists v1 v2,
      M.get x ρ1 = Some v1 /\
      M.get x ρ2 = Some v2 /\
      exposed v1 /\
      V i v1 v2.

Lemma G_top_G : forall {i Γ1 ρ1 Γ2 ρ2},
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    G i Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G_top, G.
  intros.
  destruct H as [HΓ [Hρ HG]].
  unfold Ensembles.Included, Ensembles.In, Dom_map in *.
  split; auto; intros.
  edestruct HG as [v1' [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto.
  rewrite Heqv1 in H0; inv H0; eauto.
Qed.

Definition trans_correct_top etop etop' :=
  A0.occurs_free etop' \subset A1.occurs_free etop /\
  forall i ρ1 ρ2,
    G_top i (A1.occurs_free etop) ρ1 (A0.occurs_free etop') ρ2 ->
    E true i ρ1 etop ρ2 etop'.

Theorem top etop etop':
  trans (A1.occurs_free etop) etop etop' ->
  trans_correct_top etop etop'.
Proof.
  unfold trans_correct_top.
  intros H.
  specialize (fundamental_property H);
    unfold trans_correct; intros.
  split; intros.
  - eapply trans_exp_inv; eauto.
  - eapply H0; eauto.
    eapply G_top_G; eauto.
Qed.

(* Cross-language Compositionality *)

(* Adequacy *)
Theorem adequacy e1 e2:
  trans_correct_top e1 e2 ->
  forall ρ1 ρ2,
    wf_env ρ1 ->
    (forall k, G_top k (A1.occurs_free e1) ρ1 (A0.occurs_free e2) ρ2) ->
    forall j1 r1,
      A1.bstep_fuel true ρ1 e1 j1 r1 ->
      exists j2 r2,
        A0.bstep_fuel ρ2 e2 j2 r2 /\
        (forall k, R k r1 r2).
Proof.
  intros.
  unfold trans_correct_top in H.
  destruct H as [HS HT].

  assert (HE : E true j1 ρ1 e1 ρ2 e2) by (eapply (HT j1); eauto).
  edestruct (HE j1) as [j2 [r2 [Hstep2 HR]]]; eauto.
  eexists; eexists; split; eauto.

  intros.
  assert (HE' : E true (j1 + k) ρ1 e1 ρ2 e2) by (eapply HT; eauto).
  edestruct (HE' j1) as [j2' [r2' [Hstep2' HR']]]; eauto; try lia.

  assert (Hm : j1 + k - j1 = k) by lia. (* TODO: REFACTOR *)
  rewrite Hm in *; clear Hm.

  assert (Hm : j1 - j1 = 0) by lia.
  rewrite Hm in *; clear Hm.

  destruct r2; destruct r2'; destruct r1;
    simpl in *; auto; try contradiction.

  edestruct (A0.bstep_fuel_deterministic v v0 Hstep2 Hstep2'); subst; eauto.
Qed.

(* Behavioral Refinement *)
Inductive val_ref : A1.wval -> A0.val -> Prop :=
| Ref_Tag :
  forall w v1 v2,
    val_ref' v1 v2 ->
    val_ref (Tag w v1) v2

with val_ref' : A1.val -> A0.val -> Prop :=
| Ref_Vfun :
  forall f1 ρ1 xs1 e1 f2 ρ2 xs2 e2,
    val_ref' (A1.Vfun f1 ρ1 xs1 e1) (A0.Vfun f2 ρ2 xs2 e2)

| Ref_Vconstr_nil :
  forall c,
    val_ref' (A1.Vconstr c []) (A0.Vconstr c [])

| Ref_Vconstr_cons :
  forall c v1 v2 vs1 vs2,
    val_ref v1 v2 ->
    val_ref' (A1.Vconstr c vs1) (A0.Vconstr c vs2) ->
    val_ref' (A1.Vconstr c (v1 :: vs1)) (A0.Vconstr c (v2 :: vs2)).

Hint Constructors val_ref : core.
Hint Constructors val_ref' : core.

Scheme val_ref_mut := Induction for val_ref Sort Prop
with val_ref'_mut := Induction for val_ref' Sort Prop.

Lemma val_ref_Vconstr c w vs1 vs2 :
  Forall2 val_ref vs1 vs2 ->
  val_ref (Tag w (A1.Vconstr c vs1)) (A0.Vconstr c vs2).
Proof.
  intros.
  induction H; simpl; auto.
  constructor.
  econstructor; eauto.
  inv IHForall2; auto.
Qed.

Lemma V_val_ref {v1 v2} :
  wf_val v1 ->
  (forall i, V i v1 v2) ->
  val_ref v1 v2.
Proof.
  intros H.
  revert v2.
  induction H using wf_val_mut with (P0 := fun v1 wf =>
                                             forall (v2 : A0.val) w,
                                               (forall i, (V i (Tag w v1) v2)) ->
                                               match v1, v2 with
                                               | A1.Vfun _ _ _ _, A0.Vfun _ _ _ _ => True
                                               | A1.Vconstr c1 vs1, A0.Vconstr c2 vs2  =>
                                                   c1 = c2 /\ Forall2 val_ref vs1 vs2
                                               | _ , _ => False
                                               end)
                                    (P1 := fun ρ wf => True);
    intros; simpl in *; eauto.
  - specialize (IHwf_val _ _ H).
    destruct v; destruct v2; try contradiction; subst; auto.
    destruct IHwf_val as [Hc HV]; subst; auto.
    eapply val_ref_Vconstr; eauto.
  - destruct v2; auto.
    destruct (H 0); subst; auto; contradiction.
  - destruct v2.
    + destruct (H 0); subst; auto; contradiction.
    + destruct (H 0) as [_ [Hc Hlen]]; subst; simpl in *.
      symmetry in Hlen.
      apply length_zero_iff_nil in Hlen; subst.
      split; auto.
  - destruct v2.
    + destruct (H0 0); subst; auto; contradiction.
    + destruct (H0 1) as [Hv1 [Hc HV']]; subst;
        split; auto.
      inv HV'.
      clear H3 H5.
      assert (HV' : forall i, V i v y /\ V i (Tag w0 (A1.Vconstr c0 vs)) (A0.Vconstr c0 l')).
      {
        intros.
        specialize (H0 (S i)).
        destruct i; simpl in *;
          destruct H0 as [_ [_ HFV]];
          inv HFV.
        - inv Hv1.
          inv H4.
          inv H8; inv H5;
            repeat (split; auto).
          + intros.
            apply H2 in H0.
            inv H0.
            inv H12; auto.
          + simpl.
            f_equal.
            eapply Forall2_length; eauto.
        - inv Hv1.
          inv H4.
          inv H8; inv H5;
            repeat (split; auto).
          + intros.
            apply H2 in H0.
            inv H0.
            inv H12; auto.
          + constructor; auto.
            * eapply V_mono with (S i); eauto.
            * eapply V_mono_Forall with (S i); eauto.
      }

      assert (HV0 : forall i, V i v y) by (intros; destruct (HV' i); auto).
      assert (HV1 : forall i, V i (Tag w0 (A1.Vconstr c0 vs)) (A0.Vconstr c0 l')) by (intros; destruct (HV' i); auto).

      constructor; auto.
      specialize (IHwf_val0 _ _ HV1).
      simpl in IHwf_val0.
      destruct IHwf_val0 as [Hc HF]; auto.
Qed.

Lemma R_res_val_ref {v1 v2} :
  wf_val v1 ->
  (forall i, R i (A1.Res v1) (A0.Res v2)) ->
  val_ref v1 v2.
Proof.
  intros; eapply V_val_ref; eauto.
Qed.

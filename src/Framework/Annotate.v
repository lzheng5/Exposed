From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF0 ANF Refl0 Refl Id.

Module A0 := ANF0.
Module A1 := ANF.

(* Trivial Web Annotation With A Single Exposed Web Id *)
Parameter w0 : web.
Axiom w0_exposed : w0 \in Exposed.
Axiom Exposed_Singleton : forall w, w \in Exposed -> w = w0.

(* Specification *)
Inductive trans (Γ : Ensemble var) : A0.exp -> A1.exp -> Prop :=
| Trans_ret :
  forall {x},
    (x \in Γ) ->
    trans Γ (A0.Eret x) (A1.Eret x)

| Trans_fun :
  forall {f xs e k e' k'},
    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->
    trans Γ (A0.Efun f xs e k) (A1.Efun f w0 xs e' k')

| Trans_app :
  forall {f xs},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans Γ (A0.Eapp f xs) (A1.Eapp f w0 xs)

| Trans_letapp :
  forall {x f xs k k'},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w0 xs k')

| Trans_constr :
  forall {x t xs k k'},
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (A0.Econstr x t xs k) (A1.Econstr x w0 t xs k')

| Trans_proj :
  forall {x y k k' n},
    (y \in Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (A0.Eproj x n y k) (A1.Eproj x w0 n y k')

| Trans_case_nil :
  forall {x},
    (x \in Γ) ->
    trans Γ (A0.Ecase x []) (A1.Ecase x w0 [])

| Trans_case_cons :
  forall {x e e' t cl cl'},
    (x \in Γ) ->
    trans Γ e e' ->
    trans Γ (A0.Ecase x cl) (A1.Ecase x w0 cl') ->
    trans Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x w0 ((t, e') :: cl')).

Hint Constructors trans : core.

(* Cross-language Logical Relations *)
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

Fixpoint V (i : nat) (v1 : A0.val) (wv2 : A1.wval) {struct i} : Prop :=
  wf_val wv2 /\
  exposed wv2 /\ (* every value is exposed *)
  match wv2 with
  | A1.TAG _ w2 v2 =>
      match v1, v2 with
      | A0.Vconstr c1 vs1, A1.Vconstr c2 vs2 =>
          c1 = c2 /\
          match i with
          | 0 => length vs1 = length vs2
          | S i0 => Forall2 (V i0) vs1 vs2
          end

      | A0.Vfun f1 ρ1 xs1 e1, A1.Vfun f2 ρ2 xs2 e2 =>
          length xs1 = length xs2 /\
          match i with
          | 0 => True
          | S i0 =>
              forall j vs1 vs2 ρ3 ρ4,
                j <= i0 ->
                (w2 \in Exposed -> Forall exposed vs2) ->
                Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                set_lists xs1 vs1 (M.set f1 (A0.Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
                set_lists xs2 vs2 (M.set f2 (Tag w2 (A1.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                E' V (exposedb w2) (i0 - (i0 - j)) ρ3 e1 ρ4 e2
          end

      | _, _ => False
      end
  end.

Notation R := (R' V).

Notation E := (E' V).

Lemma trans_exp_inv {Γ e e'} :
  trans Γ e e' ->
  (A1.occurs_free e') \subset (A0.occurs_free e).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros H.
  induction H; simpl; intros; auto.
  - inv H0; auto.
  - inv H1; auto.
  - inv H1; auto.
  - inv H2; auto.
  - inv H1; auto.
  - inv H1; auto.
  - inv H0; auto.
  - inv H2; auto.
Qed.

Lemma trans_exp_weaken {Γ Γ' e e'} :
  trans Γ e e' ->
  Γ \subset Γ' ->
  trans Γ' e e'.
Proof.
  intros H.
  revert Γ'.
  induction H; simpl; intros; auto.
  - constructor.
    + eapply IHtrans1; eauto.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
    + eapply IHtrans2; eauto.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
  - constructor; auto.
    eapply Included_trans; eauto.
  - constructor; auto.
    + eapply Included_trans; eauto.
    + eapply IHtrans; eauto.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
  - constructor.
    + eapply Included_trans; eauto.
    + eapply IHtrans; eauto.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
  - constructor; auto.
    eapply IHtrans; eauto.
    eapply Included_Union_compat; eauto.
    apply Included_refl.
Qed.

Theorem trans_complete :
  forall e,
   exists e',
     Annotate.trans (A0.occurs_free e) e e'.
Proof.
  intros e.
  induction e using A0.exp_ind'.
  - eexists; eauto.
  - exists (A1.Eapp x w0 xs).
    constructor; auto.
    eapply A0.free_app_xs_subset; eauto.
  - inv IHe1; inv IHe2.
    exists (A1.Efun f w0 xs x x0).
    constructor; auto.
    eapply trans_exp_weaken; eauto.
    eapply A0.free_fun_e_subset; eauto.
    eapply trans_exp_weaken; eauto.
    eapply A0.free_fun_k_subset; eauto.
  - inv IHe.
    exists (A1.Eletapp x f w0 xs x0); constructor; auto.
    eapply A0.free_letapp_xs_subset; eauto.
    eapply trans_exp_weaken; eauto.
    eapply A0.free_letapp_k_subset; eauto.
  - inv IHe.
    exists (A1.Econstr x w0 c xs x0); constructor; auto.
    eapply A0.free_constr_xs_subset; eauto.
    eapply trans_exp_weaken; eauto.
    eapply A0.free_constr_k_subset; eauto.
  - exists (A1.Ecase x w0 []); auto.
  - inv IHe; inv IHe0.
    inv H0.
    + exists (A1.Ecase x w0 ([(c, x0)])); constructor; auto.
      eapply trans_exp_weaken; eauto.
      eapply A0.free_case_hd_subset; eauto.
    + exists (A1.Ecase x w0 ((c, x0) :: (t, e') :: cl')); constructor; auto.
      eapply trans_exp_weaken; eauto.
      eapply A0.free_case_hd_subset; eauto.

      eapply trans_exp_weaken; eauto.
      eapply A0.free_case_tl_subset; eauto.
  - inv IHe.
    exists (A1.Eproj x w0 n v0 x0); constructor; auto.
    eapply trans_exp_weaken; eauto.
    eapply A0.free_proj_k_subset; eauto.
Qed.

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
Lemma R_res_inv_l v1 r2 :
  (forall k, R k (A0.Res v1) r2) ->
  exists v2, r2 = A1.Res v2 /\ (forall k, V k v1 v2).
Proof.
  intros.
  destruct r2.
  - specialize (H 0); simpl in *; contradiction.
  - eexists; split; eauto.
Qed.

(* Exposed Lemmas *)
Lemma V_exposed_r {i v1 v2}:
  V i v1 v2 ->
  exposed v2.
Proof.
  intros HV.
  destruct i; simpl in *;
    destruct HV as [Hv2 [Hex _]]; auto.
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

Lemma V_exposed_res_r {i v1 v2}:
  V i v1 v2 ->
  exposed_res (Res v2).
Proof.
  intros HV.
  constructor.
  eapply V_exposed_r; eauto.
Qed.

Lemma R_exposed_res_r {i r1 r2} :
  R i r1 r2 ->
  exposed_res r2.
Proof.
  unfold R.
  intros.
  destruct r1; destruct r2; try contradiction; auto.
  constructor.
  eapply V_exposed_r; eauto.
Qed.

(* Environment Relation *)
Definition G i Γ1 ρ1 Γ2 ρ2 :=
  wf_env ρ2 /\
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
    G i Γ ρ1 (A1.occurs_free e2) ρ2 ->
    E ex i ρ1 e1 ρ2 e2.

(* Environment Lemmas *)
Lemma G_wf_env_r {i Γ1 ρ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  wf_env ρ2.
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
  eapply V_wf_val_r; eauto.

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
    eapply G_wf_env_r; eauto.

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
  inv H; split; auto.
Qed.

(* Monotonicity Lemmas *)
Lemma V_mono_Forall_aux :
  forall i j (V : nat -> A0.val -> A1.wval -> Prop) vs1 vs2,
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
  destruct v2.
  destruct i; simpl in H0;
    destruct j; simpl; intros;
    destruct H0 as [Hv1 [Hex HV]]; subst.
  - repeat (split; auto).
  - inv H1.
  - repeat (split; auto).
    destruct v1; destruct v; try contradiction.
    + destruct HV.
      split; auto.
    + destruct HV as [Hc HV]; subst.
      repeat split; auto.
      eapply Forall2_length; eauto.
  - repeat (split; auto).
    destruct v1; destruct v; try contradiction;
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
  trans_correct Γ (A0.Eret x) (A1.Eret x).
Proof.
  unfold trans_correct, G, E, E', R, R', Ensembles.Included, Ensembles.In, Dom_map.
  intros.
  inv H2.
  - exists 0, A1.OOT; split; auto.
  - inv H3.
    edestruct (G_get H0) as [v2 [Heqv2 HV]]; eauto.
    exists 1, (A1.Res v2); split; auto.
    + constructor.
      * constructor; auto.
      * destruct ex; auto.
        eapply V_exposed_res_r; eauto.
    + apply V_mono with i; try lia; auto.
Qed.

Lemma constr_compat Γ x t xs k k' :
  (FromList xs \subset Γ) ->
  trans_correct (x |: Γ) k k' ->
  trans_correct Γ (A0.Econstr x t xs k) (A1.Econstr x w0 t xs k').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H3.
  - exists 0, A1.OOT; split; simpl; auto.
  - inv H4.
    destruct (G_get_list H1 xs vs) as [vs' [Heqvs' Hvs]]; auto.
    + eapply A1.free_constr_xs_subset; eauto.
    + assert (wf_val (Tag w0 (A1.Vconstr t vs'))).
      {
        apply wf_val_Vconstr; auto.
        eapply V_wf_val_Forall_r; eauto.
        intros.
        eapply V_exposed_Forall_r; eauto.
      }

      assert (exposed (Tag w0 (A1.Vconstr t vs'))).
      {
        constructor.
        apply w0_exposed.
        eapply V_exposed_Forall_r; eauto.
      }

      assert (length vs = length vs').
      {
        unfold wval in *.
        rewrite <- (get_list_length_eq _ _ _ H10).
        rewrite <- (get_list_length_eq _ _ _ Heqvs'); auto.
      }

      edestruct (H0 ex i (M.set x (A0.Vconstr t vs) ρ1) (M.set x (Tag w0 (A1.Vconstr t vs')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk' Rr]]]; eauto; try lia.
      * eapply G_subset with (Γ2 := (x |: (A1.occurs_free (A1.Econstr x w0 t xs k')))).
        eapply G_set; eauto.
        -- destruct i; simpl; repeat (split; eauto).
           eapply V_mono_Forall; eauto; lia.
        -- apply Included_refl.
        -- apply A1.free_constr_k_subset.
      * exists (S j2), r2; split; eauto.
        -- econstructor.
           econstructor; eauto.
           intros.
           eapply V_exposed_Forall_r; eauto.
           destruct ex; auto.
           eapply R_exposed_res_r; eauto.
        -- apply R_mono with (i - c); try lia; auto.
Qed.

Lemma Vfun_V Γ1 f xs e e' :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  forall {i Γ2 ρ1 ρ2},
    wf_env ρ2 ->
    G i Γ1 ρ1 Γ2 ρ2 ->
    A1.occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
    V i (A0.Vfun f ρ1 xs e) (Tag w0 (A1.Vfun f ρ2 xs e')).
Proof.
  unfold trans_correct.
  intros He i.
  induction i; simpl; intros; auto;
    repeat (split; auto); intros;
    try (constructor; apply w0_exposed).

  apply (He (exposedb w0) (i - (i - j)) ρ3 ρ4); auto.
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

Lemma fun_compat Γ e e' k k' f xs :
  trans_correct (FromList xs :|: (f |: Γ)) e e' ->
  trans_correct (f |: Γ) k k' ->
  trans_correct Γ (A0.Efun f xs e k) (A1.Efun f w0 xs e' k').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H3.
  - exists 0, A1.OOT; split; simpl; eauto.
  - inv H4.
    edestruct (H0 ex (i - 1) (M.set f (A0.Vfun f ρ1 xs e) ρ1) (M.set f (Tag w0 (A1.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_subset with (Γ2 := (f |: A1.occurs_free (A1.Efun f w0 xs e' k'))).
      eapply G_set; eauto.
      apply G_mono with i; eauto; lia.
      * eapply Vfun_V; eauto.
        -- eapply G_wf_env_r; eauto.
        -- apply G_mono with i; eauto; lia.
        -- apply A1.free_fun_e_subset.
      * apply Included_refl.
      * apply A1.free_fun_k_subset.
    + exists (S j2), r2; split; auto.
      constructor.
      econstructor; eauto.
      destruct ex; auto.
      eapply R_exposed_res_r; eauto.

      apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma app_compat Γ xs f :
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  trans_correct Γ (A0.Eapp f xs) (A1.Eapp f w0 xs).
Proof.
  unfold trans_correct, G, E, E'.
  intros.
  inv H3.
  - exists 0, A1.OOT; split; simpl; auto.
  - inv H4.
    edestruct (G_get H1 f) as [fv2 [Heqfv2 HV]]; eauto.
    destruct i.
    inv H2.
    destruct fv2; simpl in HV;
      destruct HV as [Hv1 [Hex HV]];
      destruct v; try contradiction.
    destruct HV as [Hlen HV].

    assert (Hw : w = w0).
    {
      inv Hex.
      apply Exposed_Singleton; eauto.
    }
    subst.

    edestruct (G_get_list H1 xs vs) as [vs2 [Heqvs2 Vvs]]; eauto.
    eapply A1.free_app_xs_subset; eauto.

    destruct (set_lists_length3 (M.set v (Tag w0 (A1.Vfun v t l e0)) t) l vs2) as [ρ4 Heqρ4].
    unfold wval in *.
    rewrite <- (Forall2_length _ _ _ Vvs).
    rewrite <- (set_lists_length_eq _ _ _ _ H8); auto.

    assert (Forall A1.exposed vs2) by (eapply V_exposed_Forall_r; eauto).
    assert (HE : E (exposedb w0) (i - (i - i)) ρ'' e ρ4 e0).
    {
      eapply (HV i vs vs2); eauto.
      apply V_mono_Forall with (S i); auto; lia.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E in HE.
    destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.

    assert (A1.exposed_res r2) by (eapply R_exposed_res_r; eauto).

    exists (S j2), r2; split; eauto.
    constructor; auto.
    econstructor; eauto.
    destruct ex; auto.
Qed.

Lemma proj_compat Γ x i y e e' :
  (y \in Γ) ->
  trans_correct (x |: Γ) e e' ->
  trans_correct Γ (A0.Eproj x i y e) (A1.Eproj x w0 i y e').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H3.
  - exists 0, A1.OOT; split; simpl; auto.
  - inv H4.
    edestruct (G_get H1 y) as [v2 [Heqv2 HV]]; eauto.
    destruct i0.
    inv H2.
    destruct v2;
      simpl in HV;
      destruct HV as [Hv1 [Hex HV]]; subst;
      destruct v0; try contradiction.
    rename l into vs'.
    rename c0 into t'.
    destruct HV as [Heqt HFvs]; subst.
    destruct (Forall2_nth_error H11 HFvs) as [v' [Heqv' HFv]].
    edestruct (H0 ex i0 (M.set x v ρ1) (M.set x v' ρ2)) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
    + eapply G_subset with (Γ2 := (x |: (A1.occurs_free (A1.Eproj x w0 i y e')))).
      eapply G_set; eauto.
      eapply G_mono with (S i0); eauto; try lia.
      apply Included_refl.
      apply A1.free_proj_k_subset.
    + assert (Hw : w = w0).
      {
        inv Hex.
        apply Exposed_Singleton; eauto.
      }
      subst.

      exists (S j2), r2; split; eauto.
      constructor.
      econstructor; eauto.
      destruct ex; auto.
      eapply R_exposed_res_r; eauto.
Qed.

Lemma case_nil_compat Γ x:
  (x \in Γ) ->
  trans_correct Γ (A0.Ecase x []) (A1.Ecase x w0 []).
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H2.
  - exists 0, A1.OOT; split; simpl; auto.
  - inv H3.
    inv H6.
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
  wf_env ρ2 /\
  Γ2 \subset Γ1 /\
  forall x,
    (x \in Γ1) ->
    exists v1 v2,
      M.get x ρ1 = Some v1 /\
      M.get x ρ2 = Some v2 /\
      exposed v2 /\
      V i v1 v2.

Lemma G_top_wf_env_r i Γ1 ρ1 Γ2 ρ2 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  wf_env ρ2.
Proof.
  unfold G_top.
  intros; tauto.
Qed.

Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  Γ3 \subset Γ1 ->
  Γ4 \subset Γ3 ->
  G_top i Γ3 ρ1 Γ4 ρ2.
Proof.
  unfold G_top.
  intros.
  destruct H as [Hr [Hs HG]].
  repeat (split; auto).
Qed.

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
  A1.occurs_free etop' \subset A0.occurs_free etop /\
  forall i ρ1 ρ2,
    G_top i (A0.occurs_free etop) ρ1 (A1.occurs_free etop') ρ2 ->
    E true i ρ1 etop ρ2 etop'.

Lemma trans_correct_top_subset e1 e2 :
  trans_correct_top e1 e2 ->
  A1.occurs_free e2 \subset A0.occurs_free e1.
Proof.
  unfold Annotate.trans_correct_top.
  intros.
  inv H; auto.
Qed.

Theorem top etop etop':
  trans (A0.occurs_free etop) etop etop' ->
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
    wf_env ρ2 ->
    (forall k, G_top k (A0.occurs_free e1) ρ1 (A1.occurs_free e2) ρ2) ->
    forall j1 r1,
      A0.bstep_fuel ρ1 e1 j1 r1 ->
      exists j2 r2,
        A1.bstep_fuel true ρ2 e2 j2 r2 /\
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

  edestruct (A1.bstep_fuel_deterministic w w1 Hstep2 Hstep2'); subst; eauto.
Qed.

(* Behavioral Refinement *)
Inductive val_ref : A0.val -> A1.wval -> Prop :=
| Ref_Vfun :
  forall f1 ρ1 xs1 e1 f2 ρ2 xs2 e2,
    val_ref (A0.Vfun f1 ρ1 xs1 e1) (Tag w0 (A1.Vfun f2 ρ2 xs2 e2))

| Ref_Vconstr_nil :
  forall c,
    val_ref (A0.Vconstr c []) (Tag w0 (A1.Vconstr c []))

| Ref_Vconstr_cons :
  forall c v1 v2 vs1 vs2,
    val_ref v1 v2 ->
    val_ref (A0.Vconstr c vs1) (Tag w0 (A1.Vconstr c vs2)) ->
    val_ref (A0.Vconstr c (v1 :: vs1)) (Tag w0 (A1.Vconstr c (v2 :: vs2))).

Hint Constructors val_ref : core.

Lemma val_ref_Vconstr c vs1 vs2 :
  Forall2 val_ref vs1 vs2 ->
  val_ref (A0.Vconstr c vs1) (Tag w0 (A1.Vconstr c vs2)).
Proof.
  intros.
  induction H; simpl; auto.
Qed.

Theorem V_val_ref {v1 v2} :
  (forall i, V i v1 v2) ->
  val_ref v1 v2.
Proof.
  revert v2.
  induction v1 using val_ind'; intros; simpl.
  - specialize (H 0).
    destruct v2.
    destruct H as [Hw [Hex HV]].
    destruct v; try contradiction.
    destruct HV as [Hc Hlen]; subst.

    symmetry in Hlen.
    apply length_zero_iff_nil in Hlen; subst; auto.
    inv Hex.
    apply Exposed_Singleton in H1; subst; auto.
  - destruct v2.
    pose proof (H 0) as H0; simpl in *.
    destruct H0 as [Hw [Hex HV]].
    destruct v; try contradiction.
    destruct HV as [Hc Hlen]; subst.

    destruct l0; simpl in *; inv Hlen.
    inv Hex.
    apply Exposed_Singleton in H3; subst.

    assert (HV' : forall i, V i v1 t /\ V i (A0.Vconstr c l) (Tag w0 (A1.Vconstr c l0))).
    {
      intros.
      specialize (H (S i)); simpl in *.
      destruct H as [_ [He [Hc HFV]]]; subst.
      inv HFV.
      split; auto.

      assert (He' : exposed (Tag w0 (A1.Vconstr c l0))) by (inv He; inv H5; auto).

      assert (Hw' : wf_val (Tag w0 (A1.Vconstr c l0))).
      {
        constructor; intros; auto.
        inv Hw.
        inv H4; auto.
      }

      destruct i; simpl in *;
        repeat (split; auto);
        try (eapply V_mono_Forall with (S i); eauto).
    }

    assert (HV0 : forall i, V i v1 t) by (intros; destruct (HV' i); auto).
    assert (HV1 : forall i, V i (A0.Vconstr c l) (Tag w0 (A1.Vconstr c l0))) by (intros; destruct (HV' i); auto).

    auto.
  - specialize (H 0); simpl in *.
    destruct H as [Hw [He HV]].
    destruct v2; try contradiction; auto.
    destruct v; try contradiction.
    inv He.
    apply Exposed_Singleton in H0; subst; auto.
Qed.

Corollary R_res_val_ref {v1 v2} :
  (forall i, R i (A0.Res v1) (A1.Res v2)) ->
  val_ref v1 v2.
Proof.
  intros; eapply V_val_ref; eauto.
Qed.

(* Linking Compat Lemmas *)

(* [trans_correct] is stronger than [trans_correct_top] due to [G_top] *)
Lemma trans_correct_trans_correct_top e1 e2 :
  A1.occurs_free e2 \subset A0.occurs_free e1 ->
  trans_correct (A0.occurs_free e1) e1 e2 ->
  trans_correct_top e1 e2.
Proof.
  unfold trans_correct_top, trans_correct.
  intros.
  split; auto; intros.
  eapply H0; eauto.
  eapply G_top_G; eauto.
Qed.

(* Top-level Environment Lemmas *)
Lemma G_top_get_list {i Γ1 ρ1 Γ2 ρ2} :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  forall xs,
    (FromList xs) \subset Γ1 ->
    exists vs1 vs2,
      get_list xs ρ1 = Some vs1 /\
      get_list xs ρ2 = Some vs2 /\
      Forall2 (V i) vs1 vs2.
Proof.
  unfold G_top.
  intros HG xs.
  destruct HG as [Hr2 [HS HG]].
  induction xs; simpl; intros.
  - eexists; eexists; repeat split; eauto.
  - rewrite FromList_cons in H.
    edestruct IHxs as [vs1 [vs2 [Heqvs1 [Heqvs2 HVs]]]].
    eapply Included_trans; eauto.
    apply Included_Union_r.

    destruct (HG a) as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]].
    unfold Ensembles.Included, Ensembles.In, FromList in *.
    eapply H; eauto.
    apply Union_introl; auto.

    rewrite Heqv1.
    rewrite Heqvs1.
    rewrite Heqv2.
    rewrite Heqvs2.
    exists (v1 :: vs1), (v2 :: vs2); split; auto.
Qed.

Lemma G_top_set {i Γ1 ρ1 Γ2 ρ2}:
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  forall {x v1 v2},
    wf_val v2 ->
    V i v1 v2 ->
    G_top i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
Proof.
  unfold G_top.
  intros.
  destruct H as [Hr2 [HS HG]].
  split.
  eapply wf_env_set; eauto.

  split.
  apply Included_Union_compat; auto.
  apply Included_refl.

  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss.
    eexists; eexists; repeat split; eauto.
    eapply V_exposed_r; eauto.
  - repeat (rewrite M.gso; auto).
    inv H.
    inv H2; contradiction.
    eapply HG; eauto.
Qed.

Lemma G_top_set_lists {i Γ1 ρ1 Γ2 ρ2}:
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 (V i) vs1 vs2 ->
    Forall exposed vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    G_top i (FromList xs :|: Γ1) ρ3 (FromList xs :|: Γ2) ρ4.
Proof.
  unfold G_top.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    inv H1; inv H2.
    destruct HG as [Hr2 [HS HG]].
    repeat (split; auto); intros.
    apply Included_Union_compat; auto.
    apply Included_refl.
    inv H1.
    inv H2.
    eapply HG; eauto.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
    inv H; inv H0; inv H1; inv H2.
    destruct HG as [Hr2 [HS HG]].

    split.
    eapply wf_env_set; eauto.
    eapply (wf_env_set_lists _ Hr2 vs2 xs); eauto.
    eapply V_wf_val_Forall_r; eauto.
    eapply V_wf_val_r; eauto.

    split.
    apply Included_Union_compat; auto.
    apply Included_refl.

    intros.
    destruct (M.elt_eq x a); subst.
    + repeat rewrite M.gss in *; eauto.
      eexists; eexists; split; eauto.
    + repeat (rewrite M.gso in *; auto).
      edestruct IHxs as [v1' [v2' [Heqv1' [Heqv2' [Hex HV']]]]]; eauto.
      eapply not_In_cons_Union; eauto.
Qed.

(* Monotonicity Lemma *)
Lemma G_top_mono {Γ1 Γ2 ρ1 ρ2} i j:
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  j <= i ->
  G_top j Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G_top.
  intros.
  destruct H as [Hr2 [HS HG]].
  repeat (split; auto); intros.
  edestruct HG as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto.
  eexists; eexists; repeat split; eauto.
  apply V_mono with i; eauto.
Qed.

(* Compatibility Lemmas *)
Lemma Vfun_V_top e e' :
  trans_correct_top e e' ->
  forall i f xs Γ1 Γ2 ρ1 ρ2,
    wf_env ρ2 ->
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    A0.occurs_free e \subset (FromList xs :|: (f |: Γ1)) ->
    A1.occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
    V i (A0.Vfun f ρ1 xs e) (Tag w0 (A1.Vfun f ρ2 xs e')).
Proof.
  unfold trans_correct_top.
  intros [HS He] i.
  induction i; simpl; intros; auto;
    assert (exposed (Tag w0 (A1.Vfun f ρ2 xs e'))) by (constructor; apply w0_exposed);
    repeat (split; auto); intros.
  destruct (exposed_reflect w0).
  2 : { exfalso; apply n; apply w0_exposed. }

  apply (He (i - (i - j)) ρ3 ρ4); auto.
  eapply G_top_subset with (Γ1 := FromList xs :|: (f |: Γ1)) (Γ2 := FromList xs :|: (f |: Γ2)); eauto.
  eapply G_top_set_lists; eauto.
  eapply G_top_set; eauto.
  eapply G_top_mono; eauto; try lia.
  apply V_mono with i; try lia.
  eapply IHi with (Γ2 := Γ2); eauto.
  apply G_top_mono with (S i); eauto; lia.
Qed.

Lemma free_fun_compat e e' f k k' xs :
  A1.occurs_free e' \subset A0.occurs_free e ->
  A1.occurs_free k' \subset A0.occurs_free k ->
  A1.occurs_free (A1.Efun f w0 xs e' k') \subset A0.occurs_free (A0.Efun f xs e k).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  inv H1; auto.
Qed.

Lemma fun_compat_top e e' k k' f xs :
  trans_correct_top e e' ->
  trans_correct_top k k' ->
  trans_correct_top (A0.Efun f xs e k) (Efun f w0 xs e' k').
Proof.
  unfold trans_correct_top, E, E'.
  intros.
  destruct H.
  destruct H0.
  split; intros.
  eapply free_fun_compat; eauto.

  pose proof H3 as HG.
  destruct H3 as [Hr2 [HS HG']].
  inv H5.
  - exists 0, OOT; split; simpl; eauto.
  - inv H3.
    edestruct (H2 (i - 1) (M.set f (A0.Vfun f ρ1 xs e) ρ1) (M.set f (Tag w0 (A1.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_top_subset with (Γ1 := (f |: (A0.occurs_free (A0.Efun f xs e k)))) (Γ2 := (f |: (A1.occurs_free (A1.Efun f w0 xs e' k')))); eauto.
      * eapply G_top_set; eauto.
        eapply G_top_mono; eauto; try lia.
        eapply Vfun_V_top with (Γ1 := (A0.occurs_free (A0.Efun f xs e k))) (Γ2 := (A1.occurs_free (A1.Efun f w0 xs e' k'))); eauto.
        -- unfold trans_correct_top.
           split; auto.
        -- eapply G_top_mono; eauto; try lia.
        -- eapply A0.free_fun_e_subset; eauto.
        -- eapply A1.free_fun_e_subset; eauto.
      * eapply A0.free_fun_k_subset; eauto.
    + exists (S j2), r2; split; auto.
      * constructor; auto.
        eapply R_exposed_res_r; eauto.
      * apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma free_letapp_compat k k' f x xs :
  A1.occurs_free k' \subset A0.occurs_free k ->
  A1.occurs_free (A1.Eletapp x f w0 xs k') \subset A0.occurs_free (A0.Eletapp x f xs k).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  inv H0; auto.
Qed.

Lemma letapp_compat_top k k' xs x f :
  trans_correct_top k k' ->
  trans_correct_top (A0.Eletapp x f xs k) (A1.Eletapp x f w0 xs k').
Proof.
  unfold trans_correct_top, E, E'.
  intros.
  destruct H.
  split; intros.
  eapply free_letapp_compat; eauto.

  pose proof H1 as HG.
  destruct H1 as [Hr2 [HS HG']].
  inv H3.
  - exists 0, OOT; split; simpl; auto.
  - inv H1.
    + edestruct (HG' f) as [fv1 [fv2 [Heqfv1 [Heqfv2 [Hexfv HVf]]]]]; eauto.
      rewrite Heqfv1 in H7; inv H7.
      destruct fv2.
      destruct i.
      inv H2.
      simpl in HVf.
      destruct HVf as [Hfv2 [Hw HV]]; subst.
      destruct v0; try contradiction.
      destruct HV as [Hlen HV].

      edestruct (G_top_get_list HG xs) as [vs1 [vs2 [Heqvs1 [Heqvs2 HVvs]]]].
      eapply A0.free_letapp_xs_subset; eauto.

      rewrite Heqvs1 in H8; inv H8.

      destruct (set_lists_length3 (M.set v0 (Tag w0 (Vfun v0 t l e0)) t) l vs2) as [ρ4 Heqρ4].
      unfold wval in *.
      rewrite <- (Forall2_length _ _ _ HVvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H11); auto.

      inv Hw.
      apply Exposed_Singleton in H3; subst.

      unfold E' in HV.
      edestruct (HV i vs vs2 ρ'' ρ4) with (j1 := c0) as [j2 [r2 [He0 HR]]]; eauto; try lia.
      * intros.
        eapply V_exposed_Forall_r; eauto.
      * eapply V_mono_Forall; eauto; lia.
      * destruct r2; simpl in HR; try contradiction.
        edestruct (H0 (i - c0) (M.set x v ρ1) (M.set x w ρ2)) with (j1 := c') as [j3 [r3 [He1 HR']]]; eauto; try lia.
        eapply G_top_subset with (Γ1 := x |: (A0.occurs_free (A0.Eletapp x f xs k))) (Γ2 := x |: (A1.occurs_free (A1.Eletapp x f w0 xs k'))); eauto.
        eapply G_top_set; eauto.
        eapply G_top_mono; eauto; lia.
        -- eapply V_wf_val_r; eauto.
        -- eapply V_mono; eauto; try lia.
        -- eapply A0.free_letapp_k_subset; eauto.
        -- exists (S (j2 + j3)), r3; split; eauto.
           2 : { eapply R_mono; eauto; lia. }

           constructor; auto.
           econstructor; eauto.
           intros.
           split.
           eapply V_exposed_Forall_r; eauto.
           eapply V_exposed_r; eauto.
           eapply R_exposed_res_r; eauto.
    + eexists; exists OOT; split; simpl; eauto.
Qed.

(* Linking Preservation *)
Lemma preserves_linking f x e1 e2 e1' e2' :
  trans_correct_top e1 e2 ->
  trans_correct_top e1' e2' ->
  trans_correct_top (A0.link f x e1 e1') (A1.link f Annotate.w0 x e2 e2').
Proof.
  unfold A0.link, A1.link.
  intros.
  eapply fun_compat_top; eauto.
  eapply letapp_compat_top; eauto.
Qed.

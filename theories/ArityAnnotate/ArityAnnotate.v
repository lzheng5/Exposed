From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From LambdaANF Require Import ANF.
From LambdaWeb Require Import ANF Erase.
From Annotate Require Import Annotate.

(* Trivial Web Annotation Based on Function Arities *)

(* We annotate function values with some Exposed web id based on their arities. *)
(* We annotate constructor values with a single Exposed web id. *)

(* Note this is basically annotating `fun_tag`s in CertiCoq, however, there are no internal webs. *)

Module A0 := LambdaANF.ANF.
Module A1 := LambdaWeb.ANF.

Definition arity_to_web (n : nat) : web := Pos.of_nat n.

(* Annotate constructor values with `wc`.
   This works since closure and constructor values live in different web universes. *)
Definition wc := arity_to_web 0.

(* Specification *)
Inductive trans (Γ : vars) : A0.exp -> A1.exp -> Prop :=
| Trans_ret :
  forall {x},
    (x \in Γ) ->
    trans Γ (A0.Eret x) (A1.Eret x)

| Trans_fun :
  forall {f xs e k e' k'},
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->
    trans Γ (A0.Efun f xs e k) (A1.Efun f w xs e' k')

| Trans_app :
  forall {f xs},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    trans Γ (A0.Eapp f xs) (A1.Eapp f w xs)

| Trans_letapp :
  forall {x f xs k k'},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    trans (x |: Γ) k k' ->
    trans Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w xs k')

| Trans_constr :
  forall {x t xs k k'},
    (FromList xs \subset Γ) ->
    (wc \in Exposed) ->
    trans (x |: Γ) k k' ->
    trans Γ (A0.Econstr x t xs k) (A1.Econstr x wc t xs k')

| Trans_proj :
  forall {x y k k' n},
    (y \in Γ) ->
    (wc \in Exposed) ->
    trans (x |: Γ) k k' ->
    trans Γ (A0.Eproj x n y k) (A1.Eproj x wc n y k')

| Trans_case_nil :
  forall {x},
    (x \in Γ) ->
    (wc \in Exposed) ->
    trans Γ (A0.Ecase x []) (A1.Ecase x wc [])

| Trans_case_cons :
  forall {x e e' t cl cl'},
    (x \in Γ) ->
    (wc \in Exposed) ->
    trans Γ e e' ->
    trans Γ (A0.Ecase x cl) (A1.Ecase x wc cl') ->
    trans Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x wc ((t, e') :: cl')).

Hint Constructors trans : core.

Lemma trans_exp_inv {Γ e e'} :
  trans Γ e e' ->
  (A1.occurs_free e') \subset (A0.occurs_free e).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros H.
  induction H; simpl; intros; auto.
  - inv H0; auto.
  - inv H2; auto.
  - inv H2; auto.
  - inv H3; auto.
  - inv H2; auto.
  - inv H2; auto.
  - inv H1; auto.
  - inv H3; auto.
Qed.

Lemma trans_exp_weaken {Γ Γ' e e'} :
  trans Γ e e' ->
  Γ \subset Γ' ->
  trans Γ' e e'.
Proof.
  intros H.
  revert Γ'.
  induction H; simpl; intros; auto; subst.
  - constructor; auto.
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
  - constructor; auto.
    + eapply Included_trans; eauto.
    + eapply IHtrans; eauto.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
  - constructor; auto.
    eapply IHtrans; eauto.
    eapply Included_Union_compat; eauto.
    apply Included_refl.
Qed.

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
    exposed wv2 /\
    match wv2 with
    | A1.TAG _ w2 v2 =>
        match v1, v2 with
        | A0.Vconstr c1 vs1, A1.Vconstr c2 vs2 =>
              w2 = wc /\
              c1 = c2 /\
              match i with
              | 0 => length vs1 = length vs2
              | S i0 => Forall2 (V i0) vs1 vs2
              end

        | A0.Vfun f1 ρ1 xs1 e1, A1.Vfun f2 ρ2 xs2 e2 =>
            length xs1 = length xs2 /\
              w2 = arity_to_web (length xs1) /\
              match i with
              | 0 => True
              | S i0 =>
                  forall j vs1 vs2 ρ3 ρ4,
                    j <= i0 ->
                    Forall exposed vs2 ->
                    Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                    set_lists xs1 vs1 (M.set f1 (A0.Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
                    set_lists xs2 vs2 (M.set f2 (Tag w2 (A1.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                    E' V true (i0 - (i0 - j)) ρ3 e1 ρ4 e2
              end
        | _, _ => False
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

(* Exposed Lemmas *)
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
Definition G i Γ1 ρ1 ρ2 :=
  wf_env ρ2 /\
    forall x,
      (x \in Γ1) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
          M.get x ρ2 = Some v2 /\
          V i v1 v2.

(* Environment Lemmas *)
Lemma G_subset Γ1 Γ2 {i ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  G i Γ2 ρ1 ρ2.
Proof. unfold G. fcrush. Qed.

Lemma G_wf_env_r i Γ1 ρ1 ρ2 :
  G i Γ1 ρ1 ρ2 ->
  wf_env ρ2.
Proof. unfold G. intros; tauto. Qed.

Lemma G_get {Γ1 i ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  forall x v1,
    (x \in Γ1) ->
    M.get x ρ1 = Some v1 ->
    exists v2,
      M.get x ρ2 = Some v2 /\
        V i v1 v2.
Proof.
  unfold G.
  intros.
  destruct H as [Hwf HG].
  edestruct HG as [v1' [v2 [Heqv1 [Heqv2 HV]]]]; eauto; invc.
  fcrush.
Qed.

Lemma G_get_list {i Γ1 ρ1 ρ2} :
  G i Γ1 ρ1 ρ2 ->
  forall xs vs1,
    (FromList xs) \subset Γ1 ->
    get_list xs ρ1 = Some vs1 ->
    exists vs2,
      get_list xs ρ2 = Some vs2 /\
        Forall2 (V i) vs1 vs2.
Proof.
  intros HG xs.
  induction xs; simpl; intros.
  - fcrush.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H0.
    unfold Ensembles.Included, Ensembles.In in *.
    edestruct (G_get HG) as [v2 [Heqv2 HV]]; eauto.
    eapply (H a); fcrush.
    edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto; fcrush.
Qed.

Lemma G_set {i Γ1 ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  forall {x v1 v2},
    V i v1 v2 ->
    G i (x |: Γ1) (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  unfold G.
  intro HG.
  pose proof HG as HG'.
  intros.

  destruct HG as [Hwf HG].
  split.
  eapply wf_env_set; eauto.
  eapply V_wf_val_r; eauto.

  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss in *.
    fcrush.
  - repeat (rewrite M.gso in *; auto).
    fcrush.
Qed.

Lemma G_set_lists {i Γ1 ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 (V i) vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    G i (FromList xs :|: Γ1) ρ3 ρ4.
Proof.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    inv H0; inv H1.
    eapply G_subset; eauto; normalize_sets;
      rewrite Union_Empty_set_neut_l; eauto;
      apply Included_refl.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
    inv H; inv H0; inv H1.
    eapply G_subset with (Γ1 := (a |: (FromList xs :|: Γ1))); eauto;
      try (normalize_sets;
           rewrite Union_assoc;
           apply Included_refl).
    eapply G_set; eauto.
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
    + fcrush.
    + destruct HV as [Heqw [Heqc HV]]; subst.
      repeat split; auto.
      eapply Forall2_length; eauto.
  - repeat (split; auto).
    destruct v1; destruct v; try contradiction.
    + destruct HV as [Hlen [Heqw HV]]; subst.
      repeat split; auto; intros.
      specialize (HV j0 vs1 vs2 ρ3 ρ4).
      rewrite normalize_step in *; try lia.
      apply HV; eauto; lia.
    + destruct HV as [Heqw [Heqc HV]]; subst.
      repeat split; auto.
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
  unfold E, R, E', R'.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; eauto.
  apply R_mono with (i - j1); try lia; auto.
Qed.

Lemma G_mono {Γ1 ρ1 ρ2} i j:
  G i Γ1 ρ1 ρ2 ->
  j <= i ->
  G j Γ1 ρ1 ρ2.
Proof.
  unfold G.
  intros.
  inv H.
  split; auto; intros.
  edestruct H2 as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto; invc.
  eexists; eexists; repeat split; eauto.
  apply V_mono with i; eauto.
Qed.

(* Compatibility Lemmas *)
Definition trans_correct Γ e1 e2 :=
  forall i ρ1 ρ2,
    G i Γ ρ1 ρ2 ->
    E true i ρ1 e1 ρ2 e2.

Lemma ret_compat Γ x :
  (x \in Γ) ->
  trans_correct Γ (A0.Eret x) (A1.Eret x).
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H2.
  - fcrush.
  - inv H3.
    edestruct (G_get H0) as [v2 [Heqv2 HV]]; eauto.
    exists 1, (A1.Res v2); split; auto.
    + constructor.
      * constructor; auto.
      * eapply V_exposed_res_r; eauto.
    + eapply V_mono; eauto; lia.
Qed.

Lemma Vfun_V Γ1 f xs e e' :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  forall {i ρ1 ρ2},
    wf_env ρ2 ->
    G i Γ1 ρ1 ρ2 ->
    let w := arity_to_web (length xs) in
    (w \in Exposed) ->
    V i (A0.Vfun f ρ1 xs e) (Tag w (A1.Vfun f ρ2 xs e')).
Proof.
  unfold trans_correct.
  intros He i.
  induction i; simpl; intros; auto;
    repeat (split; auto); simpl;
    destruct (exposed_reflect (arity_to_web (length xs))); try contradiction;
    repeat (split; eauto);
    try (constructor; apply w0_exposed);
    intros.

  apply (He (i - (i - j)) ρ3 ρ4); auto.
  - eapply G_set_lists; eauto.
    eapply G_set; eauto.
    + apply G_mono with (S i); eauto; lia.
    + apply V_mono with i; try lia.
      eapply IHi; eauto.
      apply G_mono with (S i); eauto; lia.
Qed.

Lemma fun_compat Γ e e' k k' f xs :
  let w := arity_to_web (length xs) in
  (w \in Exposed) ->
  trans_correct (FromList xs :|: (f |: Γ)) e e' ->
  trans_correct (f |: Γ) k k' ->
  trans_correct Γ (A0.Efun f xs e k) (A1.Efun f w xs e' k').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H4.
  - exists 0, A1.OOT; split; simpl; eauto.
  - inv H5.
    edestruct (H1 (i - 1) (M.set f (A0.Vfun f ρ1 xs e) ρ1) (M.set f (Tag (arity_to_web (length xs)) (A1.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_set; eauto.
      apply G_mono with i; eauto; lia.
      * eapply Vfun_V; eauto.
        -- eapply G_wf_env_r; eauto.
        -- apply G_mono with i; eauto; lia.
    + exists (S j2), r2; split; auto.
      constructor.
      econstructor; eauto.
      eapply R_exposed_res_r; eauto.
      eapply R_mono; eauto; lia.
Qed.

Lemma app_compat Γ (xs : list var) f :
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  let w := arity_to_web (length xs) in
  (w \in Exposed) ->
  trans_correct Γ (A0.Eapp f xs) (A1.Eapp f w xs).
Proof.
  unfold trans_correct, E, E'.
  intros.
  rename H2 into HG.
  inv H4.
  - fcrush.
  - inv H2.
    edestruct (G_get HG f) as [fv2 [Heqfv2 HV]]; eauto.
    destruct i.
    fcrush.

    destruct fv2; simpl in HV;
      destruct HV as [Hv1 [Hexv1 HV]];
      destruct v; try contradiction.
    destruct HV as [Hlen [Heqw HV]]; subst.

    edestruct (G_get_list HG xs vs) as [vs2 [Heqvs2 Vvs]]; eauto.

    destruct (set_lists_length3 (M.set v (Tag (arity_to_web (length xs')) (A1.Vfun v t l e0)) t) l vs2) as [ρ4 Heqρ4].
    unfold wval in *.
    rewrite <- (Forall2_length _ _ _ Vvs).
    rewrite <- (set_lists_length_eq _ _ _ _ H8); auto.

    assert (HE : E true (i - (i - i)) ρ'' e ρ4 e0).
    {
      eapply (HV i vs vs2); eauto.
      eapply V_exposed_Forall_r; eauto.
      apply V_mono_Forall with (S i); auto; lia.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E in HE.
    destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.

    assert (length xs = length xs').
    {
      unfold var in *.
      erewrite (get_list_length_eq xs vs); eauto.
      symmetry; apply (set_lists_length_eq _ _ _ _ H8).
    }

    assert (Harity : arity_to_web (length xs) = arity_to_web (length xs')) by eauto.
    rewrite Harity in *.
    exists (S j2), r2; split; eauto.
    constructor; auto.
    econstructor; eauto.
    destruct (exposed_reflect (arity_to_web (length xs'))); try contradiction; auto.
    intros; split.
    eapply V_exposed_Forall_r; eauto.
    eapply R_exposed_res_r; eauto.
    eapply R_exposed_res_r; eauto.
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
  - admit.
  - (* eapply proj_compat; eauto. *) admit.
  - (* eapply case_nil_compat; eauto. *) admit.
  - (* eapply case_cons_compat; eauto. *) admit.
Admitted.

(* Top-level *)

Definition trans_correct_top etop etop' :=
  A1.occurs_free etop' \subset A0.occurs_free etop /\
  trans_correct (A0.occurs_free etop) etop etop'.

Lemma trans_correct_top_subset e1 e2 :
  trans_correct_top e1 e2 ->
  A1.occurs_free e2 \subset A0.occurs_free e1.
Proof.
  unfold trans_correct_top.
  intros.
  inv H; auto.
Qed.

Lemma trans_correct_top_trans_correct e1 e2 :
  trans_correct_top e1 e2 ->
  trans_correct (A0.occurs_free e1) e1 e2.
Proof.
  unfold trans_correct_top, trans_correct.
  sfirstorder.
Qed.

Lemma trans_correct_trans_correct_top e1 e2:
  A1.occurs_free e2 \subset A0.occurs_free e1 ->
  trans_correct (A0.occurs_free e1) e1 e2 ->
  trans_correct_top e1 e2.
Proof.
  unfold trans_correct_top, trans_correct.
  sfirstorder.
Qed.

Theorem top etop etop':
  trans (A0.occurs_free etop) etop etop' ->
  trans_correct_top etop etop'.
Proof.
  intros H.
  specialize (fundamental_property H).
  eapply trans_correct_trans_correct_top; eauto.
  eapply trans_exp_inv; eauto.
Qed.

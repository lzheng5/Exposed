From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF0.

(* Reflexive Logical Relation without Webs *)

(* Logical Relations *)
Definition R' (P : nat -> val -> val -> Prop) (i : nat) (r1 : res) (r2 : res) :=
  match r1, r2 with
  | OOT, OOT => True
  | Res v1, Res v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> val -> val -> Prop) (i : nat) (ρ1 : env) (e1 :exp) (ρ2 : env) (e2 : exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    bstep_fuel ρ1 e1 j1 r1 ->
    exists j2 r2,
      bstep_fuel ρ2 e2 j2 r2 /\
      R' P (i - j1) r1 r2.

Fixpoint V (i : nat) (v1 : val) (v2 : val) {struct i} : Prop :=
  match v1, v2 with
  | Vconstr c1 vs1, Vconstr c2 vs2 =>
      c1 = c2 /\
      match i with
      | 0 => length vs1 = length vs2
      | S i0 => Forall2 (V i0) vs1 vs2
      end

  | Vfun f1 ρ1 xs1 e1, Vfun f2 ρ2 xs2 e2 =>
      length xs1 = length xs2 /\
      match i with
      | 0 => True
      | S i0 =>
          forall j vs1 vs2 ρ3 ρ4,
            j <= i0 ->
            Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
            set_lists xs1 vs1 (M.set f1 (Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
            set_lists xs2 vs2 (M.set f2 (Vfun f2 ρ2 xs2 e2) ρ2) = Some ρ4 ->
            E' V (i0 - (i0 - j)) ρ3 e1 ρ4 e2
      end

  | _, _ => False
  end.

Notation R := (R' V).

Notation E := (E' V).

(* Environment Relation *)
Definition G i Γ ρ1 ρ2 :=
  forall x,
    (x \in Γ) ->
    forall v1,
      M.get x ρ1 = Some v1 ->
      exists v2,
        M.get x ρ2 = Some v2 /\
        V i v1 v2.

(* Environment Lemmas *)
Lemma G_get {i Γ ρ1 ρ2}:
  G i Γ ρ1 ρ2 ->
  forall x v1,
    (x \in Γ) ->
    M.get x ρ1 = Some v1 ->
    exists v2,
      M.get x ρ2 = Some v2 /\
      V i v1 v2.
Proof.
  unfold G.
  intros HG; intros; eauto.
Qed.


Lemma G_set {i Γ ρ1 ρ2}:
  G i Γ ρ1 ρ2 ->
  forall {x v1 v2},
    V i v1 v2 ->
    G i (x |: Γ) (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  unfold G.
  intros HG; intros.
  destruct (M.elt_eq x0 x); subst.
  - rewrite M.gss in *.
    inv H1; eauto.
  - rewrite M.gso in *; auto.
    edestruct (G_get HG) as [v2' [Heqv2' HV]]; eauto.
    inv H0; auto.
    inv H2; contradiction.
Qed.

Lemma G_get_list {i Γ ρ1 ρ2} :
  G i Γ ρ1 ρ2 ->
  forall xs vs1,
    (FromList xs \subset Γ) ->
    get_list xs ρ1 = Some vs1 ->
    exists vs2,
      get_list xs ρ2 = Some vs2 /\
      Forall2 (V i) vs1 vs2.
Proof.
  intros HG xs.
  induction xs; simpl; intros.
  - inv H0; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H0.
    rewrite FromList_cons in H.
    edestruct (G_get HG) as [v2 [Heqv2 Vv]]; eauto.
    rewrite Heqv2.
    edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
    apply Union_Included_r in H; auto.
    rewrite Heqvs2.
    exists (v2 :: vs2); split; auto.
Qed.

Lemma G_set_lists {i Γ ρ1 ρ2}:
  G i Γ ρ1 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 (V i) vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    G i (FromList xs :|: Γ) ρ3 ρ4.
Proof.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    inv H0; inv H1.
    unfold G.
    intros.
    eapply (G_get HG); eauto.
    inv H0; auto.
    inv H2.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
    inv H; inv H0; inv H1.
    unfold G.
    intros.
    destruct (M.elt_eq x a); subst.
    + rewrite M.gss in *; eauto.
      inv H0; eauto.
    + rewrite M.gso in *; auto.
      eapply IHxs; eauto.
      eapply not_In_cons_Union; eauto.
Qed.

Lemma G_subset Γ1 Γ2 i ρ1 ρ2:
  G i Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  G i Γ2 ρ1 ρ2.
Proof.
  unfold G.
  intros; eauto.
Qed.

(* Monotonicity Lemmas *)
Lemma ForallV_mono_aux :
  forall i j V vs1 vs2,
    (forall k : nat,
        k < S i ->
        forall (j : nat) (v1 v2 : val), V k v1 v2 -> j <= k -> V j v1 v2) ->
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
  destruct i; simpl in H0.
  - inv H1; simpl in *.
    destruct v1; destruct v2; try contradiction; auto.
  - destruct j; simpl.
    + destruct v1; destruct v2; try contradiction; auto.
      * destruct H0; auto.
      * destruct H0; subst.
        split; auto.
        eapply Forall2_length; eauto.
    + destruct v1; destruct v2; try contradiction; auto.
      * destruct H0.
        split; auto; intros.
        specialize (H2 j0 vs1 vs2 ρ3 ρ4).
        rewrite normalize_step in *; try lia.
        apply H2; eauto; lia.
      * destruct H0.
        repeat (split; auto).
        eapply ForallV_mono_aux; eauto; lia.
Qed.

Lemma ForallV_mono {vs1 vs2} i j :
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

Lemma E_mono {ρ1 ρ2 e1 e2} i j:
  E i ρ1 e1 ρ2 e2 ->
  j <= i ->
  E j ρ1 e1 ρ2 e2.
Proof.
  unfold E.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; eauto.
  apply R_mono with (i - j1); try lia; auto.
Qed.

Lemma G_mono {Γ ρ1 ρ2} i j:
  G i Γ ρ1 ρ2 ->
  j <= i ->
  G j Γ ρ1 ρ2.
Proof.
  unfold G.
  intros.
  edestruct H as [v2 [Heqv2 Vv]]; eauto.
  exists v2; split; auto.
  apply V_mono with i; eauto.
Qed.

Definition related e1 e2 :=
  forall i ρ1 ρ2,
    G i (occurs_free e1) ρ1 ρ2 ->
    E i ρ1 e1 ρ2 e2.

(* Compatibility Lemmas *)
Lemma ret_compat x :
  related (Eret x) (Eret x).
Proof.
  unfold related, E, R.
  intros.
  inv H1.
  - exists 0, OOT; split; auto.
  - inv H2.
    edestruct (G_get H) as [v2 [Heqv2 Vv]]; eauto.
    exists 1, (Res v2); split; auto.
    apply V_mono with i; try lia; auto.
Qed.

Lemma constr_compat {k} x t xs :
  related k k ->
  related (Econstr x t xs k) (Econstr x t xs k).
Proof.
  unfold related, E, E'.
  intros.
  inv H2.
  - exists 0, OOT; split; simpl; auto.
  - inv H3.
    destruct (G_get_list H0 xs vs) as [vs' [Heqvs' Hvs]]; auto.
    apply free_constr_xs_subset; auto.

    assert (length vs = length vs').
    {
      rewrite <- (get_list_length_eq _ _ _ H9).
      rewrite <- (get_list_length_eq _ _ _ Heqvs'); auto.
    }

    edestruct (H i (M.set x (Vconstr t vs) ρ1) (M.set x (Vconstr t vs') ρ2)) with (j1 := c) as [j2 [r2 [Hk HR]]]; eauto; try lia.
    + eapply G_subset; eauto.
      eapply G_set; eauto.
      destruct i; simpl;
        repeat (split; auto).
      eapply ForallV_mono; eauto; lia.
      eapply free_constr_k_subset; eauto.
    + exists (S j2), r2; split; eauto.
      eapply R_mono; eauto; lia.
Qed.

Lemma Vfun_V {e e'} :
  related e e' ->
  forall {i Γ ρ1 ρ2} f xs,
    G i Γ ρ1 ρ2 ->
    (occurs_free e) \subset (FromList xs :|: (f |: Γ)) ->
    V i (Vfun f ρ1 xs e) (Vfun f ρ2 xs e').
Proof.
  unfold related.
  intros He i.
  induction i; simpl; intros;
    repeat (split; auto); intros.
  rewrite normalize_step in *; try lia.
  apply (He j ρ3 ρ4).
  eapply G_subset; eauto.
  eapply G_set_lists; eauto.
  apply G_set; auto.
  - apply G_mono with (S i); auto; lia.
  - apply V_mono with i; try lia.
    eapply IHi; eauto.
    apply G_mono with (S i); auto; lia.
Qed.

Lemma fun_compat {e k} f xs :
  related e e ->
  related k k ->
  related (Efun f xs e k) (Efun f xs e k).
Proof.
  unfold related, E, E'.
  intros.
  inv H3.
  - exists 0, OOT; split; simpl; auto.
  - inv H4.
    edestruct (H0 (i - 1) (M.set f (Vfun f ρ1 xs e) ρ1) (M.set f (Vfun f ρ2 xs e) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_subset; eauto.
      eapply G_set; eauto.
      * eapply G_mono with i; eauto; lia.
      * eapply Vfun_V; eauto.
        eapply G_mono; eauto; lia.
        eapply free_fun_e_subset; eauto.
      * eapply free_fun_k_subset; eauto.
    + exists (S j2), r2; split; eauto.
      apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma app_compat f xs :
  related (Eapp f xs) (Eapp f xs).
Proof.
  unfold related, G, E, E'.
  intros.
  inv H1.
  - exists 0, OOT; split; simpl; auto.
  - inv H2.
    edestruct (G_get H) as [v2 [Heqv2 Vv]]; eauto.
    destruct i.
    inv H0.
    destruct v2; simpl in Vv; try contradiction.
    simpl in Vv.
    destruct Vv as [Hlen HVv]; subst.
    destruct (G_get_list H xs vs) as [vs2 [Heqvs2 Vvs]]; eauto.
    apply free_app_xs_subset; eauto.
    destruct (set_lists_length3 (M.set v (Vfun v t l e0) t) l vs2) as [ρ4 Heqρ4].
    unfold var in Hlen.
    rewrite <- Hlen.
    rewrite (set_lists_length_eq _ _ _ _ H6).
    apply (Forall2_length _ _ _ Vvs).

    assert (HE : E (i - (i - i)) ρ'' e ρ4 e0).
    {
      eapply (HVv i vs vs2); eauto.
      rewrite normalize_step in *; try lia.
      apply ForallV_mono with (S i); auto; lia.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E in HE.
    destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
    exists (S j2), r2; split; eauto.
Qed.

Lemma proj_compat x i y e :
  related e e ->
  related (Eproj x i y e) (Eproj x i y e).
Proof.
  unfold related, E, E'.
  intros.
  inv H2.
  - exists 0, OOT; simpl; eauto.
  - inv H3.
    edestruct (G_get H0) as [v2 [Heqv2 HV]]; eauto.
    destruct i0.
    inv H1.
    destruct v2; simpl in HV; try contradiction.
    destruct HV as [Heqt HV]; subst.
    rename l into vs'.
    destruct (Forall2_nth_error H10 HV) as [v' [Heqv' HFv']].
    edestruct (H i0 (M.set x v ρ1) (M.set x v' ρ2)) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
    + eapply (G_subset (x |: (occurs_free (Eproj x i y e)))); eauto.
      eapply G_set; eauto.
      eapply G_mono; eauto.
      apply free_proj_k_subset; auto.
    + exists (S j2), r2; split; eauto.
Qed.

Lemma letapp_compat {k} x f xs :
  related k k ->
  related (Eletapp x f xs k) (Eletapp x f xs k).
Proof.
  intros.
  specialize (app_compat f xs); intros Ha.
  unfold related, E, E' in *.
  intros.

  assert (HGa : G i (occurs_free (Eapp f xs)) ρ1 ρ2).
  {
    eapply G_subset; eauto.
    eapply free_app_letapp; eauto.
  }

  specialize (Ha _ _ _ HGa).
  inv H2.
  - exists 0, OOT; split; simpl; auto.
  - inv H3.
    + destruct (Ha (S c0) (Res v)) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      * simpl in Rra.
        destruct ra; try contradiction.
        edestruct (H (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
        -- eapply (G_subset (x |: (occurs_free (Eletapp x f xs k)))); eauto.
           eapply G_set; eauto.
           apply G_mono with i; try lia; auto.
           apply free_letapp_k_subset; eauto.
        -- exists (j1 + j2), r2; split.
           ++ inv Hap.
              inv H2.
              assert (Hj : (S c + j2) = S (c + j2)) by lia.
              rewrite Hj; eauto.
           ++ apply R_mono with (i - S c0 - c'); try lia; auto.
    + destruct (Ha (S c) OOT) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      exists j1, ra.
      destruct ra; try contradiction.
      split; auto.
      inv Hap; eauto.
      inv H2; eauto.
Qed.

Lemma case_nil_compat x:
  related (Ecase x []) (Ecase x []).
Proof.
  unfold related, G, E, E', R'.
  intros.
  inv H1.
  - exists 0, OOT; split; simpl; auto.
  - inv H2.
    inv H5.
Qed.

Lemma case_cons_compat e x cl c:
  related e e ->
  related (Ecase x cl) (Ecase x cl) ->
  related (Ecase x ((c, e) :: cl)) (Ecase x ((c, e) :: cl)).
Proof.
  unfold related, E, E', G.
  intros.
  inv H3.
  - exists 0, OOT; split; simpl; eauto.
  - inv H4.
    edestruct (H1 x) as [v2 [Heqv2 HV]]; eauto.
    destruct i.
    inv H2.
    destruct v2; simpl in HV; try contradiction.
    destruct HV as [Heqt HV]; subst.
    inv H7.
    + edestruct (H i ρ1 ρ2) with (j1 := c0) as [j2 [r2 [He' HR]]]; eauto; try lia.
      eapply G_subset; eauto.
      eapply G_mono; eauto.
      apply free_case_hd_subset; auto.
      exists (S j2), r2; split; eauto.
    + edestruct (H0 (S i) ρ1 ρ2) with (j1 := S c0) (r1 := r1) as [j2 [r2 [He' HR]]]; eauto; try lia.
      exists j2, r2; split; eauto.
      inv He'; auto.
      inv H3.
      rewrite Heqv2 in H7; inv H7; eauto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property e :
  related e e.
Proof.
  induction e using exp_ind'.
  - apply ret_compat.
  - apply app_compat.
  - apply fun_compat; auto.
  - apply letapp_compat; auto.
  - apply constr_compat; auto.
  - apply case_nil_compat; auto.
  - apply case_cons_compat; auto.
  - apply proj_compat; auto.
Qed.

(* Reflexivity of E *)
Lemma refl_V_G :
  forall i,
    (forall k : nat, k < S i -> forall v : val, V k v v) ->
    forall ρ xs Γ j vs1 vs2 ρ1 ρ2,
      j <= i ->
      Forall2 (V j) vs1 vs2 ->
      set_lists xs vs1 ρ = Some ρ1 ->
      set_lists xs vs2 ρ = Some ρ2 ->
      G j Γ ρ1 ρ2.
Proof.
  unfold G.
  intros i HI ρ xs.
  induction xs; simpl; intros.
  - destruct vs1; destruct vs2; try discriminate.
    inv H1; inv H2.
    repeat (split; auto); intros.
    eexists; split; eauto.
    eapply HI; eauto; try lia.
  - destruct vs1; destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ) eqn:Heq2; try discriminate.
    inv H0; inv H1; inv H2.

    destruct (M.elt_eq a x); subst.
    + rewrite M.gss in *; auto.
      inv H4.
      eexists; split; eauto.
    + rewrite M.gso in *; auto.
      edestruct IHxs as [v2 [Heqv2 HV]]; eauto.
Qed.

Lemma refl_V_ForallV :
  forall i,
    (forall k : nat, k < S i -> forall v : val, V k v v) ->
    forall vs j,
      j <= i ->
      Forall2 (V j) vs vs.
Proof.
  intros i HI vs.
  induction vs; simpl; intros; auto.
  constructor; auto.
  eapply HI; eauto; try lia.
Qed.

Theorem refl_V :
  forall i v, V i v v.
Proof.
  intros i.
  induction i using lt_wf_rec; intros.
  destruct i; destruct v; intros; simpl in *;
    split; auto; intros.
  - rewrite normalize_step in *; try lia.
    specialize (fundamental_property e); intros FP.
    unfold related in FP.
    apply FP.
    eapply refl_V_G; eauto.
  - eapply refl_V_ForallV; eauto; lia.
Qed.

Corollary refl_V_Forall vs :
  forall i, Forall2 (V i) vs vs.
Proof.
  induction vs; intros; auto;
    constructor; auto.
  eapply refl_V; eauto.
Qed.

Theorem refl_R :
  forall i r, R i r r.
Proof.
  unfold R'.
  intros.
  destruct r; auto.
  apply refl_V; auto.
Qed.

Theorem refl_E :
  forall i ρ e,
    E i ρ e ρ e.
Proof.
  unfold E, E'.
  intros.
  eexists; eexists; split; eauto.
  apply refl_R; auto.
Qed.

Theorem refl_G :
  forall i Γ ρ,
    G i Γ ρ ρ.
Proof.
  unfold G.
  intros.
  eexists; split; eauto.
  apply refl_V.
Qed.

(* Transitivity of E *)
Lemma trans_E_aux i :
  (forall m : nat,
      m <= i ->
      forall v1 v2 v3 : val,
        V m v1 v2 ->
        (forall i : nat, V i v2 v3) ->
        V m v1 v3) ->
  forall {ρ1 e1 ρ2 e2 ρ3 e3},
    E i ρ1 e1 ρ2 e2 ->
    (forall i, E i ρ2 e2 ρ3 e3) ->
    E i ρ1 e1 ρ3 e3.
Proof.
  unfold E, E'.
  intros IH; intros.
  edestruct H as [j2 [r2 [Hr2 HR]]]; eauto.
  edestruct (H0 j2) as [j3 [r3 [Hr3 HR']]]; eauto; try lia.
  eexists; eexists; split; eauto.
  unfold R' in *.
  destruct r1; destruct r2; destruct r3; try contradiction; auto.
  eapply IH; eauto; try lia.
  intros.
  edestruct (H0 (i0 + j2) j2) as [j3' [r3' [Hr3' HR'']]]; eauto; try lia.
  simpl in *.
  destruct r3'; try contradiction.
  edestruct (bstep_fuel_deterministic v1 v2 Hr3 Hr3'); eauto; subst.
  eapply V_mono; eauto; try lia.
Qed.

Lemma trans_V_Forall_aux i :
  (forall m : nat,
      m <= i ->
      forall v1 v2 v3 : val,
        V m v1 v2 ->
        (forall i : nat, V i v2 v3) ->
        V m v1 v3) ->
  forall {vs1 vs2 vs3},
    Forall2 (V i) vs1 vs2 ->
    (forall i, Forall2 (V i) vs2 vs3) ->
    Forall2 (V i) vs1 vs3.
Proof.
  intros IH vs1.
  induction vs1; simpl; intros.
  - inv H.
    eapply H0; eauto.
  - inv H.
    pose proof (H0 i) as H0'.
    inv H0'.
    constructor.
    + eapply IH; eauto; try lia.
      intros.
      specialize (H0 i0).
      inv H0; auto.
    + eapply IHvs1; eauto; try lia.
      intros.
      specialize (H0 i0).
      inv H0; auto.
Qed.

Theorem trans_V :
  forall {i v1 v2 v3},
    V i v1 v2 ->
    (forall i, V i v2 v3) ->
    V i v1 v3.
Proof.
  intros i.
  induction i using lt_wf_rec1; intros.
  destruct i.
  - specialize (H1 0).
    destruct v1; destruct v2; destruct v3;
      simpl in *; try contradiction.
    + destruct H0; destruct H1; subst.
      split; auto.
      rewrite H0; auto.
    + destruct H0; destruct H1; subst.
      split; auto.
      rewrite H2; auto.
  - pose proof (H1 (S i)).
    simpl in *.
    destruct v1; destruct v2; destruct v3; try contradiction.
    + destruct H0 as [Hlen HV];
      destruct H2 as [Hlen' HV'].

      split.
      rewrite Hlen; auto.

      intros.
      destruct (set_lists_length3 (M.set v0 (Vfun v0 t0 l0 e0) t0) l0 vs2) as [ρ5 Heqρ5].
      rewrite <- (set_lists_length_eq _ _ _ _ H4); auto.
      eapply trans_E_aux; eauto.
      * intros; eapply H; eauto; lia.
      * clear HV'.
        intros k.
        specialize (H1 (S k)); simpl in H1.
        destruct H1 as [_ HV'].
        assert (E (k - (k - k)) ρ5 e0 ρ4 e1).
        {
          eapply (HV' k vs2 vs2); eauto; try lia.
          intros.
          destruct H2; auto.
          eapply refl_V_Forall; eauto.
        }
        eapply E_mono; eauto; try lia.
    + destruct H0 as [Hc HV]; subst.
      destruct H2 as [Hc' HV']; subst.
      split; auto.
      eapply trans_V_Forall_aux; eauto; try lia.
      * intros; eapply H; eauto; lia.
      * clear HV'.
        intros.
        specialize (H1 (S i0)); simpl in H1.
        destruct H1 as [_ HV']; auto.
Qed.

Corollary trans_R {i r1 r2 r3} :
  R i r1 r2 ->
  (forall k, R k r2 r3) ->
  R i r1 r3.
Proof.
  unfold R, R'.
  intros.
  destruct r1; destruct r2; destruct r3; try contradiction; auto.
  eapply trans_V; eauto.
Qed.

Corollary trans_E {i ρ1 e1 ρ2 e2 ρ3 e3}:
  E i ρ1 e1 ρ2 e2 ->
  (forall i, E i ρ2 e2 ρ3 e3) ->
  E i ρ1 e1 ρ3 e3.
Proof.
  intros.
  eapply trans_E_aux; eauto.
  intros.
  eapply trans_V; eauto.
Qed.

(* Top Level *)
Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  Γ2 \subset Γ1 /\
  G i Γ1 ρ1 ρ2.

Lemma G_top_G : forall {i Γ1 ρ1 Γ2 ρ2},
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    G i Γ1 ρ1 ρ2.
Proof.
  unfold G_top.
  intros.
  destruct H; auto.
Qed.

Definition related_top etop etop' :=
  occurs_free etop' \subset occurs_free etop /\
  forall i ρ1 ρ2,
    G_top i (occurs_free etop) ρ1 (occurs_free etop') ρ2 ->
    E i ρ1 etop ρ2 etop'.

Theorem top {etop}:
  related_top etop etop.
Proof.
  unfold related_top.
  intros.
  specialize (fundamental_property etop);
    unfold related; intros.
  split; intros.
  apply Included_refl.

  eapply H; eauto.
  eapply G_top_G; eauto.
Qed.

(* Reflexivity of [related_top] *)
Corollary refl_related_top :
  Reflexive related_top.
Proof.
  unfold related_top.
  intros e.
  split.
  apply Included_refl.
  intros.
  specialize (fundamental_property e);
    unfold related.
  intros.
  eapply H0; eauto.
  eapply G_top_G; eauto.
Qed.

(* Transitivity of [related_top] *)
Theorem trans_related_top :
  Transitive related_top.
Proof.
  intros e1 e2 e3.
  unfold related_top, G_top.
  intros.
  destruct H.
  destruct H0.
  split; intros.
  - eapply Included_trans; eauto.
  - destruct H3 as [Hs HG].
    eapply trans_E; eauto.
    intros.
    eapply H2; eauto.
    repeat (split; auto); intros.
    unfold Ensembles.Included, Ensembles.In in *.
    eapply refl_G; eauto.
Qed.

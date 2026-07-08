From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From LambdaANF Require Import Util Tactics ANF ValInd.

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
  let fix V' (v1 : val) (v2 : val) {struct v1} : Prop :=
  match v1, v2 with
  | Vconstr c1 vs1, Vconstr c2 vs2 =>
      let fix Forall2_aux vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 =>
            V' v1 v2 /\ Forall2_aux vs1 vs2
        | _, _ => False
        end in
      c1 = c2 /\
      Forall2_aux vs1 vs2

  | Vfun f1 ρ1 xs1 e1, Vfun f2 ρ2 xs2 e2 =>
      length xs1 = length xs2 /\
      forall j vs1 vs2 ρ3 ρ4,
        set_lists xs1 vs1 (M.set f1 (Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
        set_lists xs2 vs2 (M.set f2 (Vfun f2 ρ2 xs2 e2) ρ2) = Some ρ4 ->
        match i with
        | 0 => True
        | S i0 =>
            j <= i0 ->
            Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
            E' V (i0 - (i0 - j)) ρ3 e1 ρ4 e2
        end

  | _, _ => False
  end in
  V' v1 v2.

Definition V' (i : nat) (v1 : val) (v2 : val) : Prop :=
  match v1, v2 with
  | Vconstr c1 vs1, Vconstr c2 vs2 =>
      c1 = c2 /\ Forall2 (V i) vs1 vs2

  | Vfun f1 ρ1 xs1 e1, Vfun f2 ρ2 xs2 e2 =>
      length xs1 = length xs2 /\
      forall j vs1 vs2 ρ3 ρ4,
        set_lists xs1 vs1 (M.set f1 (Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
        set_lists xs2 vs2 (M.set f2 (Vfun f2 ρ2 xs2 e2) ρ2) = Some ρ4 ->
        j < i ->
        Forall2 (V j) vs1 vs2 ->
        E' V j ρ3 e1 ρ4 e2
  | _, _ => False
  end.

Lemma V_eq (i : nat) (v1 v2 : val) :
  V i v1 v2 <-> V' i v1 v2.
Proof.
  destruct v1; destruct v2; prog;
  unfold V' in *; try (destruct i; simpl in *; prog; split; prog; fail).
  - destruct i; simpl in *; split; prog.
    + specialize (H0 j); rewrite normalize_step in *; try lia.
      eapply H0; try lia; eauto.
    + specialize (H0 j); rewrite normalize_step in *; try lia.
      eapply H0; try lia; eauto.
  - destruct i; simpl in *; split; prog.
    + generalize dependent l0.
      induction l; destruct l0; prog.
    + generalize dependent l0.
      induction l; destruct l0; prog.
      apply IHl; auto.
    + generalize dependent l0.
      induction l; destruct l0; prog.
    + generalize dependent l0.
      induction l; destruct l0; prog.
      apply IHl; auto.
Qed.

(* Disallow unfolding V. Always use V_eq to turn it into V' *)
Opaque V.
Arguments V : simpl never.

Notation R := (R' V).

Notation E := (E' V).

Hint Extern 1 =>
       (match goal with
        | [H : V _ (Vconstr _ _) _ |- _] => rewrite V_eq in H; unfold V' in H
        | [H : V _ _ (Vconstr _ _) |- _] => rewrite V_eq in H; unfold V' in H
        | [H : V _ (Vfun _ _ _ _) _ |- _] => rewrite V_eq in H; unfold V' in H
        | [H : V _ _ (Vfun _ _ _ _) |- _] => rewrite V_eq in H; unfold V' in H
        | [ |- V _ (Vconstr _ _) _ ] => rewrite V_eq; unfold V'
        | [ |- V _ _ (Vconstr _ _) ] => rewrite V_eq; unfold V'
        | [ |- V _ (Vfun _ _ _ _) _] => rewrite V_eq; unfold V'
        | [ |- V _ _ (Vfun _ _ _ _)] => rewrite V_eq; unfold V'
        | [ |- R _ OOT _] => simpl
        | [ |- R _ _ OOT] => simpl
        | [ H : R _ OOT _ |- _] => simpl in H
        | [ H : R _ _ OOT |- _] => unfold R, R' in H
        | [ |- R _ (Res _) _] => simpl
        | [ |- R _ _ (Res _)] => simpl
        | [ H : R _ (Res _) _ |- _] => simpl in H
        | [ H : R _ _ (Res _) |- _] => unfold R, R' in H
        end; shelve) : custom_automation.

(* Environment Relation *)
Definition G i Γ ρ1 ρ2 :=
  forall x,
    (x \in Γ) ->
    forall v1,
      M.get x ρ1 = Some v1 ->
      exists v2,
        M.get x ρ2 = Some v2 /\
        V i v1 v2.

Definition related e1 e2 :=
  forall i ρ1 ρ2,
    G i (occurs_free e1) ρ1 ρ2 ->
    E i ρ1 e1 ρ2 e2.

(* Environment Lemmas *)
Lemma G_set {i Γ ρ1 ρ2}:
  G i Γ ρ1 ρ2 ->
  forall {x v1 v2},
    V i v1 v2 ->
    G i (x |: Γ) (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  intros HG; prog.
  intro.
  destruct (M.elt_eq x0 x); prog.
  - eexists; eauto; prog.
  - inv H0; prog.
Qed.

Lemma G_set_lists {i Γ ρ1 ρ2}:
  G i Γ ρ1 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 (V i) vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    G i (FromList xs :|: Γ) ρ3 ρ4.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    inv H0; inv H1.
    eapply HG; eauto.
    prog.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
    inv H; inv H0; inv H1.
    destruct (M.elt_eq x a); prog.
    + eexists; prog.
    + eapply IHxs; eauto.
      rewrite <- Union_assoc in H2.
      inv H2; prog.
Qed.

Lemma G_get {i Γ ρ1 ρ2 x v1}:
  G i Γ ρ1 ρ2 ->
  M.get x ρ1 = Some v1 ->
  (x \in Γ) ->
  exists v2,
    M.get x ρ2 = Some v2 /\
    V i v1 v2.
Proof.
  unfold G; prog.
Qed.

Lemma G_get_list {i Γ ρ1 ρ2 xs vs1} :
  G i Γ ρ1 ρ2 ->
  get_list xs ρ1 = Some vs1 ->
  (FromList xs \subset Γ) ->
  exists vs2,
    get_list xs ρ2 = Some vs2 /\
    Forall2 (V i) vs1 vs2.
Proof.
  unfold G.
  intros HG H_get_list H_subset.
  revert vs1 H_get_list.
  induction xs; prog; simpl.
  - eexists; prog.
  - edestruct HG as [v2 ?]; eauto; prog.
    edestruct IHxs as [vs2 ?]; eauto.
    eexists; prog.
Qed.

(* Monotonicity Lemmas *)
Lemma V_mono i :
  forall {j v1 v2},
    V i v1 v2 ->
    j <= i ->
    V j v1 v2.
Proof.
  intros.
  generalize dependent v2.
  induction v1 using val_ind''; prog.
  - eapply H1; eauto; prog.
  - generalize dependent l.
    induction vs; prog.
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

Lemma G_subset Γ1 Γ2 i ρ1 ρ2:
  G i Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  G i Γ2 ρ1 ρ2.
Proof.
  unfold G.
  intros.
  eapply H; prog.
Qed.

(* Compatibility Lemmas *)
Lemma ret_compat x :
  related (Eret x) (Eret x).
Proof.
  unfold related, E, E'.
  intros.
  inv H1; prog.
  - exists 0; eexists; prog; eauto.
  - inv H2.
    edestruct (G_get H H3) as [v2 ?]; eauto; prog.
    eexists (S _); eexists (Res _); prog; eauto; prog.
    eapply V_mono; eauto; prog.
Qed.

Lemma constr_compat {k} x t xs :
  related k k ->
  related (Econstr x t xs k) (Econstr x t xs k).
Proof.
  unfold related, E, E'.
  intros.
  inv H2; prog.
  - exists 0; eexists; prog.
  - inv H3.
    destruct (G_get_list H0 H9) as [vs' ?]; prog.
    eapply free_constr_xs_subset.
    assert (length vs = length vs').
    {
      rewrite <- (get_list_length_eq _ _ _ H9).
      rewrite <- (get_list_length_eq _ _ _ H2); auto.
    }

    edestruct (H i (M.set x (Vconstr t vs) ρ1) (M.set x (Vconstr t vs') ρ2)) with (j1 := c) as [j2 [r2 ?]]; eauto; prog.
    + eapply G_subset; eauto.
      eapply G_set; prog.
      eauto.
      eapply free_constr_k_subset.
    + eexists (S _); exists r2; prog; eauto; prog.
      eapply R_mono; try exact H6; prog.
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
  induction i; prog.
  eapply He.
  eapply G_subset; eauto.
  eapply G_set_lists; eauto.
  apply G_set.
  - apply G_mono with (S i); auto; lia.
  - apply V_mono with i; try lia.
    eapply IHi; eauto.
    apply G_mono with (S i); auto; lia.
Qed.

Lemma fun_compat {e k e' k'} f xs :
  related e e' ->
  related k k' ->
  related (Efun f xs e k) (Efun f xs e' k').
Proof.
  unfold related, E, E'.
  intros.
  inv H3.
  - exists 0; eexists; prog.
  - edestruct (H0 (i - 1) (M.set f (Vfun f ρ1 xs e) ρ1) (M.set f (Vfun f ρ2 xs e') ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 ?]]; eauto; try lia.
    + eapply G_subset; eauto.
      eapply G_set; eauto.
      * eapply G_mono with i; eauto; lia.
      * eapply Vfun_V; eauto; prog.
        eapply G_mono; eauto; prog.
        eapply free_fun_e_subset.
      * eapply free_fun_k_subset.
    + inv H4.
      prog.
    + eexists (S _), r2; prog; eauto.
      eapply R_mono; eauto; prog.
Qed.

Lemma app_compat f xs :
  related (Eapp f xs) (Eapp f xs).
Proof.
  unfold related, E, E'.
  intros.
  inv H1.
  - exists 0; eexists; prog.
  - inv H2.
    edestruct (G_get H H4) as [v2 ?]; eauto; prog.
    (* destruct i; prog. *)
    destruct (G_get_list H H5) as [vs2 ?]; eauto; prog.
    eapply free_app_xs_subset.
    destruct (set_lists_length3 (M.set v (Vfun v t l e0) t) l vs2) as [ρ4 ?].
    {
    rewrite <- (Forall2_length _ _ _ H8).
    rewrite <- (set_lists_length_eq _ _ _ _ H6).
    erewrite eq_sym; eauto.
    }

    assert (HE : E (i - 1) ρ'' e ρ4 e0).
    {
      eapply (H3 (i - 1) vs vs2); eauto; prog.
      eapply V_mono_Forall; eauto; prog.
    }

    unfold E, E' in HE.
    edestruct (HE c r1) as [j2 [r2 ?]]; eauto; prog.
    exists (S j2), r2; prog; eauto; prog.
    eapply R_mono; eauto; prog.
Qed.

Lemma proj_compat x i y e e':
  related e e' ->
  related (Eproj x i y e) (Eproj x i y e').
Proof.
  unfold related, E, E'.
  intros.
  inv H2.
  - exists 0; eexists; prog.
  - inv H3.
    edestruct (G_get H0 H9) as [v2 ?]; eauto; prog.
    rename l into vs'.
    destruct (Forall2_nth_error H10 H4) as [v' ?]; prog.
    edestruct (H i0 (M.set x v ρ1) (M.set x v' ρ2)) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
    + eapply G_subset; eauto.
      eapply G_set; eauto; prog.
      eapply free_proj_k_subset.
    + exists (S j2), r2; prog; eauto; prog.
      eapply R_mono; eauto; prog.
Qed.

Lemma letapp_compat {k k'} x f xs :
  related k k' ->
  related (Eletapp x f xs k) (Eletapp x f xs k').
Proof.
  intros.
  specialize (app_compat f xs); intros Ha.
  unfold related, E, E' in *.
  intros.
  assert (HGa : G i (occurs_free (Eapp f xs)) ρ1 ρ2).
  {
    eapply G_subset; eauto; prog.
    intro; intros.
    inv H3.
    - eapply Free_letapp2.
    - eapply Free_letapp3; auto.
  }
  specialize (Ha _ _ _ HGa).
  inv H2.
  - exists 0; eexists; prog.
  - inv H3.
    destruct (Ha (S c0) (Res v)) as [j1 [ra [Hbstep HR]]]; try lia; eauto.
    prog.
    destruct ra; try contradiction.
    edestruct (H (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 ?]]; eauto; try lia; prog.
    + eapply (G_subset (x |: occurs_free (Eletapp x f xs k))); eauto.
      eapply G_set; prog.
      eapply G_mono; eauto; prog.
      eapply free_letapp_k_subset.
    + exists (j1 + j2), r2; split.
      ++ inv Hbstep.
         inv H4.
         rewrite_math ((S c + j2) = S (c + j2)); eauto.
      ++ eapply R_mono; eauto; prog.
    + eexists; eexists; split; eauto.
      unfold R; simpl; auto.
Qed.

Lemma case_nil_compat x:
  related (Ecase x []) (Ecase x []).
Proof.
  unfold related, G, E, E', R'.
  prog.
  inv H1; fcrush.
Qed.

Lemma case_cons_compat e e' x cl cl' c:
  related e e' ->
  related (Ecase x cl) (Ecase x cl') ->
  related (Ecase x ((c, e) :: cl)) (Ecase x ((c, e') :: cl')).
Proof.
  unfold related, E, E'.
  prog.
  inv H3.
  - fcrush.
  - inv H4.
    edestruct (G_get H1 H6) as [v2 ?]; eauto; prog.
    inv H7.
    + edestruct (H i ρ1 ρ2) with (j1 := c0) as [j2 [r2 ?]]; eauto; prog.
      eapply G_subset; eauto; prog.
      eapply free_case_hd_subset.
      exists (S j2), r2; prog; eauto; prog.
      eapply R_mono; eauto; prog.
    + edestruct (H0 i ρ1 ρ2) with (j1 := S c0) (r1 := r1) as [j2 [r2 ?]]; eauto; prog; eauto.
      eapply G_subset; eauto; prog.
      eapply free_case_tl_subset.
      destruct j2.
      * fcrush.
      * exists (S j2); eexists.
        split; eauto.
        econstructor; eauto.
        inv H4.
        inv H11.
        econstructor; eauto.
        econstructor; eauto.
        prog.
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

(* Reflexivity *)
Lemma refl_V_G :
  forall i,
    (forall k : nat, k < S i -> forall v : val, V k v v) ->
    forall ρ,
      forall xs Γ j vs1 vs2 ρ1 ρ2,
        j <= i ->
        Forall2 (V j) vs1 vs2 ->
        set_lists xs vs1 ρ = Some ρ1 ->
        set_lists xs vs2 ρ = Some ρ2 ->
        G j Γ ρ1 ρ2.
Proof.
  unfold G.
  intros i HI ρ xs.
  induction xs; prog.
  - eexists; prog; eauto.
    eapply HI; prog.
  - destruct (M.elt_eq x a); prog.
    + eexists; prog.
    + edestruct IHxs as [v2 ?]; eauto; prog.
Qed.

Lemma refl_V_ForallV :
  forall i,
    (forall k : nat, k < S i -> forall v : val, V k v v) ->
    forall vs j,
      j <= i ->
      Forall2 (V j) vs vs.
Proof.
  intros i HI vs.
  induction vs; simpl; prog.
  eapply HI; eauto; try lia.
Qed.

Theorem refl_V :
  forall i v, V i v v.
Proof.
  intros i.
  induction i using lt_wf_rec.
  induction v using val_ind''; prog.
  - eapply fundamental_property.
    eapply refl_V_G with (ρ := (M.set f (Vfun f ρ xs e) ρ)); eauto.
    intros.
    eapply H; prog.
  - induction vs; prog.
Qed.

Corollary refl_V_Forall vs :
  forall i, Forall2 (V i) vs vs.
Proof.
  intros i.
  induction vs; prog.
  eapply refl_V; prog.
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
  forall i ρ e, E i ρ e ρ e.
Proof.
  unfold E, E'.
  intros.
  exists j1, r1; prog.
  apply refl_R; auto.
Qed.

Theorem refl_G :
  forall i Γ ρ, G i Γ ρ ρ.
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
  forall {vs1},
    forall {vs2 vs3},
      Forall2 (V i) vs1 vs2 ->
      (forall i, Forall2 (V i) vs2 vs3) ->
      Forall2 (V i) vs1 vs3.
Proof.
  intros IH vs1.
  induction vs1; simpl; intros.
  - inv H.
    eapply H0; eauto.
  - inv H.
    pose proof (H0 i) as H2'.
    inv H2'.
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
  induction i using lt_wf_rec1.
  induction v1 using val_ind''; prog.
  - pose proof (H1 i); prog.
    assert (length l = length vs2) by (rewrite H3; eapply set_lists_length_eq; eauto).
    destruct (set_lists_length3 (M.set v (Vfun v t l e0) t) _ _ H9) as [ρ5 ?].

    assert (length vs2 = length vs1) by (eapply eq_sym; eapply Forall2_length; eauto).
    edestruct (set_lists_length _ (M.set v (Vfun v t l e0) t) _ _ _ _ H11 H6) as [ρ6 ?].

    eapply trans_E_aux; eauto.
    + prog.
      eapply H; eauto; prog.
    + intro i0.
      specialize (H1 (S i0)); prog.
      specialize (H13 i0 vs2 vs2).
      eapply H13; eauto; prog.
      eapply refl_V_Forall; prog.
  - pose proof (H2 i); prog.
    (* clear H1 H3 H4 H5. *)
    generalize dependent l0.
    generalize dependent l.
    revert H0.
    induction vs; prog.
    + eapply H6; eauto; prog.
      specialize (H2 i0); prog.
    + eapply IHvs; eauto; prog.
      specialize (H2 i0); prog.
Qed.

Corollary trans_R {i r1 r2 r3} :
  R i r1 r2 ->
  (forall k, R k r2 r3) ->
  R i r1 r3.
Proof.
  unfold R, R'.
  intros.
  destruct r1; destruct r2; destruct r3; prog.
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
Definition G_top i Γ1 ρ1 ρ2 :=
  forall x,
    (x \in Γ1) ->
    exists v1 v2,
      M.get x ρ1 = Some v1 /\
      M.get x ρ2 = Some v2 /\
      V i v1 v2.

Lemma G_top_G : forall {i Γ1 ρ1 ρ2},
    G_top i Γ1 ρ1 ρ2 ->
    G i Γ1 ρ1 ρ2.
Proof.
  unfold G_top, G; prog.
  unfold Ensembles.Included, Ensembles.In, Dom_map in *; prog.
  edestruct H as [v1' [v2 ?]]; eauto; prog.
  eexists; prog; eauto.
Qed.

Definition related_top etop etop' :=
  occurs_free etop' \subset occurs_free etop /\
  forall i ρ1 ρ2,
    G_top i (occurs_free etop) ρ1 ρ2 ->
    E i ρ1 etop ρ2 etop'.

Theorem top etop:
  related_top etop etop.
Proof.
  unfold related_top; prog.
  eapply fundamental_property.
  eapply G_top_G; eauto.
Qed.

(* Reflexivity of [related_top] *)
Corollary refl_related_top :
  Reflexive related_top.
Proof.
  unfold related_top, Reflexive; prog.
  eapply fundamental_property.
  eapply G_top_G; eauto.
Qed.

(* Transitivity of [related_top] *)
Theorem trans_related_top :
  Transitive related_top.
Proof.
  intros e1 e2 e3.
  unfold related_top, G_top; prog.
  - eapply Included_trans; eauto.
  - eapply trans_E; eauto; prog.
    unfold Ensembles.Included, Ensembles.In in *.
    eapply H1; prog.
    edestruct H3 as [v1 [v2 ?]]; eauto; prog.
    eexists; eexists; prog; eauto; prog.
    eapply refl_V; prog.
Qed.

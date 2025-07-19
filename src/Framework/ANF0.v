From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

Require Import Framework.Util.

(* Untyped λANF without Web Annotations *)

Module M := Maps.PTree.
Definition var := M.elt.
Definition vars := Ensemble var.
Definition ctor_tag := M.elt.

(* Syntax *)
Inductive exp : Type :=
| Eret : var -> exp
| Eapp : var -> list var -> exp
| Eletapp : var -> var -> list var -> exp -> exp
| Efun : var -> list var -> exp -> exp -> exp
| Econstr : var -> ctor_tag -> list var -> exp -> exp
| Ecase : var -> list (ctor_tag * exp) -> exp
| Eproj : var -> nat -> var -> exp -> exp.

Hint Constructors exp : core.

Lemma exp_ind' :
  forall P : exp -> Type,
    (forall (x : var), P (Eret x)) ->
    (forall (x : var) (xs : list var), P (Eapp x xs)) ->
    (forall f xs (e k : exp), P e -> P k -> P (Efun f xs e k)) ->
    (forall (x f : var) (xs : list var) (e : exp),
        P e -> P (Eletapp x f xs e)) ->
    (forall (x : var) (c : ctor_tag) (xs : list var) (e : exp),
        P e -> P (Econstr x c xs e)) ->
    (forall (x : var), P (Ecase x nil)) ->
    (forall (x : var) (cl : list (ctor_tag * exp)) (c : ctor_tag) (e : exp),
        P e -> P (Ecase x cl) -> P (Ecase x ((c, e) :: cl))) ->
    (forall (x : var) (n : nat) (v0 : var) (e : exp),
        P e -> P (Eproj x n v0 e)) ->
    forall e : exp, P e.
Proof.
  intros P H1 H2 H3 H4 H5 H6 H7 H8.
  fix exp_ind' 1.
  destruct e; try (now clear exp_ind'; eauto).
  - eapply H4; eapply exp_ind'; eauto.
  - eapply H3; eapply exp_ind'; eauto.
  - eapply H5. eapply exp_ind'; eauto.
  - induction l.
    + eapply H6.
    + destruct a.
      eapply H7.
      eapply exp_ind'; eauto.
      apply IHl.
  - eapply H8. eapply exp_ind'; eauto.
Qed.

(* Value *)
Inductive val : Type :=
| Vfun : var -> M.t val -> list var -> exp -> val
| Vconstr : ctor_tag -> list val -> val.

Hint Constructors val : core.

(* Environment *)
Definition env := M.t val.

(* Result *)
Inductive res : Type :=
| OOT
| Res : val -> res.

Hint Constructors res : core.

(* Big-step Semantics *)
Definition fuel := nat.

Inductive find_tag : list (ctor_tag * exp) -> ctor_tag -> exp -> Prop :=
| find_tag_hd :
  forall c e l,
    find_tag ((c, e) :: l) c e

| find_tag_tl :
  forall c e l c' e',
    find_tag l c' e' ->
    c <> c' ->
    find_tag ((c, e) :: l) c' e'.

Hint Constructors find_tag : core.

Inductive bstep (ρ : env) : exp -> fuel -> res -> Prop :=
| BStep_ret :
  forall {x v},
    M.get x ρ = Some v ->
    bstep ρ (Eret x) 0 (Res v)

| BStep_fun :
  forall {f xs e k c r},
    bstep_fuel (M.set f (Vfun f ρ xs e) ρ) k c r ->
    bstep ρ (Efun f xs e k) c r

| BStep_app :
  forall {f f' xs ρ' xs' e vs ρ'' c r},
    M.get f ρ = Some (Vfun f' ρ' xs' e) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Vfun f' ρ' xs' e) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c r ->
    bstep ρ (Eapp f xs) c r

| BStep_letapp_Res :
  forall {x f f' xs k ρ' xs' e vs ρ'' c c' v r},
    M.get f ρ = Some (Vfun f' ρ' xs' e) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Vfun f' ρ' xs' e) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c (Res v) ->
    bstep_fuel (M.set x v ρ) k c' r ->
    bstep ρ (Eletapp x f xs k) (c + c') r

| BStep_letapp_OOT :
  forall {x f f' xs k ρ' xs' e vs ρ'' c},
    M.get f ρ = Some (Vfun f' ρ' xs' e) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Vfun f' ρ' xs' e) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c OOT ->
    bstep ρ (Eletapp x f xs k) c OOT

| BStep_constr :
  forall {x t xs e r vs c},
    get_list xs ρ = Some vs ->
    bstep_fuel (M.set x (Vconstr t vs) ρ) e c r ->
    bstep ρ (Econstr x t xs e) c r

| BStep_proj :
  forall {x t i y e c r v vs},
    M.get y ρ = Some (Vconstr t vs) ->
    nth_error vs i = Some v ->
    bstep_fuel (M.set x v ρ) e c r ->
    bstep ρ (Eproj x i y e) c r

| BStep_case :
  forall {x cl t e r c vs},
    M.get x ρ = Some (Vconstr t vs) ->
    find_tag cl t e ->
    bstep_fuel ρ e c r ->
    bstep ρ (Ecase x cl) c r

with bstep_fuel (ρ : env) : exp -> fuel -> res -> Prop :=
| BStepF_OOT :
  forall {e},
    bstep_fuel ρ e 0 OOT

| BStepF_Step :
  forall {e c r},
    bstep ρ e c r ->
    bstep_fuel ρ e (S c) r.

Hint Constructors bstep : core.
Hint Constructors bstep_fuel : core.

Scheme bstep_ind' := Minimality for bstep Sort Prop
with bstep_fuel_ind' := Minimality for bstep_fuel Sort Prop.

Lemma find_tag_deterministic {cl c e e'} :
  find_tag cl c e ->
  find_tag cl c e' ->
  e = e'.
Proof.
  intros H. revert e'.
  induction H; intros.
  - inv H; auto.
    contradiction.
  - inv H1; auto.
    contradiction.
Qed.

(* TODO: refactor *)
Theorem bstep_deterministic v v' {ρ e c c' r r'}:
    bstep ρ e c r ->
    bstep ρ e c' r' ->
    r = Res v ->
    r' = Res v' ->
    (v = v' /\ c = c').
Proof.
  intros H.
  generalize dependent v'.
  generalize dependent r'.
  generalize dependent c'.
  generalize dependent v.
  induction H using bstep_ind' with (P := fun ρ e c r =>
                                            forall v c' r' v',
                                              bstep ρ e c' r' ->
                                              r = Res v -> r' = Res v' ->
                                              v = v' /\ c = c')
                                    (P0 := fun ρ e c r =>
                                             forall v c' r' v',
                                               bstep_fuel ρ e c' r' ->
                                               r = Res v -> r' = Res v' ->
                                               v = v' /\ c = c');
    intros; subst.
  - inv H0; inv H1.
    rewrite H in H5; inv H5; auto.
  - inv H0.
    edestruct IHbstep; eauto.
  - inv H3.
    rewrite H in H6; inv H6.
    rewrite H0 in H7; inv H7.
    rewrite H1 in H8; inv H8.
    edestruct IHbstep; eauto.
  - inv H4.
    rewrite H in H9; inv H9.
    rewrite H0 in H10; inv H10.
    rewrite H1 in H13; inv H13.
    edestruct IHbstep; eauto.
    subst.
    edestruct IHbstep0; eauto.
  - inv H4.
  - inv H1.
    rewrite H in H8; inv H8.
    edestruct IHbstep; eauto.
  - inv H2.
    rewrite H in H9; inv H9.
    rewrite H0 in H10; inv H10.
    edestruct IHbstep; eauto.
  - inv H2.
    rewrite H in H5; inv H5.
    destruct (find_tag_deterministic H0 H6); subst.
    edestruct IHbstep; eauto.
  - inv H0.
  - inv H0.
    edestruct IHbstep; eauto.
Qed.

Theorem bstep_fuel_deterministic v v' {ρ e c c' r r'}:
    bstep_fuel ρ e c r ->
    bstep_fuel ρ e c' r' ->
    r = Res v ->
    r' = Res v' ->
    (v = v' /\ c = c').
Proof.
  intros.
  inv H; inv H0; try discriminate.
  edestruct (bstep_deterministic v v' H3 H); eauto.
Qed.

(* Free Variables *)
Inductive occurs_free : exp -> vars :=
| Free_ret :
  forall x,
    occurs_free (Eret x) x

| Free_fun1 :
  forall x f xs e k,
    f <> x ->
    occurs_free k x ->
    occurs_free (Efun f xs e k) x

| Free_fun2 :
  forall x f xs e k,
    f <> x ->
    ~ (List.In x xs) ->
    occurs_free e x ->
    occurs_free (Efun f xs e k) x

| Free_app1 :
  forall f xs,
    occurs_free (Eapp f xs) f

| Free_app2 :
  forall x f xs,
    List.In x xs ->
    occurs_free (Eapp f xs) x

| Free_letapp1 :
  forall y x f xs k,
    x <> y ->
    occurs_free k y ->
    occurs_free (Eletapp x f xs k) y

| Free_letapp2 :
  forall x f xs k,
    occurs_free (Eletapp x f xs k) f

| Free_letapp3 :
  forall y x f xs k,
    List.In y xs ->
    occurs_free (Eletapp x f xs k) y

| Free_constr1 :
  forall y x xs t k,
    List.In y xs ->
    occurs_free (Econstr x t xs k) y

| Free_constr2 :
  forall y x t xs k,
    y <> x ->
    occurs_free k y ->
    occurs_free (Econstr x t xs k) y

| Free_proj1 :
  forall y x i e,
    occurs_free (Eproj x i y e) y

| Free_proj2 :
  forall y x z i e,
    x <> y ->
    occurs_free e y ->
    occurs_free (Eproj x i z e) y

| Free_case1 :
  forall y cl,
    occurs_free (Ecase y cl) y

| Free_case2 :
  forall y x c e cl,
    occurs_free e y ->
    occurs_free (Ecase x ((c, e) :: cl)) y

| Free_case3 :
  forall y x c e cl,
    occurs_free (Ecase x cl) y ->
    occurs_free (Ecase x ((c, e) :: cl)) y.

Hint Constructors occurs_free : core.

(* Lemmas related to [occurs_free] *)
Lemma free_constr_k_subset k x xs t :
  (occurs_free k) \subset (x |: occurs_free (Econstr x t xs k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    eapply Free_constr2; eauto.
Qed.

Lemma free_constr_k_inv {x t xs k Γ} :
  occurs_free (Econstr x t xs k) \subset Γ ->
  occurs_free k \subset (x |: Γ).
Proof.
  intros.
  eapply Included_trans.
  eapply free_constr_k_subset.
  apply Included_Union_compat; eauto.
  apply Included_refl.
Qed.

Lemma free_constr_xs_subset x t xs e :
  FromList xs \subset occurs_free (Econstr x t xs e).
Proof.
  unfold Ensembles.Included, Ensembles.In, FromList.
  intros; auto.
Qed.

Lemma free_proj_k_subset k x i y :
  (occurs_free k) \subset (x |: occurs_free (Eproj x i y k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    eapply Free_proj2; eauto.
Qed.

Lemma free_proj_k_inv {x i y k Γ} :
  occurs_free (Eproj x i y k) \subset Γ ->
  occurs_free k \subset (x |: Γ).
Proof.
  intros.
  eapply Included_trans.
  eapply free_proj_k_subset.
  apply Included_Union_compat; eauto.
  apply Included_refl.
Qed.

Lemma free_fun_e_subset k f e : forall xs,
  (occurs_free e) \subset (FromList xs :|: (f |: occurs_free (Efun f xs e k))).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (in_dec M.elt_eq x xs).
  - apply Union_introl; auto.
  - apply Union_intror; auto.
    unfold Ensembles.In.
    destruct (M.elt_eq f x); subst.
    + apply Union_introl; auto.
    + apply Union_intror.
      unfold Ensembles.In.
      apply Free_fun2; auto.
Qed.

Lemma free_fun_k_subset k f xs e :
  (occurs_free k) \subset (f |: occurs_free (Efun f xs e k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq f x); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    constructor; auto.
Qed.

Lemma free_fun_e_inv {e xs f k Γ} :
  occurs_free (Efun f xs e k) \subset Γ ->
  occurs_free e \subset FromList xs :|: (f |: Γ).
Proof.
  intros.
  eapply Included_trans; eauto.
  eapply free_fun_e_subset; eauto.
  apply Included_Union_compat.
  apply Included_refl.
  apply Included_Union_compat; eauto.
  apply Included_refl.
Qed.

Lemma free_fun_k_inv {e xs f k Γ} :
  occurs_free (Efun f xs e k) \subset Γ ->
  occurs_free k \subset (f |: Γ).
Proof.
  intros.
  eapply Included_trans; eauto.
  eapply free_fun_k_subset; eauto.
  apply Included_Union_compat; eauto.
  apply Included_refl.
Qed.

Lemma free_app_xs_subset xs f :
  FromList xs \subset occurs_free (Eapp f xs).
Proof.
  unfold Ensembles.Included, Ensembles.In, FromList.
  intros; auto.
Qed.

Lemma free_letapp_k_subset f x xs k :
  (occurs_free k) \subset (x |: occurs_free (Eletapp x f xs k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq x x0); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    constructor; auto.
Qed.

Lemma free_letapp_k_inv {x f xs k Γ} :
  occurs_free (Eletapp x f xs k) \subset Γ ->
  occurs_free k \subset x |: Γ.
Proof.
  intros.
  eapply Included_trans.
  eapply free_letapp_k_subset.
  apply Included_Union_compat; eauto.
  apply Included_refl.
Qed.

Lemma free_letapp_xs_subset x f xs k :
  FromList xs \subset occurs_free (Eletapp x f xs k).
Proof.
  unfold Ensembles.Included, Ensembles.In, FromList.
  intros; auto.
Qed.

Lemma free_case_hd_subset e x c cl :
  occurs_free e \subset occurs_free (Ecase x ((c, e) :: cl)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros; auto.
Qed.

Lemma free_case_tl_subset x c e cl :
  occurs_free (Ecase x cl) \subset occurs_free (Ecase x ((c, e) :: cl)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros; auto.
Qed.

Lemma free_case_e_inv x Γ e t cl :
  occurs_free (Ecase x cl) \subset Γ ->
  find_tag cl t e ->
  occurs_free e \subset Γ.
Proof.
  unfold Ensembles.Included, Ensembles.In.
  induction cl; simpl; intros; inv H0.
  - apply H; auto.
  - apply IHcl; auto.
Qed.

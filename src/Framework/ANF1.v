From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

Require Import Framework.Util.

(* Untyped λANF with labels instead of web constraints *)

Module M := Maps.PTree.
Definition var := M.elt.
Definition vars := Ensemble var.
Definition ctor_tag := M.elt.
Definition label := M.elt.
Definition labels := Ensemble label.
(* Definition next_label l : label := Pos.succ l. *)

(* Syntax *)
Inductive exp : Type :=
| Eret : var -> exp
| Eapp : var -> label -> list var -> exp
| Eletapp : var -> var -> label -> list var -> exp -> exp
| Efun : var -> label -> list var -> exp -> exp -> exp
| Econstr : var -> label -> ctor_tag -> list var -> exp -> exp
| Ecase : var -> label -> list (ctor_tag * exp) -> exp
| Eproj : var -> label -> nat -> var -> exp -> exp.

Hint Constructors exp : core.

Lemma exp_ind' :
  forall P : exp -> Type,
    (forall (x : var), P (Eret x)) ->
    (forall (x : var) (w : label) (xs : list var), P (Eapp x w xs)) ->
    (forall f w xs (e k : exp), P e -> P k -> P (Efun f w xs e k)) ->
    (forall (x f : var) (w : label) (xs : list var) (e : exp),
        P e -> P (Eletapp x f w xs e)) ->
    (forall (x : var) w (c : ctor_tag) (xs : list var) (e : exp),
        P e -> P (Econstr x w c xs e)) ->
    (forall (x : var) w, P (Ecase x w nil)) ->
    (forall (x : var) w (cl : list (ctor_tag * exp)) (c : ctor_tag) (e : exp),
        P e -> P (Ecase x w cl) -> P (Ecase x w ((c, e) :: cl))) ->
    (forall (x : var) w (n : nat) (v0 : var) (e : exp),
        P e -> P (Eproj x w n v0 e)) ->
    forall e : exp, P e.
Proof.
  intros P H1 H2 H3 H4 H5 H6 H7 H8.
  fix exp_ind' 1.
  destruct e; try (now clear exp_ind'; eauto).
  - eapply H4; eapply exp_ind'; eauto.
  - eapply H3; eapply exp_ind'; eauto.
  - eapply H5. eapply exp_ind'; eauto.
  - induction l0.
    + eapply H6.
    + destruct a.
      eapply H7.
      eapply exp_ind'; eauto.
      apply IHl0.
  - eapply H8. eapply exp_ind'; eauto.
Qed.

(* Tagged Value *)
Inductive tag A : Type :=
| TAG : label -> A -> tag A.

Hint Constructors tag : core.

(* Value *)
Inductive val : Type :=
| Vfun : var -> M.t (tag val) -> list var -> exp -> val
| Vconstr : ctor_tag -> list (tag val) -> val.

Hint Constructors val : core.

Definition wval := tag val.

Definition Tag w v := TAG val w v.

(* Environment *)
Definition env := M.t wval.

(* Result *)
Inductive res : Type :=
| OOT
| Res : wval -> res.

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
  forall {x wv},
    M.get x ρ = Some wv ->
    bstep ρ (Eret x) 0 (Res wv)

| BStep_fun :
  forall {f w xs e k c r},
    bstep_fuel (M.set f (Tag w (Vfun f ρ xs e)) ρ) k c r ->
    bstep ρ (Efun f w xs e k) c r

| BStep_app :
  forall {f f' w xs ρ' xs' e vs ρ'' c r},
    M.get f ρ = Some (Tag w (Vfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w (Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c r ->
    bstep ρ (Eapp f w xs) c r

| BStep_letapp_Res :
  forall {x f f' w xs k ρ' xs' e vs ρ'' c c' v r},
    M.get f ρ = Some (Tag w (Vfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w (Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c (Res v) ->
    bstep_fuel (M.set x v ρ) k c' r ->
    bstep ρ (Eletapp x f w xs k) (c + c') r

| BStep_letapp_OOT :
  forall {x f f' w xs k ρ' xs' e vs ρ'' c},
    M.get f ρ = Some (Tag w (Vfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w (Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c OOT ->
    bstep ρ (Eletapp x f w xs k) c OOT

| BStep_constr :
  forall {x w t xs e r vs c},
    get_list xs ρ = Some vs ->
    bstep_fuel (M.set x (Tag w (Vconstr t vs)) ρ) e c r ->
    bstep ρ (Econstr x w t xs e) c r

| BStep_proj :
  forall {x w t i y e c r v vs},
    M.get y ρ = Some (Tag w (Vconstr t vs)) ->
    nth_error vs i = Some v ->
    bstep_fuel (M.set x v ρ) e c r ->
    bstep ρ (Eproj x w i y e) c r

| BStep_case :
  forall {x w cl t e r c vs},
    M.get x ρ = Some (Tag w (Vconstr t vs)) ->
    find_tag cl t e ->
    bstep_fuel ρ e c r ->
    bstep ρ (Ecase x w cl) c r

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
    rewrite H in H7; inv H7.
    rewrite H0 in H8; inv H8.
    rewrite H1 in H11; inv H11.
    edestruct IHbstep; eauto.
  - inv H4.
    rewrite H in H10; inv H10.
    rewrite H0 in H13; inv H13.
    rewrite H1 in H14; inv H14.
    edestruct IHbstep; eauto.
    subst.
    edestruct IHbstep0; eauto.
  - inv H4.
  - inv H1.
    rewrite H in H9; inv H9.
    edestruct IHbstep; eauto.
  - inv H2.
    rewrite H in H10; inv H10.
    rewrite H0 in H11; inv H11.
    edestruct IHbstep; eauto.
  - inv H2.
    rewrite H in H6; inv H6.
    destruct (find_tag_deterministic H0 H9); subst.
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
  forall x f w xs e k,
    f <> x ->
    occurs_free k x ->
    occurs_free (Efun f w xs e k) x

| Free_fun2 :
  forall x f w xs e k,
    f <> x ->
    ~ (List.In x xs) ->
    occurs_free e x ->
    occurs_free (Efun f w xs e k) x

| Free_app1 :
  forall f w xs,
    occurs_free (Eapp f w xs) f

| Free_app2 :
  forall x f w xs,
    List.In x xs ->
    occurs_free (Eapp f w xs) x

| Free_letapp1 :
  forall y x f w xs k,
    x <> y ->
    occurs_free k y ->
    occurs_free (Eletapp x f w xs k) y

| Free_letapp2 :
  forall x f w xs k,
    occurs_free (Eletapp x f w xs k) f

| Free_letapp3 :
  forall y x f w xs k,
    List.In y xs ->
    occurs_free (Eletapp x f w xs k) y

| Free_constr1 :
  forall y x xs t w k,
    List.In y xs ->
    occurs_free (Econstr x w t xs k) y

| Free_constr2 :
  forall y x w t xs k,
    y <> x ->
    occurs_free k y ->
    occurs_free (Econstr x w t xs k) y

| Free_proj1 :
  forall y x w i e,
    occurs_free (Eproj x w i y e) y

| Free_proj2 :
  forall y x z w i e,
    x <> y ->
    occurs_free e y ->
    occurs_free (Eproj x w i z e) y

| Free_case1 :
  forall y w cl,
    occurs_free (Ecase y w cl) y

| Free_case2 :
  forall y x w c e cl,
    occurs_free e y ->
    occurs_free (Ecase x w ((c, e) :: cl)) y

| Free_case3 :
  forall y x c e w cl,
    occurs_free (Ecase x w cl) y ->
    occurs_free (Ecase x w ((c, e) :: cl)) y.

Hint Constructors occurs_free : core.

(* Lemmas related to [occurs_free] *)
Lemma free_constr_k_subset k x xs t w :
  (occurs_free k) \subset (x |: occurs_free (Econstr x w t xs k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    eapply Free_constr2; eauto.
Qed.

Lemma free_constr_k_inv {x w t xs k Γ} :
  occurs_free (Econstr x w t xs k) \subset Γ ->
  occurs_free k \subset (x |: Γ).
Proof.
  intros.
  eapply Included_trans.
  eapply free_constr_k_subset.
  apply Included_Union_compat; eauto.
  apply Included_refl.
Qed.

Lemma free_constr_xs_subset x w t xs e :
  FromList xs \subset occurs_free (Econstr x w t xs e).
Proof.
  unfold Ensembles.Included, Ensembles.In, FromList.
  intros; auto.
Qed.

Lemma free_proj_k_subset k x i y w :
  (occurs_free k) \subset (x |: occurs_free (Eproj x w i y k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    eapply Free_proj2; eauto.
Qed.

Lemma free_proj_k_inv {x w i y k Γ} :
  occurs_free (Eproj x w i y k) \subset Γ ->
  occurs_free k \subset (x |: Γ).
Proof.
  intros.
  eapply Included_trans.
  eapply free_proj_k_subset.
  apply Included_Union_compat; eauto.
  apply Included_refl.
Qed.

Lemma free_fun_compat e' e k' k f w xs :
  occurs_free e' \subset occurs_free e ->
  occurs_free k' \subset occurs_free k ->
  occurs_free (Efun f w xs e' k') \subset occurs_free (Efun f w xs e k).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  inv H1; auto.
Qed.

Lemma free_fun_e_subset k f w e : forall xs,
  (occurs_free e) \subset (FromList xs :|: (f |: occurs_free (Efun f w xs e k))).
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

Lemma free_fun_k_subset k f w xs e :
  (occurs_free k) \subset (f |: occurs_free (Efun f w xs e k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq f x); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    constructor; auto.
Qed.

Lemma free_fun_e_inv {e w xs f k Γ} :
  occurs_free (Efun f w xs e k) \subset Γ ->
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

Lemma free_fun_k_inv {e w xs f k Γ} :
  occurs_free (Efun f w xs e k) \subset Γ ->
  occurs_free k \subset (f |: Γ).
Proof.
  intros.
  eapply Included_trans; eauto.
  eapply free_fun_k_subset; eauto.
  apply Included_Union_compat; eauto.
  apply Included_refl.
Qed.

Lemma free_app_xs_subset xs f w :
  FromList xs \subset occurs_free (Eapp f w xs).
Proof.
  unfold Ensembles.Included, Ensembles.In, FromList.
  intros; auto.
Qed.

Lemma free_app_letapp f w xs x k:
  occurs_free (Eapp f w xs) \subset occurs_free (Eletapp x f w xs k).
Proof.
  unfold Ensembles.Included.
  intros.
  inv H; auto.
Qed.

Lemma free_letapp_compat k' k x f w xs :
  occurs_free k' \subset occurs_free k ->
  occurs_free (Eletapp x f w xs k') \subset occurs_free (Eletapp x f w xs k).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  inv H0; auto.
Qed.

Lemma free_letapp_k_subset f x w xs k :
  (occurs_free k) \subset (x |: occurs_free (Eletapp x f w xs k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq x x0); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    constructor; auto.
Qed.

Lemma free_letapp_k_inv {x f w xs k Γ} :
  occurs_free (Eletapp x f w xs k) \subset Γ ->
  occurs_free k \subset x |: Γ.
Proof.
  intros.
  eapply Included_trans.
  eapply free_letapp_k_subset.
  apply Included_Union_compat; eauto.
  apply Included_refl.
Qed.

Lemma free_letapp_xs_subset x f w xs k :
  FromList xs \subset occurs_free (Eletapp x f w xs k).
Proof.
  unfold Ensembles.Included, Ensembles.In, FromList.
  intros; auto.
Qed.

Lemma free_case_hd_subset e x w c cl :
  occurs_free e \subset occurs_free (Ecase x w ((c, e) :: cl)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros; auto.
Qed.

Lemma free_case_tl_subset w x c e cl :
  occurs_free (Ecase x w cl) \subset occurs_free (Ecase x w ((c, e) :: cl)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros; auto.
Qed.

Lemma free_case_e_inv x w Γ e t cl :
  occurs_free (Ecase x w cl) \subset Γ ->
  find_tag cl t e ->
  occurs_free e \subset Γ.
Proof.
  unfold Ensembles.Included, Ensembles.In.
  induction cl; simpl; intros; inv H0.
  - apply H; auto.
  - apply IHcl; auto.
Qed.

(* Labels *)
Inductive has_label : exp -> labels :=
| Lab_fun1 :
  forall f l xs e k,
    has_label (Efun f l xs e k) l

| Lab_fun2 :
  forall f l0 l1 xs e k,
    has_label e l1 ->
    has_label (Efun f l0 xs e k) l1

| Lab_fun3 :
  forall f l0 l1 xs e k,
    has_label k l1 ->
    has_label (Efun f l0 xs e k) l1

| Lab_app1 :
  forall f l xs,
    has_label (Eapp f l xs) l

| Lab_letapp1 :
  forall x f l xs k,
    has_label (Eletapp x f l xs k) l

| Lab_letapp2 :
  forall x f l0 l1 xs k,
    has_label k l1 ->
    has_label (Eletapp x f l0 xs k) l1

| Lab_constr1 :
  forall x xs t l k,
    has_label (Econstr x l t xs k) l

| Lab_constr2 :
  forall x xs t l0 l1 k,
    has_label k l1 ->
    has_label (Econstr x l0 t xs k) l1

| Lab_proj1 :
  forall x l i y e,
    has_label (Eproj x l i y e) l

| Lab_proj2 :
  forall x l0 l1 i y e,
    has_label e l1 ->
    has_label (Eproj x l0 i y e) l1

| Lab_case1 :
  forall y l cl,
    has_label (Ecase y l cl) l

| Lab_case2 :
  forall y l0 l1 cl c e,
    has_label e l1 ->
    has_label (Ecase y l0 ((c, e) :: cl)) l1

| Lab_case3 :
  forall y l0 l1 cl c e,
    has_label (Ecase y l0 cl) l1 ->
    has_label (Ecase y l0 ((c, e) :: cl)) l1.

Hint Constructors has_label : core.

Inductive unique_label : exp -> Prop :=
| Unique_ret :
  forall {x},
    unique_label (Eret x)

| Unique_fun :
  forall {f xs e k l},
    (~ l \in has_label e) ->
    (~ l \in has_label k) ->
    Disjoint _ (has_label e) (has_label k) ->
    unique_label e ->
    unique_label k ->
    unique_label (Efun f l xs e k)

| Unique_app :
  forall {f xs l},
    unique_label (Eapp f l xs)

| Unique_letapp :
  forall {f x xs l k},
    (~ l \in has_label k) ->
    unique_label k ->
    unique_label (Eletapp x f l xs k)

| Unique_constr :
  forall {x t xs k l},
    (~ l \in has_label k) ->
    unique_label k ->
    unique_label (Econstr x l t xs k)

| Unique_proj :
  forall {x y k n l},
    (~ l \in has_label k) ->
    unique_label k ->
    unique_label (Eproj x l n y k)

| Unique_case_nil :
  forall {x l},
    unique_label (Ecase x l [])

| Unique_case_tl :
  forall {x l c e cl},
    (~ l \in has_label e) ->
    Disjoint _ (has_label e) (has_label (Ecase x l cl)) ->
    unique_label e ->
    unique_label (Ecase x l cl) ->
    unique_label (Ecase x l ((c , e) :: cl)).

Hint Constructors unique_label : core.

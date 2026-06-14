From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

(* untyped miniλANF based on λANF in CertiCoq *)

Module M := Maps.PTree.
Definition var := M.elt.
Definition vars := Ensemble var.
Definition web := M.elt.
Definition webs := Ensemble web.

Parameter Exposed : webs.

Parameter exposed_dec : Decidable Exposed.

Parameter exposedb : web -> bool.

Axiom exposed_reflect : forall w, Bool.reflect (w \in Exposed) (exposedb w).

(* Syntax *)
Inductive primitive : Type :=
| Ptrue
| Pfalse.

Hint Constructors primitive : core.

Inductive exp : Type :=
| Eret : var -> exp
| Eapp : var -> web -> list var -> exp
| Eletapp : var -> var -> web -> list var -> exp -> exp
| Efun : var -> web -> list var -> exp -> exp -> exp
| Eprim_val : var -> primitive -> exp -> exp
| Eif : var -> exp -> exp -> exp.

Hint Constructors exp : core.

(* Value *)
Inductive val : Type :=
| Vfun : var -> M.t val -> web -> list var -> exp -> val
| Vprim : primitive -> val.

Hint Constructors val : core.

(* Exposed Value *)
Inductive exposed : val -> Prop :=
| Exp_prim :
  forall p,
    exposed (Vprim p)

| Exp_fun :
  forall f ρ w xs e,
    w \in Exposed ->
    exposed (Vfun f ρ w xs e).

Hint Constructors exposed : core.

(* Environment *)
Definition env := M.t val.

(* Result *)
Inductive res : Type :=
| OOT
| Res : val -> res.

Hint Constructors res : core.

(* Exposed Result *)
Inductive exposed_res : res -> Prop :=
| Exp_OOT :
  exposed_res OOT

| Exp_Res :
  forall v,
    exposed v ->
    exposed_res (Res v).

Hint Constructors exposed_res : core.

Definition fuel := nat.

(* Big-step Reduction *)
Inductive bstep (ex : bool) : env -> exp -> fuel -> res -> Prop :=
| BStep_ret :
  forall {x v ρ},
    M.get x ρ = Some v ->
    bstep ex ρ (Eret x) 0 (Res v)

| BStep_fun :
  forall {ρ f w xs e k c r},
    bstep_fuel ex (M.set f (Vfun f ρ w xs e) ρ) k c r ->
    bstep ex ρ (Efun f w xs e k) c r

| BStep_app :
  forall {ρ f f' w xs ρ' xs' e vs ρ'' c r},
    M.get f ρ = Some (Vfun f' ρ' w xs' e) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Vfun f' ρ' w xs' e) ρ') = Some ρ'' ->
    bstep_fuel (exposedb w) ρ'' e c r ->
    (w \in Exposed -> Forall exposed vs /\ exposed_res r) ->
    bstep ex ρ (Eapp f w xs) c r

| BStep_letapp_Res :
  forall {ρ x f f' w xs k ρ' xs' e vs ρ'' c c' v r},
    M.get f ρ = Some (Vfun f' ρ' w xs' e) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Vfun f' ρ' w xs' e) ρ') = Some ρ'' ->
    bstep_fuel (exposedb w) ρ'' e c (Res v) ->
    (w \in Exposed -> Forall exposed vs /\ exposed v) ->
    bstep_fuel ex (M.set x v ρ) k c' r ->
    bstep ex ρ (Eletapp x f w xs k) (c + c') r

| BStep_letapp_OOT :
  forall {ρ x f f' w xs k ρ' xs' e vs ρ'' c},
    M.get f ρ = Some (Vfun f' ρ' w xs' e) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Vfun f' ρ' w xs' e) ρ') = Some ρ'' ->
    bstep_fuel (exposedb w) ρ'' e c OOT ->
    (w \in Exposed -> Forall exposed vs) ->
    bstep ex ρ (Eletapp x f w xs k) c OOT

| BStep_prim_val :
  forall {ρ x p k c r},
    bstep_fuel ex (M.set x (Vprim p) ρ) k c r ->
    bstep ex ρ (Eprim_val x p k) c r

| BStep_if_true :
  forall {ρ x t e c r},
    M.get x ρ = Some (Vprim Ptrue) ->
    bstep_fuel ex ρ t c r ->
    bstep ex ρ (Eif x t e) c r

| BStep_if_false :
  forall {ρ x t e c r},
    M.get x ρ = Some (Vprim Pfalse) ->
    bstep_fuel ex ρ e c r ->
    bstep ex ρ (Eif x t e) c r

with bstep_fuel (ex : bool) : env -> exp -> fuel -> res -> Prop :=
| BStepF_OOT :
  forall {ρ e},
    bstep_fuel ex ρ e 0 OOT

| BStepF_Step :
  forall {ρ e c r},
    bstep ex ρ e c r ->
    (if ex then exposed_res r else True) ->
    bstep_fuel ex ρ e (S c) r.

Hint Constructors bstep : core.
Hint Constructors bstep_fuel : core.

Scheme bstep_ind' := Minimality for bstep Sort Prop
with bstep_fuel_ind' := Minimality for bstep_fuel Sort Prop.

Theorem bstep_deterministic {ex ρ e c v c' v' r r'}:
    bstep ex ρ e c r ->
    bstep ex ρ e c' r' ->
    r = Res v ->
    r' = Res v' ->
    (v = v' /\ c = c').
Proof.
  intros H.
  generalize dependent v'.
  generalize dependent r'.
  generalize dependent c'.
  generalize dependent v.
  induction H using bstep_ind' with (P := fun ex ρ e c r =>
                                            forall v c' r' v',
                                              bstep ex ρ e c' r' ->
                                              r = Res v -> r' = Res v' ->
                                              v = v' /\ c = c')
                                    (P0 := fun ex ρ e c r =>
                                             forall v c' r' v',
                                               bstep_fuel ex ρ e c' r' ->
                                               r = Res v -> r' = Res v' ->
                                               v = v' /\ c = c');
    intros; subst.
  - inv H0; inv H1.
    rewrite H in H6; inv H6; auto.
  - inv H0.
    edestruct IHbstep as [Hv Hc]; eauto.
  - inv H4.
    rewrite H in H8; inv H8.
    rewrite H0 in H9; inv H9.
    rewrite H1 in H11; inv H11.
    edestruct IHbstep as [Hv Hc]; eauto.
  - inv H5.
    rewrite H in H11; inv H11.
    rewrite H0 in H13; inv H13.
    rewrite H1 in H16; inv H16.
    edestruct IHbstep as [Hv Hc]; eauto.
    subst.
    edestruct IHbstep0 as [Hvk Hck]; eauto.
  - inv H5.
  - inv H0.
    edestruct IHbstep as [Hv Hc]; eauto.
  - inv H1.
    + edestruct IHbstep as [Hv Hc]; eauto.
    + rewrite H in H8; inv H8.
  - inv H1.
    + rewrite H in H8; inv H8.
    + edestruct IHbstep as [Hv Hc]; eauto.
  - inv H0.
  - inv H1.
    edestruct IHbstep as [Hv Hc]; eauto.
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

| Free_prim_val :
  forall y x p k,
    y <> x ->
    occurs_free k y ->
    occurs_free (Eprim_val x p k) y

| Free_if1 :
  forall x t e,
    occurs_free (Eif x t e) x

| Free_if2 :
  forall y x t e,
    occurs_free t y ->
    occurs_free (Eif x t e) y

| Free_if3 :
  forall y x t e,
    occurs_free e y ->
    occurs_free (Eif x t e) y.

Hint Constructors occurs_free : core.

(* Lemmas related to [occurs_free] *)
Lemma free_prim_val_k_subset {k x p} :
  (occurs_free k) \subset (x |: occurs_free (Eprim_val x p k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    constructor; auto.
Qed.

Lemma free_prim_val_k_inv {x p k Γ} :
  occurs_free (Eprim_val x p k) \subset Γ ->
  occurs_free k \subset (x |: Γ).
Proof.
  intros.
  eapply Included_trans.
  eapply free_prim_val_k_subset.
  apply Included_Union_compat; eauto.
  apply Included_refl.
Qed.

Lemma free_fun_e_subset {k f w e} : forall {xs},
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

Lemma free_fun_k_subset {k f w xs e} :
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

Lemma free_letapp_k_subset {f x w xs k} :
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

Lemma free_if_t_subset {x t e} :
  (occurs_free t) \subset (occurs_free (Eif x t e)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros; eauto.
Qed.

Lemma free_if_e_subset {x t e} :
  (occurs_free e) \subset (occurs_free (Eif x t e)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros; eauto.
Qed.

Lemma free_if_t_inv {x t e Γ}:
  occurs_free (Eif x t e) \subset Γ ->
  occurs_free t \subset Γ.
Proof.
  intros.
  eapply Included_trans; eauto.
  eapply free_if_t_subset; eauto.
Qed.

Lemma free_if_e_inv {x t e Γ}:
  occurs_free (Eif x t e) \subset Γ ->
  occurs_free e \subset Γ.
Proof.
  intros.
  eapply Included_trans; eauto.
  eapply free_if_e_subset; eauto.
Qed.

(* Web Identifiers *)
Inductive has_web : exp -> webs :=
| Web_fun1 :
  forall f w xs e k,
    has_web (Efun f w xs e k) w

| Web_fun2 :
  forall w' f w xs e k,
    has_web e w' ->
    has_web (Efun f w xs e k) w'

| Web_fun3 :
  forall w' f w xs e k,
    has_web k w' ->
    has_web (Efun f w xs e k) w'

| Web_app :
  forall f w xs,
    has_web (Eapp f w xs) w

| Web_letapp1 :
  forall x f w xs k,
    has_web (Eletapp x f w xs k) w

| Web_letapp2 :
  forall w' x f w xs k,
    has_web k w' ->
    has_web (Eletapp x f w xs k) w'

| Web_prim_val :
  forall x p k w,
  has_web k w ->
  has_web (Eprim_val x p k) w

| Web_if1 :
  forall x t e w,
    has_web t w ->
    has_web (Eif x t e) w

| Web_if2 :
  forall x t e w,
    has_web e w ->
    has_web (Eif x t e) w.

Hint Constructors has_web : core.

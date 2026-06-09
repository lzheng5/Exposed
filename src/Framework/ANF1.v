From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Base Util.
Export Base.

(* Untyped λANF with labels instead of web constraints *)

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
  forall {f f' w w' xs ρ' xs' e vs ρ'' c r},
    M.get f ρ = Some (Tag w' (Vfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w' (Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c r ->
    bstep ρ (Eapp f w xs) c r

| BStep_letapp_Res :
  forall {x f f' w w' xs k ρ' xs' e vs ρ'' c c' v r},
    M.get f ρ = Some (Tag w' (Vfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w' (Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c (Res v) ->
    bstep_fuel (M.set x v ρ) k c' r ->
    bstep ρ (Eletapp x f w xs k) (c + c') r

| BStep_letapp_OOT :
  forall {x f f' w w' xs k ρ' xs' e vs ρ'' c},
    M.get f ρ = Some (Tag w' (Vfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w' (Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c OOT ->
    bstep ρ (Eletapp x f w xs k) c OOT

| BStep_constr :
  forall {x w t xs e r vs c},
    get_list xs ρ = Some vs ->
    bstep_fuel (M.set x (Tag w (Vconstr t vs)) ρ) e c r ->
    bstep ρ (Econstr x w t xs e) c r

| BStep_proj :
  forall {x w w' t i y e c r v vs},
    M.get y ρ = Some (Tag w' (Vconstr t vs)) ->
    nth_error vs i = Some v ->
    bstep_fuel (M.set x v ρ) e c r ->
    bstep ρ (Eproj x w i y e) c r

| BStep_case :
  forall {x w w' cl t e r c vs},
    M.get x ρ = Some (Tag w' (Vconstr t vs)) ->
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

(* TODO: refactoring *)
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

Lemma bstep_lt_Res_not_OOT_aux ρ e c r v :
  bstep ρ e c r ->
  r = Res v ->
  forall c0,
    c <= c0 ->
    ~ (bstep ρ e c0 OOT).
Proof.
  intros.
  generalize dependent c0.
  generalize dependent v.
  induction H using bstep_ind' with (P := fun ρ e c r =>
                                            forall v,
                                              r = Res v ->
                                              forall c0,
                                                c <= c0 ->
                                                ~ bstep ρ e c0 OOT)
                                    (P0 := fun ρ e c r =>
                                             forall v,
                                               r = Res v ->
                                               forall c0,
                                                 c <= c0 ->
                                                 ~ bstep_fuel ρ e c0 OOT);
    intros; intro Hc.
  - inv H0.
    inv Hc.
  - inv H0.
    inv Hc.
    eapply IHbstep; eauto.
  - inv H3.
    inv Hc; invc.
    eapply IHbstep; eauto.
  - inv H4.
    inv Hc; invc.
    2 : { eapply IHbstep with (c0 := c0); eauto; lia. }
    assert (Hcv : v = v1 /\ c = c1).
    {
      eapply bstep_fuel_deterministic; eauto.
    }
    inv Hcv.
    eapply IHbstep0 with (c0 := c'0); eauto; lia.
  - inv H3.
  - inv H1.
    inv Hc; invc.
    eapply IHbstep; eauto.
  - inv H2.
    inv Hc; invc.
    eapply IHbstep; eauto.
  - inv H2.
    inv Hc; invc.
    assert (He : e = e0).
    {
      eapply find_tag_deterministic; eauto.
    }
    inv He.
    eapply IHbstep; eauto.
  - inv H.
  - inv H0.
    inv Hc.
    inv H1.
    eapply IHbstep with (c0 := c1); eauto; lia.
Qed.

Lemma bstep_lt_Res_not_OOT ρ e c v :
  bstep ρ e c (Res v) ->
  forall c0,
    c <= c0 ->
    ~ (bstep ρ e c0 OOT).
Proof. eauto using bstep_lt_Res_not_OOT_aux. Qed.

Lemma bstep_fuel_lt_Res_not_OOT ρ e c v :
  bstep_fuel ρ e c (Res v) ->
  forall c0,
    c <= c0 ->
    ~ (bstep_fuel ρ e c0 OOT).
Proof.
  intros.
  inv H.
  intro Hc.
  inv Hc.
  inv H0.
  eapply bstep_lt_Res_not_OOT with (c0 := c); eauto; lia.
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

Lemma free_constr_xs_inv Γ x w t xs e :
  occurs_free (Econstr x w t xs e) \subset Γ ->
  FromList xs \subset Γ.
Proof.
  intros.
  eapply Included_trans; eauto.
  eapply free_constr_xs_subset; eauto.
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
Proof. fcrush. Qed.

Lemma free_app_xs_inv Γ f w xs :
  occurs_free (Eapp f w xs) \subset Γ ->
  FromList xs \subset Γ.
Proof. sfirstorder. Qed.

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

Lemma free_letapp_xs_inv Γ x f w xs k :
  occurs_free (Eletapp x f w xs k) \subset Γ ->
  FromList xs \subset Γ.
Proof.
  intros.
  eapply Included_trans; eauto.
  eapply free_letapp_xs_subset; eauto.
Qed.

Lemma free_case_hd_subset e x w c cl :
  occurs_free e \subset occurs_free (Ecase x w ((c, e) :: cl)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros; auto.
Qed.

Lemma free_case_hd_inv Γ e x w c cl :
  occurs_free (Ecase x w ((c, e) :: cl)) \subset Γ ->
  occurs_free e \subset Γ.
Proof.
  intros.
  eapply Included_trans; eauto.
  eapply free_case_hd_subset; eauto.
Qed.

Lemma free_case_tl_subset w x c e cl :
  occurs_free (Ecase x w cl) \subset occurs_free (Ecase x w ((c, e) :: cl)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros; auto.
Qed.

Lemma free_case_tl_inv Γ e x w c cl :
  occurs_free (Ecase x w ((c, e) :: cl)) \subset Γ ->
  occurs_free (Ecase x w cl) \subset Γ.
Proof.
  intros.
  eapply Included_trans; eauto.
  eapply free_case_tl_subset; eauto.
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

Fixpoint occurs_free_case (cl : list (ctor_tag * exp)) : vars :=
  match cl with
  | [] => (Empty_set _)
  | ((c, e) :: cl) => (occurs_free e) :|: (occurs_free_case cl)
  end.

Lemma occurs_free_case_compat cl :
  forall y x l,
    (y \in (occurs_free_case cl)) ->
    (y \in (occurs_free (Ecase x l cl))).
Proof.
  unfold Ensembles.In.
  induction cl; simpl; intros; auto.
  - inv H.
  - destruct a.
    inv H; auto.
Qed.

Lemma occurs_free_case_inv cl :
  forall y x l,
    (y \in (occurs_free (Ecase x l cl))) ->
    (y = x \/ (y \in (occurs_free_case cl))).
Proof.
  unfold Ensembles.In.
  induction cl; simpl; intros; auto.
  - inv H.
    left; auto.
  - destruct a.
    inv H; auto.
    + right; left; auto.
    + eapply IHcl in H6; eauto; inv H6.
      * left; auto.
      * right; right; auto.
Qed.

(* Linking *)

(* A dedicated label for linking purposes *)
(* Note it doesn't matter whether this label occurs inside a program body. *)
Parameter l0 : label.

Definition link f x e1 e2 : exp :=
  Efun f l0 [] e1
    (Eletapp x f l0 [] e2).

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

Lemma has_label_dec e :
  Decidable (has_label e).
Proof.
  induction e using exp_ind'; constructor; intros.
  - right.
    intro Hc; inv Hc.
  - destruct (M.elt_eq x0 w) eqn:Hx; subst.
    + left; auto.
    + right; intro Hc; inv Hc; contradiction.
  - destruct (M.elt_eq x w) eqn:Hx; subst.
    + left; auto.
    + inv IHe1; inv IHe2.
      specialize (Dec x).
      specialize (Dec0 x).
      inv Dec.
      * left; auto.
      * inv Dec0.
        -- left; auto.
        -- right; intro Hc; inv Hc; contradiction.
  - destruct (M.elt_eq x0 w) eqn:Hx; subst.
    + left; auto.
    + inv IHe.
      destruct (Dec x0).
      * left; auto.
      * right; intro Hc; inv Hc; contradiction.
  - destruct (M.elt_eq x0 w) eqn:Hx; subst.
    + left; auto.
    + inv IHe.
      destruct (Dec x0).
      * left; auto.
      * right; intro Hc; inv Hc; contradiction.
  - destruct (M.elt_eq x0 w) eqn:Hx; subst.
    + left; auto.
    + right; intro Hc; inv Hc; contradiction.
  - destruct (M.elt_eq x0 w) eqn:Hx; subst.
    + left; auto.
    + inv IHe; inv IHe0.
      destruct (Dec x0).
      * left; auto.
      * destruct (Dec0 x0).
        -- left; auto.
        -- right; intro Hc; inv Hc; contradiction.
  - destruct (M.elt_eq x0 w) eqn:Hx; subst.
    + left; auto.
    + inv IHe.
      destruct (Dec x0).
      * left; auto.
      * right; intro Hc; inv Hc; contradiction.
Qed.

Lemma has_label_fun_body {f w xs e k} :
  has_label e \subset has_label (Efun f w xs e k).
Proof. fcrush. Qed.

Lemma has_label_fun_cont {f w xs e k} :
  has_label k \subset has_label (Efun f w xs e k).
Proof. fcrush. Qed.

Lemma has_label_letapp_cont {x f w xs k} :
  has_label k \subset has_label (Eletapp x f w xs k).
Proof. fcrush. Qed.

Lemma has_label_constr_cont {x w c xs k} :
  has_label k \subset has_label (Econstr x w c xs k).
Proof. fcrush. Qed.

Lemma has_label_proj_body {x w n y e} :
  has_label e \subset has_label (Eproj x w n y e).
Proof. fcrush. Qed.

Lemma has_label_case_hd {x w c e cl} :
  has_label e \subset has_label (Ecase x w ((c, e) :: cl)).
Proof. fcrush. Qed.

Lemma has_label_case_tl {x w c e cl} :
  has_label (Ecase x w cl) \subset has_label (Ecase x w ((c, e) :: cl)).
Proof. fcrush. Qed.

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

| Unique_case :
  forall {x l cl L},
    (~ l \in L) ->
    unique_label_case cl L ->
    unique_label (Ecase x l cl)

with unique_label_case : list (ctor_tag * exp) -> labels -> Prop :=
| Unique_case_nil :
  unique_label_case [] (Empty_set _)

| Unique_case_tl :
  forall {c e cl L},
    Disjoint _ (has_label e) L ->
    unique_label e ->
    unique_label_case cl L ->
    unique_label_case ((c , e) :: cl) ((has_label e) :|: L).

Hint Constructors unique_label : core.
Hint Constructors unique_label_case : core.

Scheme unique_label_mut := Induction for unique_label Sort Prop
with unique_label_case_mut := Induction for unique_label_case Sort Prop.

(* Well-formed Value and Environment *)
Inductive wf_val : wval -> Prop :=
| WF_TAG :
  forall w v,
    wf_val' v ->
    wf_val (Tag w v)

with wf_val' : val -> Prop :=
| WF_Vfun :
  forall f ρ xs e,
    wf_env ρ ->
    wf_val' (Vfun f ρ xs e)

| WF_Vconstr_nil :
  forall c,
    wf_val' (Vconstr c [])

| WF_Vconstr :
  forall c v vs,
    wf_val v ->
    wf_val' (Vconstr c vs) ->
    wf_val' (Vconstr c (v :: vs))

with wf_env : env -> Prop :=
| WF_env :
  forall ρ,
    (forall x v, ρ ! x = Some v -> wf_val v) ->
    wf_env ρ.

Hint Constructors wf_val : core.
Hint Constructors wf_val' : core.
Hint Constructors wf_env : core.

Scheme wf_val_mut := Induction for wf_val Sort Prop
  with wf_val'_mut := Induction for wf_val' Sort Prop
  with wf_env_mut := Induction for wf_env Sort Prop.

(* Well-formed Result *)
Inductive wf_res : res -> Prop :=
| WF_OOT : wf_res OOT
| WF_Res : forall v, wf_val v -> wf_res (Res v).

Hint Constructors wf_res : core.

Lemma wf_env_get ρ :
  wf_env ρ ->
  forall x v,
    ρ ! x = Some v ->
    wf_val v.
Proof. intros H; inv H; eauto. Qed.

Lemma wf_env_get_list ρ :
  wf_env ρ ->
  forall xs vs,
    get_list xs ρ = Some vs ->
    Forall wf_val vs.
Proof.
  intros Henv xs.
  induction xs; simpl; intros.
  - inv H; auto.
  - destruct (ρ ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ) eqn:Heq2; try discriminate.
    inv H.
    constructor; eauto.
    eapply wf_env_get; eauto.
Qed.

Lemma wf_env_set ρ x v :
  wf_env ρ ->
  wf_val v ->
  wf_env (M.set x v ρ).
Proof.
  intros.
  inv H.
  constructor; intros.
  destruct (M.elt_eq x x0); subst.
  - rewrite M.gss in *; inv H; auto.
  - rewrite M.gso in *; eauto.
Qed.

Lemma wf_env_set_lists :
  forall ρ,
    wf_env ρ ->
    forall vs xs ρ',
      Forall wf_val vs ->
      set_lists xs vs ρ = Some ρ' ->
      wf_env ρ'.
Proof.
  intros ρ Henv vs.
  induction vs; simpl; intros.
  - specialize (set_lists_length_eq _ _ _ _ H0); intros.
    rewrite length_zero_iff_nil in H1; inv H1.
    inv H0; auto.
  - destruct xs; inv H0.
    destruct (set_lists xs vs ρ) eqn:Heq1; try discriminate.
    inv H2. inv H.
    rename e into x0.
    constructor; intros.
    destruct (M.elt_eq x0 x); subst.
    + rewrite M.gss in *; inv H; auto.
    + rewrite M.gso in *; auto.
      rename t into ρ'.
      assert (wf_env ρ') by (eapply IHvs; eauto).
      eapply wf_env_get; eauto.
Qed.

Lemma wf_val_Vconstr c w vs :
  Forall wf_val vs ->
  wf_val (Tag w (Vconstr c vs)).
Proof.
  intros H. induction H; simpl; auto.
  assert (Hwf : wf_val (Tag w (Vconstr c l))) by (apply IHForall).
  inv Hwf. constructor. constructor; auto.
Qed.

Lemma wf_val_Vconstr_inv {w c vs} :
  wf_val (Tag w (Vconstr c vs)) ->
  Forall wf_val vs.
Proof.
  intros.
  remember (Tag w (Vconstr c vs)) as v.
  revert c vs Heqv.
  induction H using wf_val_mut with
    (P0 := fun v wf =>
             forall (c : ctor_tag) (vs : list wval),
               v = Vconstr c vs ->
               Forall wf_val vs)
    (P1 := fun ρ wf => True);
    intros; eauto.
  - inv Heqv; eauto.
  - inv H.
  - inv H; auto.
  - inv H0; constructor; eauto.
Qed.

Lemma bstep_wf_res ρ e c r :
  wf_env ρ ->
  bstep ρ e c r ->
  wf_res r.
Proof.
  intros Hw H.
  induction H using bstep_ind' with
    (P0 := fun ρ e c r => wf_env ρ -> wf_res r);
    intros; auto.

  - (* BStep_ret *)
    constructor.
    eapply wf_env_get; eauto.

  - (* BStep_fun *)
    apply IHbstep.
    eapply wf_env_set; eauto.

  - (* BStep_app *)
    assert (Hwfclo : wf_val (Tag w' (Vfun f' ρ' xs' e))).
    { eapply wf_env_get; eauto. }
    assert (Hwfρ' : wf_env ρ').
    { inv Hwfclo.
      match goal with [Hv : wf_val' _ |- _] => inv Hv end; auto. }
    assert (Hwfvs : Forall wf_val vs).
    { eapply wf_env_get_list. apply Hw. eassumption. }
    assert (Hwfρf : wf_env (M.set f' (Tag w' (Vfun f' ρ' xs' e)) ρ')).
    { eapply wf_env_set; eauto. }
    apply IHbstep.
    eapply wf_env_set_lists with (ρ := M.set f' (Tag w' (Vfun f' ρ' xs' e)) ρ'); eauto.

  - (* BStep_letapp_Res *)
    assert (Hwfclo : wf_val (Tag w' (Vfun f' ρ' xs' e))).
    { eapply wf_env_get; eauto. }
    assert (Hwfρ' : wf_env ρ').
    { inv Hwfclo.
      match goal with [Hv : wf_val' _ |- _] => inv Hv end; auto. }
    assert (Hwfvs : Forall wf_val vs).
    { eapply wf_env_get_list. apply Hw. eassumption. }
    assert (Hwfρf : wf_env (M.set f' (Tag w' (Vfun f' ρ' xs' e)) ρ')).
    { eapply wf_env_set; eauto. }
    assert (Hwfρ'' : wf_env ρ'').
    { eapply wf_env_set_lists
        with (ρ := M.set f' (Tag w' (Vfun f' ρ' xs' e)) ρ'); eauto. }
    assert (Hwfres : wf_res (Res v)) by (apply IHbstep; auto).
    inv Hwfres.
    apply IHbstep0.
    eapply wf_env_set; eauto.

  - (* BStep_constr *)
    apply IHbstep.
    eapply wf_env_set; eauto.
    eapply wf_val_Vconstr; eauto.
    eapply wf_env_get_list; eauto.

  - (* BStep_proj *)
    apply IHbstep.
    eapply wf_env_set; eauto.
    assert (Hwfvc : wf_val (Tag w' (Vconstr t vs))) by (eapply wf_env_get; eauto).
    apply wf_val_Vconstr_inv in Hwfvc.
    eapply Forall_nth_error; eauto.
Qed.

Lemma bstep_fuel_wf_res ρ e c r :
  wf_env ρ ->
  bstep_fuel ρ e c r ->
  wf_res r.
Proof.
  intros.
  inv H0; eauto using bstep_wf_res.
Qed.

(* Sub Value and Environment for the Labeled Semantics *)
(* Analogous to [subval]/[subenv] in [ANF.v], but for [ANF1.v]'s labeled
   semantics: there is no exposed-web tracking, so the relations and weakening
   lemma [bstep_subenv] are streamlined accordingly. Function closures may
   capture different envs as long as the envs agree on the body's free vars. *)
Inductive subval : wval -> wval -> Prop :=
| Sub_wval :
  forall v1 v2 w,
    subval' v1 v2 ->
    subval (Tag w v1) (Tag w v2)

with subval' : val -> val -> Prop :=
| Sub_fun :
  forall Γ f xs e ρ1 ρ2,
    (occurs_free e) \subset (FromList xs :|: (f |: Γ)) ->
    subenv Γ ρ1 ρ2 ->
    subval' (Vfun f ρ1 xs e) (Vfun f ρ2 xs e)

| Sub_constr_nil :
  forall c,
    subval' (Vconstr c []) (Vconstr c [])

| Sub_constr_cons :
  forall c v1 v2 vs1 vs2,
    subval v1 v2 ->
    subval' (Vconstr c vs1) (Vconstr c vs2) ->
    subval' (Vconstr c (v1 :: vs1)) (Vconstr c (v2 :: vs2))

with subenv : vars -> env -> env -> Prop :=
| Sub_env :
  forall Γ ρ1 ρ2,
    (forall x,
        (x \in Γ) ->
        forall v1,
          M.get x ρ1 = Some v1 ->
          exists v2,
            M.get x ρ2 = Some v2 /\
            subval v1 v2) ->
    subenv Γ ρ1 ρ2.

Hint Constructors subval' : core.
Hint Constructors subval : core.
Hint Constructors subenv : core.

Scheme subval_mut := Induction for subval Sort Prop
with subval'_mut := Induction for subval' Sort Prop
with subenv_mut := Induction for subenv Sort Prop.

Inductive subres : res -> res -> Prop :=
| Sub_OOT :
  subres OOT OOT

| Sub_Res :
  forall {v1 v2},
    subval v1 v2 ->
    subres (Res v1) (Res v2).

Hint Constructors subres : core.

Lemma subenv_set {x v1 v2 Γ ρ1 ρ2}:
  subval v1 v2 ->
  subenv Γ ρ1 ρ2 ->
  subenv (x |: Γ) (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  intros Hv Hρ.
  constructor; intros y Hy w1 Hgw.
  destruct (M.elt_eq x y) as [<-|Hne].
  - rewrite M.gss in Hgw. inv Hgw.
    exists v2. rewrite M.gss. split; auto.
  - rewrite M.gso in Hgw by auto.
    inv Hρ.
    assert (Hy' : y \in Γ).
    { inv Hy; auto. inv H0; contradiction. }
    edestruct (H _ Hy' _ Hgw) as [w2 [Hgw2 Hwv]].
    exists w2. rewrite M.gso by auto. auto.
Qed.

Lemma subenv_get {Γ ρ1 ρ2} :
  subenv Γ ρ1 ρ2 ->
  forall x,
    (x \in Γ) ->
    forall {v1},
      ρ1 ! x = Some v1 ->
      exists v2,
        ρ2 ! x = Some v2 /\
        subval v1 v2.
Proof. intros; inv H; eauto. Qed.

Lemma subenv_subset Γ1 {Γ2 ρ1 ρ2} :
  subenv Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  subenv Γ2 ρ1 ρ2.
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  constructor; intros.
  eapply subenv_get; eauto.
Qed.

Lemma subenv_set_lists Γ ρ1 ρ2:
  subenv Γ ρ1 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 subval vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    subenv (FromList xs :|: Γ) ρ3 ρ4.
Proof.
  intros Hs xs.
  induction xs; simpl; intros;
    destruct vs1; destruct vs2; try discriminate.
  - inv H0; inv H1.
    constructor; intros.
    eapply subenv_get; eauto.
    inv H0; auto. inv H2.
  - destruct (set_lists xs vs1 ρ1) eqn:Heq1;
      destruct (set_lists xs vs2 ρ2) eqn:Heq2;
      try discriminate.
    inv H; inv H0; inv H1.
    eapply (subenv_subset (a |: (FromList xs :|: Γ))).
    eapply subenv_set; eauto.
    rewrite FromList_cons; eauto.
    rewrite <- Union_assoc.
    eapply Included_refl.
Qed.

Lemma subenv_get_lists {Γ ρ1 ρ2}:
  subenv Γ ρ1 ρ2 ->
  forall xs,
    (FromList xs \subset Γ) ->
    forall {vs1},
      get_list xs ρ1 = Some vs1 ->
      exists vs2,
        get_list xs ρ2 = Some vs2 /\
        Forall2 subval vs1 vs2.
Proof.
  intros Hs xs.
  induction xs; simpl; intros.
  - inv H0; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq2; try discriminate.
    inv H0.
    rewrite FromList_cons in H.
    edestruct (subenv_get Hs a) as [v2 [Heqv2 Hv2]]; eauto.
    edestruct IHxs as [vs2 [Heqvs2 Hvs]]; eauto.
    apply Union_Included_r in H; auto.
    rewrite Heqv2.
    rewrite Heqvs2.
    eexists; split; eauto.
Qed.

Lemma subval_Vconstr c w vs1 vs2 :
  Forall2 subval vs1 vs2 ->
  subval (Tag w (Vconstr c vs1)) (Tag w (Vconstr c vs2)).
Proof.
  intros H.
  induction H; simpl; auto.
  inv IHForall2; auto.
Qed.

Lemma subval_Vconstr_inv_l {w c vs1 v2} :
  subval (Tag w (Vconstr c vs1)) v2 ->
  exists vs2,
    v2 = (Tag w (Vconstr c vs2)) /\
    Forall2 subval vs1 vs2.
Proof.
  intros.
  remember (Tag w (Vconstr c vs1)) as v1.
  generalize dependent vs1.
  induction H using subval_mut with
    (P0 := fun v1' v2' sub =>
             match v1', v2' with
             | Vfun _ _ _ _, Vfun _ _ _ _ => True
             | Vconstr _ vs1, Vconstr _ vs2 => Forall2 subval vs1 vs2
             | _, _ => False
             end)
    (P1 := fun _ _ _ _ => True);
    intros; auto.
  inv Heqv1.
  destruct v2; try contradiction.
  inv s; eauto.
Qed.

Lemma subval_refl v :
  wf_val v ->
  subval v v.
Proof.
  intros H.
  induction H using wf_val_mut with
    (P0 := fun v wf =>
             match v with
             | Vfun f ρ xs e => subenv (occurs_free e) ρ ρ
             | Vconstr c vs => Forall2 subval vs vs
             end)
    (P1 := fun ρ wf => forall Γ, subenv Γ ρ ρ); intros.
  - (* WF_TAG *)
    destruct v.
    + constructor; auto.
      eapply (Sub_fun (occurs_free e)); eauto.
      unfold Ensembles.Included, Ensembles.In, FromList.
      intros. repeat apply Union_intror; auto.
    + eapply subval_Vconstr; eauto.
  - (* WF_Vfun *) auto.
  - (* WF_Vconstr_nil *) constructor.
  - (* WF_Vconstr *) constructor; auto.
  - (* WF_env *)
    constructor; intros y Hy v Hgv.
    exists v; split; eauto.
Qed.

Lemma subval_refl_Forall vs :
  Forall wf_val vs ->
  Forall2 subval vs vs.
Proof.
  intros H.
  induction H; constructor; auto.
  apply subval_refl; auto.
Qed.

Lemma subenv_refl Γ ρ :
  wf_env ρ ->
  subenv Γ ρ ρ.
Proof.
  intros Hwf.
  constructor; intros y Hy v Hgv.
  exists v; split; auto.
  apply subval_refl. eapply wf_env_get; eauto.
Qed.

Lemma subval_trans v1 v2 v3 :
  subval v1 v2 ->
  subval v2 v3 ->
  subval v1 v3
with subval'_trans v1 v2 v3 :
  subval' v1 v2 ->
  subval' v2 v3 ->
  subval' v1 v3
with subenv_trans Γ1 Γ2 ρ1 ρ2 ρ3 :
  subenv Γ1 ρ1 ρ2 ->
  subenv Γ2 ρ2 ρ3 ->
  subenv (Γ1 :&: Γ2) ρ1 ρ3.
Proof.
  - (* subval_trans *)
    intros H1 H2.
    inv H1. inv H2. constructor. eapply subval'_trans; eauto.

  - (* subval'_trans *)
    intros H1 H2.
    inv H1.
    + (* Sub_fun *)
      inversion H2 as [Γb fb xsb eb ρb1 ρb2 HFVb Hsubb | |]; subst.
      eapply Sub_fun with (Γ := Γ :&: Γb).
      * (* FV inclusion *)
        unfold Ensembles.Included, Ensembles.In in *.
        intros z Hz.
        pose proof (H _ Hz) as Hza.
        pose proof (HFVb _ Hz) as Hzb.
        inv Hza; [left; auto|].
        inv Hzb; [left; auto|].
        rename H1 into Hzfa. rename H3 into Hzfb.
        right.
        inv Hzfa; [left; auto|].
        inv Hzfb; [left; auto|].
        right. constructor; auto.
      * eapply subenv_trans; eauto.
    + (* Sub_constr_nil *)
      inv H2. constructor.
    + (* Sub_constr_cons *)
      inv H2. constructor.
      * eapply subval_trans; eauto.
      * eapply subval'_trans; eauto.

  - (* subenv_trans *)
    intros H1 H2.
    constructor; intros y Hy v_y Hgy.
    inversion Hy as [a Hy_Γ Hy_Γ' Ha]; subst.
    inv H1.
    edestruct (H y Hy_Γ v_y Hgy) as [v_mid [Hg_mid Hsub_mid]].
    inv H2.
    edestruct (H0 y Hy_Γ' v_mid Hg_mid) as [v3 [Hg3 Hsub3]].
    exists v3; split; auto.
    eapply subval_trans; eauto.
Qed.

Lemma subres_trans r1 r2 r3 :
  subres r1 r2 ->
  subres r2 r3 ->
  subres r1 r3.
Proof.
  intros H1 H2.
  inv H1; inv H2; constructor.
  eapply subval_trans; eauto.
Qed.

(* Semantic Weakening Lemmas *)
Lemma bstep_subenv {Γ ρ1 ρ2 e c r1}:
  (occurs_free e) \subset Γ ->
  subenv Γ ρ1 ρ2 ->
  bstep ρ1 e c r1 ->
  (exists r2, bstep ρ2 e c r2 /\ subres r1 r2).
Proof.
  intros.
  generalize dependent ρ2.
  generalize dependent Γ.
  induction H1 using bstep_ind' with
    (P0 := fun ρ1 e c r =>
             forall Γ,
               occurs_free e \subset Γ ->
               forall ρ2,
                 subenv Γ ρ1 ρ2 ->
                 exists r2, bstep_fuel ρ2 e c r2 /\ subres r r2);
    intros; subst.

  - (* BStep_ret *)
    edestruct (subenv_get H1 x) as [v2' [Heqv2' Hv]]; eauto.

  - (* BStep_fun *)
    assert (HFk : occurs_free k \subset (f |: (occurs_free (Efun f w xs e k))))
      by apply free_fun_k_subset.
    destruct (IHbstep _ HFk (M.set f (Tag w (Vfun f ρ2 xs e)) ρ2)) as [r2 [Hr2 Hs]].
    + eapply subenv_set; eauto.
      constructor.
      econstructor; eauto.
      * eapply Included_trans; eauto.
        apply free_fun_e_subset.
        apply Included_Union_compat.
        apply Included_refl.
        apply Included_Union_compat; eauto.
        apply Included_refl.
      * eapply subenv_subset; eauto.
    + eexists; split; eauto.

  - (* BStep_app *)
    edestruct (subenv_get H4 f) as [vf2 [Heqvf2 Hvf2]]; eauto.
    inv Hvf2.
    inv H8.
    edestruct (subenv_get_lists H4 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_app_xs_subset.

    assert (Hlen : length xs' = length vs2).
    { erewrite <- (Forall2_length _ _ _ Hvs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto. }
    destruct (set_lists_length3
                (M.set f' (Tag w' (Vfun f' ρ0 xs' e)) ρ0)
                _ _ Hlen) as [ρ2' Heqρ2'].

    edestruct (IHbstep _ H11 ρ2') as [r2 [Hr2 Hs]].
    + eapply subenv_set_lists; eauto.
      eapply subenv_set; eauto.
    + exists r2; split; auto.
      eapply BStep_app; eauto.

  - (* BStep_letapp_Res *)
    edestruct (subenv_get H5 f) as [vf2 [Heqvf2 Hvf2]]; eauto.
    inv Hvf2.
    inv H9.
    edestruct (subenv_get_lists H5 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_letapp_xs_subset.

    assert (Hlen : length xs' = length vs2).
    { erewrite <- (Forall2_length _ _ _ Hvs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto. }
    destruct (set_lists_length3
                (M.set f' (Tag w' (Vfun f' ρ0 xs' e)) ρ0)
                _ _ Hlen) as [ρ2' Heqρ2'].

    edestruct (IHbstep _ H12 ρ2') as [r2 [Hr2 Hs]].
    + eapply subenv_set_lists; eauto.
      eapply subenv_set; eauto.
    + inv Hs.
      assert (HFk : occurs_free k \subset (x |: Γ)) by (eapply free_letapp_k_inv; eauto).
      destruct (IHbstep0 _ HFk (M.set x v2 ρ2)) as [r3 [Hr3 Hs']].
      * eapply subenv_set; eauto.
      * exists r3; split; auto.
        econstructor; eauto.

  - (* BStep_letapp_OOT *)
    edestruct (subenv_get H4 f) as [vf2 [Heqvf2 Hvf2]]; eauto.
    inv Hvf2.
    inv H8.
    edestruct (subenv_get_lists H4 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_letapp_xs_subset.

    assert (Hlen : length xs' = length vs2).
    { erewrite <- (Forall2_length _ _ _ Hvs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto. }
    destruct (set_lists_length3
                (M.set f' (Tag w' (Vfun f' ρ0 xs' e)) ρ0)
                _ _ Hlen) as [ρ2' Heqρ2'].

    edestruct (IHbstep _ H11 ρ2') as [r2 [Hr2 Hs]].
    + eapply subenv_set_lists; eauto.
      eapply subenv_set; eauto.
    + inv Hs.
      exists OOT; split; auto.
      econstructor; eauto.

  - (* BStep_constr *)
    edestruct (subenv_get_lists H2 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_constr_xs_subset.

    assert (HFk : occurs_free e \subset (x |: Γ)) by (eapply free_constr_k_inv; eauto).
    destruct (IHbstep _ HFk (M.set x (Tag w (Vconstr t vs2)) ρ2)) as [r2 [Hr2 Hs]].
    + eapply subenv_set; eauto.
      eapply subval_Vconstr; eauto.
    + exists r2; split; auto.
      econstructor; eauto.

  - (* BStep_proj *)
    edestruct (subenv_get H3 y) as [vy2 [Heqvy2 Hvy2]]; eauto.
    edestruct (subval_Vconstr_inv_l Hvy2) as [vs2 [Heqvs2 Hvs2]]; subst.
    edestruct (Forall2_nth_error H0 Hvs2) as [v' [Heqv' Hv']].
    assert (HFk : occurs_free e \subset (x |: Γ)) by (eapply free_proj_k_inv; eauto).
    destruct (IHbstep _ HFk (M.set x v' ρ2)) as [r2 [Hr2 Hs]].
    + eapply subenv_set; eauto.
    + exists r2; split; auto.
      econstructor; eauto.

  - (* BStep_case *)
    edestruct (subenv_get H3 x) as [vx2 [Heqvx2 Hvx2]]; eauto.
    edestruct (subval_Vconstr_inv_l Hvx2) as [vs2 [Heqvs2 Hvs2]]; subst.
    edestruct IHbstep as [r2 [Hr2 Hs]]; eauto.
    + eapply free_case_e_inv; eauto.

  - (* BStepF_OOT *)
    exists OOT; split; auto.

  - (* BStepF_Step *)
    edestruct IHbstep as [r2 [Hr2 Hs]]; eauto.
Qed.

Lemma bstep_fuel_subenv {Γ ρ1 ρ2 e c r1}:
  (occurs_free e) \subset Γ ->
  subenv Γ ρ1 ρ2 ->
  bstep_fuel ρ1 e c r1 ->
  (exists r2, bstep_fuel ρ2 e c r2 /\ subres r1 r2).
Proof.
  intros.
  inv H1.
  - exists OOT; split; auto.
  - destruct (bstep_subenv H H0 H2) as [r2 [Hr2 Hs]].
    exists r2; split; auto.
Qed.

Lemma bstep_fuel_drop_unused {f val ρ e c r}:
  ~ (f \in occurs_free e) ->
  wf_env ρ ->
  bstep_fuel (M.set f val ρ) e c r ->
  exists r', bstep_fuel ρ e c r' /\ subres r r'.
Proof.
  intros Hf Hwf Hcb.
  eapply @bstep_fuel_subenv with (Γ := occurs_free e); eauto.
  - apply Included_refl.
  - constructor; intros z Hz w Hgw.
    destruct (M.elt_eq z f) as [<-|Hne]; [contradiction|].
    rewrite M.gso in Hgw by auto.
    exists w; split; auto.
    apply subval_refl. eapply wf_env_get; eauto.
Qed.

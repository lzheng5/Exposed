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
(* [wf_env Γ ρ] is scoped on Γ: ρ is total on Γ, and every value stored in ρ
   is well-formed. [WF_Vfun] additionally requires the closure's body's free
   variables to be covered by the closure's argument list, the recursive name,
   and the captured-environment scope Γ. *)
Inductive wf_val : wval -> Prop :=
| WF_TAG :
  forall w v,
    wf_val' v ->
    wf_val (Tag w v)

with wf_val' : val -> Prop :=
| WF_Vfun :
  forall f ρ xs e Γ,
    wf_env Γ ρ ->
    occurs_free e \subset FromList xs :|: (f |: Γ) ->
    wf_val' (Vfun f ρ xs e)

| WF_Vconstr_nil :
  forall c,
    wf_val' (Vconstr c [])

| WF_Vconstr :
  forall c v vs,
    wf_val v ->
    wf_val' (Vconstr c vs) ->
    wf_val' (Vconstr c (v :: vs))

with wf_env : vars -> env -> Prop :=
| WF_env :
  forall Γ ρ,
    (forall x v, ρ ! x = Some v -> wf_val v) ->
    (forall x, x \in Γ -> exists v, ρ ! x = Some v) ->
    wf_env Γ ρ.

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

Lemma wf_env_get {Γ ρ} :
  wf_env Γ ρ ->
  forall x v,
    ρ ! x = Some v ->
    wf_val v.
Proof. intros H; inv H; eauto. Qed.

Lemma wf_env_get_total {Γ ρ} :
  wf_env Γ ρ ->
  forall x,
    x \in Γ ->
    exists v, ρ ! x = Some v /\ wf_val v.
Proof.
  intros H x Hx. inv H.
  edestruct H1 as [v Hg]; eauto.
  exists v; split; auto.
  eapply H0; eauto.
Qed.

Lemma wf_env_subset {Γ1 Γ2 ρ} :
  wf_env Γ1 ρ ->
  Γ2 \subset Γ1 ->
  wf_env Γ2 ρ.
Proof.
  intros Hw Hsub.
  inv Hw. constructor; intros; eauto.
Qed.

Lemma wf_env_get_list {Γ ρ} :
  wf_env Γ ρ ->
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

Lemma wf_env_set {Γ ρ} x v :
  wf_env Γ ρ ->
  wf_val v ->
  wf_env (x |: Γ) (M.set x v ρ).
Proof.
  intros Henv Hv.
  inv Henv.
  constructor; intros.
  - destruct (M.elt_eq x x0) as [<-|Hne].
    + rewrite M.gss in H1; inv H1; auto.
    + rewrite M.gso in H1 by auto; eauto.
  - destruct (M.elt_eq x x0) as [<-|Hne].
    + eexists. rewrite M.gss; reflexivity.
    + inv H1.
      * inv H2; contradiction.
      * edestruct H0 as [w Hgw]; eauto.
        eexists. rewrite M.gso by auto. eassumption.
Qed.

Lemma wf_env_set_lists :
  forall {Γ ρ},
    wf_env Γ ρ ->
    forall vs xs ρ',
      Forall wf_val vs ->
      set_lists xs vs ρ = Some ρ' ->
      wf_env (FromList xs :|: Γ) ρ'.
Proof.
  intros Γ ρ Henv vs.
  induction vs; simpl; intros xs ρ' Hwfvs Hset.
  - destruct xs; try discriminate.
    inv Hset.
    rewrite FromList_nil, Union_Empty_set_neut_l. auto.
  - destruct xs; try discriminate.
    simpl in Hset.
    destruct (set_lists xs vs ρ) eqn:Heq1; try discriminate.
    inv Hset.
    inv Hwfvs.
    rewrite FromList_cons, <- Union_assoc.
    eapply wf_env_set; eauto.
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
    (P1 := fun Γ ρ wf => True);
    intros; eauto.
  - inv Heqv; eauto.
  - inv H.
  - inv H; auto.
  - inv H0; constructor; eauto.
Qed.

Lemma bstep_wf_res {Γ ρ e c r} :
  wf_env Γ ρ ->
  occurs_free e \subset Γ ->
  bstep ρ e c r ->
  wf_res r.
Proof.
  intros Hw HF Hb.
  generalize dependent Γ.
  induction Hb using bstep_ind' with
    (P0 := fun ρ e c r =>
             forall Γ,
               wf_env Γ ρ ->
               occurs_free e \subset Γ ->
               wf_res r);
    intros.

  - (* BStep_ret *)
    constructor.
    eapply wf_env_get; eauto.

  - (* BStep_fun *)
    eapply IHHb with (Γ := f |: Γ).
    + eapply wf_env_set; eauto.
      apply WF_TAG.
      eapply WF_Vfun with (Γ := Γ); eauto.
      eapply free_fun_e_inv; eauto.
    + eapply free_fun_k_inv; eauto.

  - (* BStep_app *)
    assert (HwfFun : wf_val (Tag w' (Vfun f' ρ' xs' e))).
    { eapply wf_env_get; eauto. }
    inversion HwfFun as [w0 v0 Hwfv0]; subst; clear HwfFun.
    inversion Hwfv0 as [f0 ρ0 xs0 e0 Γclo Hwfρclo HFVe | | ]; subst; clear Hwfv0.
    assert (Hwfvs : Forall wf_val vs).
    { eapply wf_env_get_list; eauto. }
    eapply IHHb with (Γ := FromList xs' :|: (f' |: Γclo)).
    + eapply wf_env_set_lists; eauto.
      eapply wf_env_set; eauto.
      apply WF_TAG. eapply WF_Vfun; eauto.
    + apply Included_refl.

  - (* BStep_letapp_Res *)
    assert (HwfFun : wf_val (Tag w' (Vfun f' ρ' xs' e))).
    { eapply wf_env_get; eauto. }
    inversion HwfFun as [w0 v0 Hwfv0]; subst; clear HwfFun.
    inversion Hwfv0 as [f0 ρ0 xs0 e0 Γclo Hwfρclo HFVe | | ]; subst; clear Hwfv0.
    assert (Hwfvs : Forall wf_val vs).
    { eapply wf_env_get_list; eauto. }
    assert (Hwfρ'' : wf_env (FromList xs' :|: (f' |: Γclo)) ρ'').
    { eapply wf_env_set_lists; eauto.
      eapply wf_env_set; eauto.
      apply WF_TAG. eapply WF_Vfun; eauto. }
    assert (Hwfres : wf_res (Res v)).
    { eapply IHHb with (Γ := FromList xs' :|: (f' |: Γclo)); auto.
      apply Included_refl. }
    inv Hwfres.
    eapply IHHb0 with (Γ := x |: Γ).
    + eapply wf_env_set; eauto.
    + eapply free_letapp_k_inv; eauto.

  - (* BStep_letapp_OOT *)
    constructor.

  - (* BStep_constr *)
    eapply IHHb with (Γ := x |: Γ).
    + eapply wf_env_set; eauto.
      eapply wf_val_Vconstr; eauto.
      eapply wf_env_get_list; eauto.
    + eapply free_constr_k_inv; eauto.

  - (* BStep_proj *)
    assert (Hwfvc : wf_val (Tag w' (Vconstr t vs))).
    { eapply wf_env_get; eauto. }
    eapply IHHb with (Γ := x |: Γ).
    + eapply wf_env_set; eauto.
      apply wf_val_Vconstr_inv in Hwfvc.
      eapply Forall_nth_error; eauto.
    + eapply free_proj_k_inv; eauto.

  - (* BStep_case *)
    eapply IHHb; eauto.
    eapply free_case_e_inv; eauto.

  - (* BStepF_OOT *)
    constructor.

  - (* BStepF_Step *)
    eapply IHHb; eauto.
Qed.

Lemma bstep_fuel_wf_res {Γ ρ e c r} :
  wf_env Γ ρ ->
  occurs_free e \subset Γ ->
  bstep_fuel ρ e c r ->
  wf_res r.
Proof.
  intros.
  inv H1; eauto.
  eapply bstep_wf_res; eauto.
Qed.

(* Value and Environment Equivalence for the Labeled Semantics *)
(* The labeled semantics tracks no exposed-web information, so the value
   relation reduces to a structural equivalence: tags must match, constructors
   match componentwise, and closures may differ only in the captured
   environment (modulo agreement on the body's free variables). [env_eqv Γ ρ1
   ρ2] requires both environments to be defined on Γ and equivalent on it. *)
Inductive val_eqv : wval -> wval -> Prop :=
| Eqv_wval :
  forall v1 v2 w,
    val_eqv' v1 v2 ->
    val_eqv (Tag w v1) (Tag w v2)

with val_eqv' : val -> val -> Prop :=
| Eqv_fun :
  forall Γ f xs e ρ1 ρ2,
    (occurs_free e) \subset (FromList xs :|: (f |: Γ)) ->
    env_eqv Γ ρ1 ρ2 ->
    val_eqv' (Vfun f ρ1 xs e) (Vfun f ρ2 xs e)

| Eqv_constr_nil :
  forall c,
    val_eqv' (Vconstr c []) (Vconstr c [])

| Eqv_constr_cons :
  forall c v1 v2 vs1 vs2,
    val_eqv v1 v2 ->
    val_eqv' (Vconstr c vs1) (Vconstr c vs2) ->
    val_eqv' (Vconstr c (v1 :: vs1)) (Vconstr c (v2 :: vs2))

with env_eqv : vars -> env -> env -> Prop :=
| Eqv_env :
  forall Γ ρ1 ρ2,
    (forall x,
        (x \in Γ) ->
        exists v1 v2,
          M.get x ρ1 = Some v1 /\
          M.get x ρ2 = Some v2 /\
          val_eqv v1 v2) ->
    env_eqv Γ ρ1 ρ2.

Hint Constructors val_eqv' : core.
Hint Constructors val_eqv : core.
Hint Constructors env_eqv : core.

Scheme val_eqv_mut := Induction for val_eqv Sort Prop
with val_eqv'_mut := Induction for val_eqv' Sort Prop
with env_eqv_mut := Induction for env_eqv Sort Prop.

Inductive res_eqv : res -> res -> Prop :=
| Eqv_OOT :
  res_eqv OOT OOT

| Eqv_Res :
  forall {v1 v2},
    val_eqv v1 v2 ->
    res_eqv (Res v1) (Res v2).

Hint Constructors res_eqv : core.

Lemma env_eqv_set {x v1 v2 Γ ρ1 ρ2}:
  val_eqv v1 v2 ->
  env_eqv Γ ρ1 ρ2 ->
  env_eqv (x |: Γ) (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  intros Hv Hρ.
  constructor; intros y Hy.
  destruct (M.elt_eq x y) as [<-|Hne].
  - exists v1, v2.
    rewrite !M.gss. eauto.
  - inv Hρ.
    assert (Hy' : y \in Γ).
    { inv Hy; auto. inv H0; contradiction. }
    edestruct (H _ Hy') as [w1 [w2 [Hgw1 [Hgw2 Hwv]]]].
    exists w1, w2. rewrite !M.gso by auto. eauto.
Qed.

Lemma env_eqv_get {Γ ρ1 ρ2} :
  env_eqv Γ ρ1 ρ2 ->
  forall x,
    (x \in Γ) ->
    exists v1 v2,
      ρ1 ! x = Some v1 /\
      ρ2 ! x = Some v2 /\
      val_eqv v1 v2.
Proof. intros; inv H; eauto. Qed.

Lemma env_eqv_subset Γ1 {Γ2 ρ1 ρ2} :
  env_eqv Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  env_eqv Γ2 ρ1 ρ2.
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  constructor; intros.
  eapply env_eqv_get; eauto.
Qed.

Lemma env_eqv_set_lists Γ ρ1 ρ2:
  env_eqv Γ ρ1 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 val_eqv vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    env_eqv (FromList xs :|: Γ) ρ3 ρ4.
Proof.
  intros Hs xs.
  induction xs; simpl; intros;
    destruct vs1; destruct vs2; try discriminate.
  - inv H0; inv H1.
    constructor; intros.
    eapply env_eqv_get; eauto.
    inv H0; auto. inv H2.
  - destruct (set_lists xs vs1 ρ1) eqn:Heq1;
      destruct (set_lists xs vs2 ρ2) eqn:Heq2;
      try discriminate.
    inv H; inv H0; inv H1.
    eapply (env_eqv_subset (a |: (FromList xs :|: Γ))).
    eapply env_eqv_set; eauto.
    rewrite FromList_cons; eauto.
    rewrite <- Union_assoc.
    eapply Included_refl.
Qed.

Lemma env_eqv_get_lists {Γ ρ1 ρ2}:
  env_eqv Γ ρ1 ρ2 ->
  forall xs,
    (FromList xs \subset Γ) ->
    forall {vs1},
      get_list xs ρ1 = Some vs1 ->
      exists vs2,
        get_list xs ρ2 = Some vs2 /\
        Forall2 val_eqv vs1 vs2.
Proof.
  intros Hs xs.
  induction xs; simpl; intros.
  - inv H0; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq2; try discriminate.
    inv H0.
    rewrite FromList_cons in H.
    edestruct (env_eqv_get Hs a) as [v1' [v2 [Heqv1' [Heqv2 Hv2]]]]; eauto.
    rewrite Heq1 in Heqv1'; inv Heqv1'.
    edestruct IHxs as [vs2 [Heqvs2 Hvs]]; eauto.
    apply Union_Included_r in H; auto.
    rewrite Heqv2.
    rewrite Heqvs2.
    eexists; split; eauto.
Qed.

Lemma val_eqv_Vconstr c w vs1 vs2 :
  Forall2 val_eqv vs1 vs2 ->
  val_eqv (Tag w (Vconstr c vs1)) (Tag w (Vconstr c vs2)).
Proof.
  intros H.
  induction H; simpl; auto.
  inv IHForall2; auto.
Qed.

Lemma val_eqv_Vconstr_inv_l {w c vs1 v2} :
  val_eqv (Tag w (Vconstr c vs1)) v2 ->
  exists vs2,
    v2 = (Tag w (Vconstr c vs2)) /\
    Forall2 val_eqv vs1 vs2.
Proof.
  intros.
  remember (Tag w (Vconstr c vs1)) as v1.
  generalize dependent vs1.
  induction H using val_eqv_mut with
    (P0 := fun v1' v2' sub =>
             match v1', v2' with
             | Vfun _ _ _ _, Vfun _ _ _ _ => True
             | Vconstr _ vs1, Vconstr _ vs2 => Forall2 val_eqv vs1 vs2
             | _, _ => False
             end)
    (P1 := fun _ _ _ _ => True);
    intros; auto.
  inv Heqv1.
  destruct v2; try contradiction.
  match goal with [Hv' : val_eqv' _ _ |- _] => inv Hv'; eauto end.
Qed.

Lemma val_eqv_refl v :
  wf_val v ->
  val_eqv v v.
Proof.
  intros H.
  induction H using wf_val_mut with
    (P0 := fun v wf => val_eqv' v v)
    (P1 := fun Γ ρ wf => env_eqv Γ ρ ρ).
  - (* WF_TAG *) intros w v0 Hv' IHv'. constructor; auto.
  - (* WF_Vfun *)
    intros f ρ0 xs e Γ Hwfρ IHρ HFV.
    eapply (Eqv_fun Γ); eauto.
  - (* WF_Vconstr_nil *) intros c. constructor.
  - (* WF_Vconstr *)
    intros c v0 vs Hv IHv Hvs IHvs. econstructor; eauto.
  - (* WF_env *)
    intros Γ ρ0 Hwf IHwf Htot.
    constructor; intros y Hy.
    edestruct Htot as [v0 Hg]; eauto.
    exists v0, v0. repeat split; eauto.
Qed.

Lemma val_eqv_refl_Forall vs :
  Forall wf_val vs ->
  Forall2 val_eqv vs vs.
Proof.
  intros H.
  induction H; constructor; auto.
  apply val_eqv_refl; auto.
Qed.

Lemma env_eqv_refl Γ ρ :
  wf_env Γ ρ ->
  env_eqv Γ ρ ρ.
Proof.
  intros Hwf.
  constructor; intros y Hy.
  inv Hwf. edestruct H0 as [v Hg]; eauto.
  exists v, v. repeat split; auto.
  apply val_eqv_refl. eapply H; eauto.
Qed.

Lemma val_eqv_trans v1 v2 v3 :
  val_eqv v1 v2 ->
  val_eqv v2 v3 ->
  val_eqv v1 v3
with val_eqv'_trans v1 v2 v3 :
  val_eqv' v1 v2 ->
  val_eqv' v2 v3 ->
  val_eqv' v1 v3
with env_eqv_trans Γ1 Γ2 ρ1 ρ2 ρ3 :
  env_eqv Γ1 ρ1 ρ2 ->
  env_eqv Γ2 ρ2 ρ3 ->
  env_eqv (Γ1 :&: Γ2) ρ1 ρ3.
Proof.
  - (* val_eqv_trans *)
    intros H1 H2.
    inv H1. inv H2. constructor. eapply val_eqv'_trans; eauto.

  - (* val_eqv'_trans *)
    intros H1 H2.
    inv H1.
    + (* Eqv_fun *)
      inversion H2 as [Γb fb xsb eb ρb1 ρb2 HFVb Hsubb | |]; subst.
      eapply Eqv_fun with (Γ := Γ :&: Γb).
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
      * eapply env_eqv_trans; eauto.
    + (* Eqv_constr_nil *)
      inv H2. constructor.
    + (* Eqv_constr_cons *)
      inv H2. constructor.
      * eapply val_eqv_trans; eauto.
      * eapply val_eqv'_trans; eauto.

  - (* env_eqv_trans *)
    intros H1 H2.
    constructor; intros y Hy.
    inversion Hy as [a Hy_Γ Hy_Γ' Ha]; subst.
    inv H1.
    edestruct (H y Hy_Γ) as [v1 [v_mid [Hg1 [Hg_mid Hsub_mid]]]].
    inv H2.
    edestruct (H0 y Hy_Γ') as [v_mid' [v3 [Hg_mid' [Hg3 Hsub3]]]].
    rewrite Hg_mid in Hg_mid'; inv Hg_mid'.
    exists v1, v3; repeat split; auto.
    eapply val_eqv_trans; eauto.
Qed.

Lemma res_eqv_trans r1 r2 r3 :
  res_eqv r1 r2 ->
  res_eqv r2 r3 ->
  res_eqv r1 r3.
Proof.
  intros H1 H2.
  inv H1; inv H2; constructor.
  eapply val_eqv_trans; eauto.
Qed.

(* Symmetry of value/environment/result equivalence. *)
Lemma val_eqv_sym v1 v2 :
  val_eqv v1 v2 ->
  val_eqv v2 v1
with val_eqv'_sym v1 v2 :
  val_eqv' v1 v2 ->
  val_eqv' v2 v1
with env_eqv_sym Γ ρ1 ρ2 :
  env_eqv Γ ρ1 ρ2 ->
  env_eqv Γ ρ2 ρ1.
Proof.
  - (* val_eqv_sym *)
    intros H.
    inversion H as [v1' v2' w Hv']; subst; clear H.
    constructor. apply val_eqv'_sym; assumption.
  - (* val_eqv'_sym *)
    intros H.
    inversion H as [Γ0 f0 xs0 e0 ρa ρb HFV Hρ
                   | c0
                   | c0 va vb vsa vsb Hv Hvs]; subst; clear H.
    + (* Eqv_fun *)
      eapply Eqv_fun; [eassumption|].
      apply env_eqv_sym; assumption.
    + (* Eqv_constr_nil *)
      constructor.
    + (* Eqv_constr_cons *)
      constructor.
      * apply val_eqv_sym; assumption.
      * apply val_eqv'_sym; assumption.
  - (* env_eqv_sym *)
    intros H.
    inversion H as [Γ0 ρa ρb Hget]; subst; clear H.
    constructor; intros y Hy.
    edestruct Hget as [v1' [v2' [Hg1 [Hg2 Hv]]]]; eauto.
    exists v2', v1'; repeat split; auto.
    apply val_eqv_sym; assumption.
Qed.

Lemma res_eqv_sym r1 r2 :
  res_eqv r1 r2 ->
  res_eqv r2 r1.
Proof.
  intros H. inv H; constructor.
  apply val_eqv_sym; assumption.
Qed.

Lemma bstep_env_eqv_l {Γ ρ1 ρ2 e c r1}:
  (occurs_free e) \subset Γ ->
  env_eqv Γ ρ1 ρ2 ->
  bstep ρ1 e c r1 ->
  (exists r2, bstep ρ2 e c r2 /\ res_eqv r1 r2).
Proof.
  intros HF Hρ Hb.
  generalize dependent ρ2.
  generalize dependent Γ.
  induction Hb using bstep_ind' with
    (P0 := fun ρ1 e c r =>
             forall Γ,
               occurs_free e \subset Γ ->
               forall ρ2,
                 env_eqv Γ ρ1 ρ2 ->
                 exists r2, bstep_fuel ρ2 e c r2 /\ res_eqv r r2);
    intros Γ HF ρ2 Hρ.

  - (* BStep_ret *)
    edestruct (env_eqv_get Hρ x) as [v1' [v2' [Hg1 [Hg2 Hv]]]].
    { apply HF. constructor. }
    rewrite H in Hg1; inv Hg1.
    exists (Res v2'); split; eauto.

  - (* BStep_fun *)
    assert (HFk : occurs_free k \subset (f |: (occurs_free (Efun f w xs e k))))
      by apply free_fun_k_subset.
    destruct (IHHb _ HFk (M.set f (Tag w (Vfun f ρ2 xs e)) ρ2)) as [r2 [Hr2 Hs]].
    + eapply env_eqv_set; eauto.
      constructor.
      econstructor; eauto.
      * eapply Included_trans; eauto.
        apply free_fun_e_subset.
        apply Included_Union_compat.
        apply Included_refl.
        apply Included_Union_compat; eauto.
        apply Included_refl.
      * eapply env_eqv_subset; eauto.
    + eexists; split; eauto.

  - (* BStep_app *)
    edestruct (env_eqv_get Hρ f) as [vf1 [vf2 [Hgf1 [Hgf2 Hvf]]]].
    { apply HF. constructor. }
    rewrite H in Hgf1; inv Hgf1.
    inversion Hvf as [v1a v2a w0 Hvf']; subst; clear Hvf.
    inversion Hvf' as [Γclo fclo xsclo eclo ρclo1 ρclo2 HFVe Hρcloeq | | ]; subst; clear Hvf'.
    edestruct (env_eqv_get_lists Hρ xs) as [vs2 [Hgvs2 Hvs2]]; eauto.
    { eapply Included_trans; [|eassumption]. apply free_app_xs_subset. }

    assert (Hlen : length xs' = length vs2).
    { erewrite <- (Forall2_length _ _ _ Hvs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto. }
    destruct (set_lists_length3
                (M.set f' (Tag w' (Vfun f' ρclo2 xs' e)) ρclo2)
                _ _ Hlen) as [ρ2' Heqρ2'].

    edestruct (IHHb _ HFVe ρ2') as [r2 [Hr2 Hs]].
    + eapply env_eqv_set_lists; eauto.
      eapply env_eqv_set; eauto.
    + exists r2; split; auto.
      eapply BStep_app; eauto.

  - (* BStep_letapp_Res *)
    edestruct (env_eqv_get Hρ f) as [vf1 [vf2 [Hgf1 [Hgf2 Hvf]]]].
    { apply HF. constructor. }
    rewrite H in Hgf1; inv Hgf1.
    inversion Hvf as [v1a v2a w0 Hvf']; subst; clear Hvf.
    inversion Hvf' as [Γclo fclo xsclo eclo ρclo1 ρclo2 HFVe Hρcloeq | | ]; subst; clear Hvf'.
    edestruct (env_eqv_get_lists Hρ xs) as [vs2 [Hgvs2 Hvs2]]; eauto.
    { eapply Included_trans; [|eassumption]. apply free_letapp_xs_subset. }

    assert (Hlen : length xs' = length vs2).
    { erewrite <- (Forall2_length _ _ _ Hvs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto. }
    destruct (set_lists_length3
                (M.set f' (Tag w' (Vfun f' ρclo2 xs' e)) ρclo2)
                _ _ Hlen) as [ρ2' Heqρ2'].

    edestruct (IHHb _ HFVe ρ2') as [r2 [Hr2 Hs]].
    + eapply env_eqv_set_lists; eauto.
      eapply env_eqv_set; eauto.
    + inv Hs.
      assert (HFk : occurs_free k \subset (x |: Γ)) by (eapply free_letapp_k_inv; eauto).
      destruct (IHHb0 _ HFk (M.set x v2 ρ2)) as [r3 [Hr3 Hs']].
      * eapply env_eqv_set; eauto.
      * exists r3; split; auto.
        econstructor; eauto.

  - (* BStep_letapp_OOT *)
    edestruct (env_eqv_get Hρ f) as [vf1 [vf2 [Hgf1 [Hgf2 Hvf]]]].
    { apply HF. constructor. }
    rewrite H in Hgf1; inv Hgf1.
    inversion Hvf as [v1a v2a w0 Hvf']; subst; clear Hvf.
    inversion Hvf' as [Γclo fclo xsclo eclo ρclo1 ρclo2 HFVe Hρcloeq | | ]; subst; clear Hvf'.
    edestruct (env_eqv_get_lists Hρ xs) as [vs2 [Hgvs2 Hvs2]]; eauto.
    { eapply Included_trans; [|eassumption]. apply free_letapp_xs_subset. }

    assert (Hlen : length xs' = length vs2).
    { erewrite <- (Forall2_length _ _ _ Hvs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto. }
    destruct (set_lists_length3
                (M.set f' (Tag w' (Vfun f' ρclo2 xs' e)) ρclo2)
                _ _ Hlen) as [ρ2' Heqρ2'].

    edestruct (IHHb _ HFVe ρ2') as [r2 [Hr2 Hs]].
    + eapply env_eqv_set_lists; eauto.
      eapply env_eqv_set; eauto.
    + inv Hs.
      exists OOT; split; auto.
      econstructor; eauto.

  - (* BStep_constr *)
    edestruct (env_eqv_get_lists Hρ xs) as [vs2 [Hgvs2 Hvs2]]; eauto.
    { eapply Included_trans; [|eassumption]. apply free_constr_xs_subset. }

    assert (HFk : occurs_free e \subset (x |: Γ)) by (eapply free_constr_k_inv; eauto).
    destruct (IHHb _ HFk (M.set x (Tag w (Vconstr t vs2)) ρ2)) as [r2 [Hr2 Hs]].
    + eapply env_eqv_set; eauto.
      eapply val_eqv_Vconstr; eauto.
    + exists r2; split; auto.
      econstructor; eauto.

  - (* BStep_proj *)
    edestruct (env_eqv_get Hρ y) as [vy1 [vy2 [Hgy1 [Hgy2 Hvy]]]].
    { apply HF. constructor. }
    rewrite H in Hgy1; inv Hgy1.
    edestruct (val_eqv_Vconstr_inv_l Hvy) as [vs2 [Heqvs2 Hvs2]]; subst.
    edestruct (Forall2_nth_error H0 Hvs2) as [v' [Heqv' Hv']].
    assert (HFk : occurs_free e \subset (x |: Γ)) by (eapply free_proj_k_inv; eauto).
    destruct (IHHb _ HFk (M.set x v' ρ2)) as [r2 [Hr2 Hs]].
    + eapply env_eqv_set; eauto.
    + exists r2; split; auto.
      econstructor; eauto.

  - (* BStep_case *)
    edestruct (env_eqv_get Hρ x) as [vx1 [vx2 [Hgx1 [Hgx2 Hvx]]]].
    { apply HF. constructor. }
    rewrite H in Hgx1; inv Hgx1.
    edestruct (val_eqv_Vconstr_inv_l Hvx) as [vs2 [Heqvs2 Hvs2]]; subst.
    assert (HFe : occurs_free e \subset Γ) by (eapply free_case_e_inv; eauto).
    destruct (IHHb _ HFe _ Hρ) as [r2 [Hr2 Hs]].
    exists r2; split; auto.
    eapply BStep_case; eauto.

  - (* BStepF_OOT *)
    exists OOT; split; auto.

  - (* BStepF_Step *)
    edestruct IHHb as [r2 [Hr2 Hs]]; eauto.
Qed.

Lemma bstep_fuel_env_eqv_l {Γ ρ1 ρ2 e c r1}:
  (occurs_free e) \subset Γ ->
  env_eqv Γ ρ1 ρ2 ->
  bstep_fuel ρ1 e c r1 ->
  (exists r2, bstep_fuel ρ2 e c r2 /\ res_eqv r1 r2).
Proof.
  intros.
  inv H1.
  - exists OOT; split; auto.
  - destruct (bstep_env_eqv_l H H0 H2) as [r2 [Hr2 Hs]].
    exists r2; split; auto.
Qed.

Lemma bstep_fuel_drop_unused {Γ f val ρ e c r}:
  ~ (f \in occurs_free e) ->
  occurs_free e \subset Γ ->
  wf_env Γ ρ ->
  bstep_fuel (M.set f val ρ) e c r ->
  exists r', bstep_fuel ρ e c r' /\ res_eqv r r'.
Proof.
  intros Hf HF Hwf Hcb.
  eapply @bstep_fuel_env_eqv_l with (Γ := occurs_free e); eauto.
  - apply Included_refl.
  - constructor; intros z Hz.
    destruct (M.elt_eq z f) as [<-|Hne]; [contradiction|].
    inv Hwf.
    edestruct H0 as [w Hgw]; eauto.
    exists w, w. repeat split; auto.
    + rewrite M.gso by auto. assumption.
    + apply val_eqv_refl. eapply H; eauto.
Qed.

Lemma bstep_env_eqv_r {Γ ρ1 ρ2 e c r2}:
  (occurs_free e) \subset Γ ->
  env_eqv Γ ρ1 ρ2 ->
  bstep ρ2 e c r2 ->
  (exists r1, bstep ρ1 e c r1 /\ res_eqv r1 r2).
Proof.
  intros HF Hρ Hb.
  apply env_eqv_sym in Hρ.
  edestruct (bstep_env_eqv_l HF Hρ Hb) as [r1 [Hr1 Hs]].
  exists r1; split; auto.
  apply res_eqv_sym; assumption.
Qed. 

Lemma bstep_fuel_env_eqv_r {Γ ρ1 ρ2 e c r2}:
  (occurs_free e) \subset Γ ->
  env_eqv Γ ρ1 ρ2 ->
  bstep_fuel ρ2 e c r2 ->
  (exists r1, bstep_fuel ρ1 e c r1 /\ res_eqv r1 r2).
Proof.
  intros.
  inv H1.
  - exists OOT; split; auto.
  - destruct (bstep_env_eqv_r H H0 H2) as [r1 [Hr1 Hs]].
    exists r1; split; auto.
Qed.
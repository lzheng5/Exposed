From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

Require Import Framework.Util.

(* Untyped λANF with Exposed Webs *)

Module M := Maps.PTree.
Definition var := M.elt.
Definition vars := Ensemble var.
Definition web := M.elt.
Definition webs := Ensemble web.
Definition ctor_tag := M.elt.

Parameter Exposed : webs.

Parameter exposed_dec : Decidable Exposed.

Parameter exposedb : web -> bool.

Axiom exposed_reflect : forall w, Bool.reflect (w \in Exposed) (exposedb w).

(* Syntax *)
Inductive exp : Type :=
| Eret : var -> exp
| Eapp : var -> web -> list var -> exp
| Eletapp : var -> var -> web -> list var -> exp -> exp
| Efun : var -> web -> list var -> exp -> exp -> exp
| Econstr : var -> web -> ctor_tag -> list var -> exp -> exp
| Ecase : var -> web -> list (ctor_tag * exp) -> exp
| Eproj : var -> web -> nat -> var -> exp -> exp.

Hint Constructors exp : core.

Lemma exp_ind' :
  forall P : exp -> Type,
    (forall (x : var), P (Eret x)) ->
    (forall (x : var) (w : web) (xs : list var), P (Eapp x w xs)) ->
    (forall f w xs (e k : exp), P e -> P k -> P (Efun f w xs e k)) ->
    (forall (x f : var) (w : web) (xs : list var) (e : exp),
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
  - induction l.
    + eapply H6.
    + destruct a.
      eapply H7.
      eapply exp_ind'; eauto.
      apply IHl.
  - eapply H8. eapply exp_ind'; eauto.
Qed.

(* Tagged Value *)
Inductive tag A : Type :=
| TAG : web -> A -> tag A.

Hint Constructors tag : core.

(* Value *)
Inductive val : Type :=
| Vfun : var -> M.t (tag val) -> list var -> exp -> val
| Vconstr : ctor_tag -> list (tag val) -> val.

Hint Constructors val : core.

(* Tagged Value *)
Definition wval := tag val.

Definition Tag w v := TAG val w v.

(* Environment *)
Definition env := M.t wval.

(* Exposed Value *)
Inductive exposed : wval -> Prop :=
| Exp_fun :
  forall w f ρ xs e,
    (w \in Exposed) ->
    exposed (Tag w (Vfun f ρ xs e))

| Exp_constr :
  forall w c vs,
    (w \in Exposed) ->
    Forall exposed vs ->
    exposed (Tag w (Vconstr c vs)).

Hint Constructors exposed : core.

(* Well-formed Value and Environment *)
Inductive wf_val : wval -> Prop :=
| WF_TAG :
  forall w v,
    (w \in Exposed -> exposed (Tag w v)) ->
    wf_val' v ->
    wf_val (Tag w v)

with wf_val' : val -> Prop :=
| WF_Vfun:
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

(* Result *)
Inductive res : Type :=
| OOT
| Res : wval -> res.

Hint Constructors res : core.

(* Exposed Result *)
Inductive exposed_res : res -> Prop :=
| Exp_OOT :
  exposed_res OOT

| Exp_Res :
  forall wv,
    exposed wv ->
    exposed_res (Res wv).

Hint Constructors exposed_res : core.

(* Well-formed Result *)
Inductive wf_res : res -> Prop :=
| WF_OOT :
  wf_res OOT

| WF_Res :
  forall v,
    wf_val v ->
    wf_res (Res v).

Hint Constructors wf_res : core.

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

Inductive bstep (ex : bool) (ρ : env) : exp -> fuel -> res -> Prop :=
| BStep_ret :
  forall {x wv},
    M.get x ρ = Some wv ->
    bstep ex ρ (Eret x) 0 (Res wv)

| BStep_fun :
  forall {f w xs e k c r},
    bstep_fuel ex (M.set f (Tag w (Vfun f ρ xs e)) ρ) k c r ->
    bstep ex ρ (Efun f w xs e k) c r

| BStep_app :
  forall {f f' w xs ρ' xs' e vs ρ'' c r},
    M.get f ρ = Some (Tag w (Vfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w (Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    bstep_fuel (exposedb w) ρ'' e c r ->
    (w \in Exposed -> Forall exposed vs /\ exposed_res r) ->
    bstep ex ρ (Eapp f w xs) c r

| BStep_letapp_Res :
  forall {x f f' w xs k ρ' xs' e vs ρ'' c c' v r},
    M.get f ρ = Some (Tag w (Vfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w (Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    bstep_fuel (exposedb w) ρ'' e c (Res v) ->
    (w \in Exposed -> Forall exposed vs /\ exposed v) ->
    bstep_fuel ex (M.set x v ρ) k c' r ->
    bstep ex ρ (Eletapp x f w xs k) (c + c') r

| BStep_letapp_OOT :
  forall {x f f' w xs k ρ' xs' e vs ρ'' c},
    M.get f ρ = Some (Tag w (Vfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w (Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    bstep_fuel (exposedb w) ρ'' e c OOT ->
    (w \in Exposed -> Forall exposed vs) ->
    bstep ex ρ (Eletapp x f w xs k) c OOT

| BStep_constr :
  forall {x w t xs e r vs c},
    get_list xs ρ = Some vs ->
    (w \in Exposed -> Forall exposed vs) ->
    bstep_fuel ex (M.set x (Tag w (Vconstr t vs)) ρ) e c r ->
    bstep ex ρ (Econstr x w t xs e) c r

| BStep_proj :
  forall {x w t i y e c r v vs},
    M.get y ρ = Some (Tag w (Vconstr t vs)) ->
    nth_error vs i = Some v ->
    bstep_fuel ex (M.set x v ρ) e c r ->
    bstep ex ρ (Eproj x w i y e) c r

| BStep_case :
  forall {x w cl t e r c vs},
    M.get x ρ = Some (Tag w (Vconstr t vs)) ->
    find_tag cl t e ->
    bstep_fuel ex ρ e c r ->
    bstep ex ρ (Ecase x w cl) c r

with bstep_fuel (ex : bool) (ρ : env) : exp -> fuel -> res -> Prop :=
| BStepF_OOT :
  forall {e},
    bstep_fuel ex ρ e 0 OOT

| BStepF_Step :
  forall {e c r},
    bstep ex ρ e c r ->
    (if ex then exposed_res r else True) ->
    bstep_fuel ex ρ e (S c) r.

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

Theorem bstep_deterministic v v' {ex ρ e c c' r r'}:
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
    rewrite H in H5; inv H5; auto.
  - inv H0.
    edestruct IHbstep; eauto.
  - inv H4.
    rewrite H in H8; inv H8.
    rewrite H0 in H9; inv H9.
    rewrite H1 in H10; inv H10.
    edestruct IHbstep; eauto.
  - inv H5.
    rewrite H in H11; inv H11.
    rewrite H0 in H12; inv H12.
    rewrite H1 in H15; inv H15.
    edestruct IHbstep; eauto.
    subst.
    edestruct IHbstep0; eauto.
  - inv H5.
  - inv H2.
    rewrite H in H10; inv H10.
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
  - inv H1.
    edestruct IHbstep; eauto.
Qed.

Theorem bstep_fuel_deterministic v v' {ex ρ e c c' r r'}:
    bstep_fuel ex ρ e c r ->
    bstep_fuel ex ρ e c' r' ->
    r = Res v ->
    r' = Res v' ->
    (v = v' /\ c = c').
Proof.
  intros.
  inv H; inv H0; try discriminate.
  edestruct (bstep_deterministic v v' H3 H); eauto.
Qed.

Lemma bstep_exposed {r1 ex ex' ρ1 e c}:
  bstep ex ρ1 e c r1 ->
  exposed_res r1 ->
  bstep ex' ρ1 e c r1.
Proof.
  intros H.
  generalize dependent ex'.
  induction H using bstep_ind' with (P0 := fun ex ρ1 e c r1 =>
                                             forall ex',
                                               exposed_res r1 ->
                                               bstep_fuel ex' ρ1 e c r1); intros; eauto.
  constructor; eauto.
  destruct ex'; auto.
Qed.

Lemma bstep_fuel_exposed {r1 ex ex' ρ1 e c}:
  bstep_fuel ex ρ1 e c r1 ->
  exposed_res r1 ->
  bstep_fuel ex' ρ1 e c r1.
Proof.
  intros.
  inv H; constructor; auto.
  eapply bstep_exposed; eauto.
  destruct ex'; auto.
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

(* Lemmas about [wf_val] and [wf_env] *)
Lemma wf_env_get ρ :
  wf_env ρ ->
  forall x v,
    ρ ! x = Some v ->
    wf_val v.
Proof.
  intros.
  inv H; eauto.
Qed.

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
  - rewrite M.gss in *; auto.
    inv H; simpl; auto.
  - rewrite M.gso in *; auto.
    eapply H1; eauto.
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
    inv H2.
    inv H.
    rename e into x0.
    constructor; intros.
    destruct (M.elt_eq x0 x); subst.
    + rewrite M.gss in *; auto.
      inv H; auto.
    + rewrite M.gso in *; auto.
      rename t into ρ'.
      assert (wf_env ρ').
      eapply IHvs; eauto.
      eapply wf_env_get; eauto.
Qed.

Lemma wf_val_Vconstr c w vs :
  Forall wf_val vs ->
  (w \in Exposed -> Forall exposed vs) ->
  wf_val (Tag w (Vconstr c vs)).
Proof.
  intros H.
  induction H; simpl; auto; intros.
  assert (wf_val (Tag w (Vconstr c l))).
  {
    apply IHForall.
    intros.
    apply H1 in H2.
    inv H2; auto.
  }
  inv H2.
  constructor; auto.
Qed.

Lemma wf_val_Vconstr_inv {w c vs} :
  wf_val (Tag w (Vconstr c vs)) ->
  (Forall wf_val vs /\ (w \in Exposed -> Forall exposed vs)).
Proof.
  intros.
  remember (Tag w (Vconstr c vs)) as v.
  revert c vs Heqv.
  induction H using wf_val_mut with (P0 := fun v wf =>
                                             forall (c : ctor_tag) (vs : list (tag val)),
                                               v = (Vconstr c vs) ->
                                               Forall wf_val vs)
                                    (P1 := fun ρ wf => True);
    intros; eauto.
  - inv Heqv.
    split; eauto; intros.
    apply e in H.
    inv H; eauto.
  - inv H.
  - inv H; auto.
  - inv H0.
    constructor; eauto.
Qed.

Lemma bstep_wf_res ρ ex e c r :
  wf_env ρ ->
  bstep ex ρ e c r ->
  wf_res r.
Proof.
  intros Hw H.
  induction H using bstep_ind' with (P0 := fun ex ρ e c r => wf_env ρ -> wf_res r); intros; auto.
  - constructor.
    eapply wf_env_get; eauto.
  - apply IHbstep.
    eapply wf_env_set; eauto.
  - apply IHbstep.
    eapply (wf_env_set_lists (M.set f' (Tag w (Vfun f' ρ' xs' e)) ρ')) with (xs := xs') (vs := vs); eauto.
    + eapply wf_env_set; eauto.
      eapply wf_env_get in H; eauto.
      inv H.
      inv H7; auto.
      eapply wf_env_get; eauto.
    + eapply wf_env_get_list; eauto.
  - apply IHbstep0.
    eapply wf_env_set; eauto.
    assert (wf_res (Res v)).
    {
      apply IHbstep.
      eapply (wf_env_set_lists (M.set f' (Tag w (Vfun f' ρ' xs' e)) ρ')) with (xs := xs') (vs := vs); eauto.
      - eapply wf_env_set; eauto.
        eapply wf_env_get in H; eauto.
        inv H.
        inv H8; auto.
        eapply wf_env_get; eauto.
      - eapply wf_env_get_list; eauto.
    }
    inv H5; auto.
  - apply IHbstep.
    eapply wf_env_set; eauto.
    eapply wf_val_Vconstr; eauto.
    eapply wf_env_get_list; eauto.
  - apply IHbstep.
    eapply wf_env_set; eauto.
    eapply wf_env_get in H; eauto.
    destruct (wf_val_Vconstr_inv H).
    edestruct (Forall_nth_error H0 H2) as [v' [Heqv' H']]; eauto.
    rewrite Heqv' in H0; inv H0; auto.
Qed.

Lemma bstep_fuel_wf_res ρ ex e c r :
  wf_env ρ ->
  bstep_fuel ex ρ e c r ->
  wf_res r.
Proof.
  intros.
  inv H0; auto.
  eapply bstep_wf_res; eauto.
Qed.

(* Sub Value and Environment *)
(* These definitions and lemmas are set up to show [bstep_subenv],
 * which is handy to reason about join points without explicit language construct *)
Inductive subval : wval -> wval -> Prop :=
| Sub_wval :
  forall v1 v2 w,
    subval' v1 v2 ->
    subval (Tag w v1) (Tag w v2)

with subval' : val -> val -> Prop :=
| Sub_fun :
  forall Γ f xs e ρ1 ρ2 ,
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
  intros.
  constructor.
  inv H0.
  inv H.
  intros.
  destruct (var_dec x x0); subst.
  - rewrite M.gss in *.
    inv H2; eauto.
  - rewrite M.gso in *; auto.
    eapply H1; eauto.
    inv H; auto.
    inv H3; contradiction.
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
    inv H0; auto.
    inv H2.
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

Lemma subval_exposed v1 v2 :
  subval v1 v2 ->
  exposed v1 ->
  exposed v2.
Proof.
  intros H.
  induction H using subval_mut with (P0 := fun v1' v2' sub =>
                                             match v1', v2' with
                                             | Vfun f1 ρ1 xs1 e1, Vfun f2 ρ2 xs2 e2 => True
                                             | Vconstr c1 vs1, Vconstr c2 vs2 => Forall exposed vs1 -> Forall exposed vs2
                                             | _, _ => False
                                             end)
                                    (P1 := fun Γ ρ1 ρ2 sub => True);
    intros; auto.
  inv s.
  - inv H; auto.
  - inv H; auto.
  - inv H; auto.
  - inv H0; auto.
Qed.

Lemma subval_exposed_Forall vs1 vs2 :
  Forall2 subval vs1 vs2 ->
  Forall exposed vs1 ->
  Forall exposed vs2.
Proof.
  intros H.
  induction H; simpl; intros; auto.
  inv H1; constructor; auto.
  eapply subval_exposed; eauto.
Qed.

Lemma subres_exposed r1 r2:
  subres r1 r2 ->
  exposed_res r1 ->
  exposed_res r2.
Proof.
  intros.
  inv H; auto.
  inv H0; constructor.
  eapply subval_exposed; eauto.
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
  induction H using subval_mut with (P0 := fun v1' v2' sub =>
                                             match v1', v2' with
                                             | Vfun f1 ρ1 xs1 e1, Vfun f2 ρ2 xs2 e2 => True
                                             | Vconstr c1 vs1, Vconstr c2 vs2 => Forall2 subval vs1 vs2
                                             | _, _ => False
                                             end)
                                    (P1 := fun Γ ρ1 ρ2 sub => True);
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
  induction H using wf_val_mut with (P0 := fun v wf =>
                                             match v with
                                             | Vfun f ρ xs e => subenv (occurs_free e) ρ ρ
                                             | Vconstr c vs => Forall2 subval vs vs
                                             end)
                                    (P1 := fun ρ wf => forall Γ, subenv Γ ρ ρ); eauto.
  destruct v.
  - constructor; auto.
    eapply (Sub_fun (occurs_free e0)); eauto.
    unfold Ensembles.Included, Ensembles.In, FromList.
    intros.
    repeat apply Union_intror; auto.
  - eapply subval_Vconstr; eauto.
Qed.

Lemma subval_refl_Forall vs :
  Forall wf_val vs ->
  Forall2 subval vs vs.
Proof.
  intros H.
  induction H; constructor; auto.
  apply subval_refl; auto.
Qed.

(* Semantic Weakening Lemmas *)
Lemma bstep_subenv {ex Γ ρ1 ρ2 e c r1}:
  wf_env ρ2 ->
  (occurs_free e) \subset Γ ->
  subenv Γ ρ1 ρ2 ->
  bstep ex ρ1 e c r1 ->
  (exists r2, bstep ex ρ2 e c r2 /\ subres r1 r2 /\ wf_res r2).
Proof.
  intros Hρ2. intros.
  generalize dependent ρ2.
  generalize dependent Γ.
  induction H1 using bstep_ind' with (P0 := fun ex ρ1 e c r =>
                                              forall Γ,
                                                occurs_free e \subset Γ ->
                                                forall ρ2,
                                                  wf_env ρ2 ->
                                                  subenv Γ ρ1 ρ2 ->
                                                  (exists r2, bstep_fuel ex ρ2 e c r2 /\ subres r r2 /\ wf_res r2)); intros; subst.
  - edestruct (subenv_get H1 x) as [v2' [Heqv2' Hv]]; eauto.
    exists (Res v2'); repeat split; auto.
    constructor.
    eapply wf_env_get; eauto.

  - assert (occurs_free k \subset (f |: (occurs_free (Efun f w xs e k)))) by apply free_fun_k_subset.
    destruct (IHbstep _ H2 (M.set f (Tag w (Vfun f ρ2 xs e)) ρ2)) as [r2 [Hr2 Hr]].
    + eapply wf_env_set; eauto.
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

  - edestruct (subenv_get H5 f) as [f2 [Heqf2 Hf2]]; eauto.
    inv Hf2.
    inv H9.
    edestruct (subenv_get_lists H5 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_app_xs_subset.

    assert (Hlen : length xs' = length vs2).
    {
      erewrite <- (Forall2_length _ vs vs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto.
    }
    destruct (set_lists_length3 (M.set f' (Tag w (Vfun f' ρ0 xs' e)) ρ0) _ _ Hlen) as [ρ2' Heqρ2'].

    edestruct (IHbstep _ H12 ρ2') as [r2 [Hr2 [Hs Hr]]]; eauto.
    + assert (wf_val (Tag w (Vfun f' ρ0 xs' e))) by (eapply wf_env_get; eauto).
      eapply (wf_env_set_lists (M.set f' (Tag w (Vfun f' ρ0 xs' e)) ρ0)) with (xs := xs') (vs := vs2); eauto.
      eapply wf_env_set; eauto.
      inv H6.
      inv H10; auto.
      eapply wf_env_get_list; eauto.
    + eapply subenv_set_lists; eauto.
      eapply subenv_set; eauto.
    + exists r2; split; auto.
      eapply BStep_app; eauto.
      intros.
      destruct H3; auto.
      split; auto.
      eapply subval_exposed_Forall; eauto.
      eapply subres_exposed; eauto.

  - edestruct (subenv_get H6 f) as [v2 [Heqv2 Hv2]]; eauto.
    inv Hv2.
    inv H10.
    edestruct (subenv_get_lists H6 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_letapp_xs_subset.

    assert (Hlen : length xs' = length vs2).
    {
      erewrite <- (Forall2_length _ vs vs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto.
    }
    destruct (set_lists_length3 (M.set f' (Tag w (Vfun f' ρ0 xs' e)) ρ0) _ _ Hlen) as [ρ2' Heqρ2'].
    assert (wf_val (Tag w (Vfun f' ρ0 xs' e))) by (eapply wf_env_get; eauto).

    destruct (IHbstep _ H13 ρ2') as [r2 [Hr2 [Hs Hr]]]; auto.
    + eapply (wf_env_set_lists (M.set f' (Tag w (Vfun f' ρ0 xs' e)) ρ0)) with (xs := xs') (vs := vs2) ; eauto.
      eapply wf_env_set; eauto.
      inv H7.
      inv H11; auto.
      eapply wf_env_get_list; eauto.
    + eapply subenv_set_lists; eauto.
      eapply subenv_set; eauto.
    + inv Hs.
      assert (occurs_free k \subset (x |: Γ)) by (eapply free_letapp_k_inv; eauto).
      destruct (IHbstep0 _ H8 (M.set x v2 ρ2)) as [r3 [Hr3 [Hs' Hr']]]; auto.
      * eapply wf_env_set; eauto.
        inv Hr; auto.
      * eapply subenv_set; eauto.
      * exists r3; repeat (split; auto).
        econstructor; eauto.
        intros.
        destruct H3; auto.
        split.
        -- eapply subval_exposed_Forall; eauto.
        -- eapply subval_exposed; eauto.

  - edestruct (subenv_get H5 f) as [v2 [Heqv2 Hv2]]; eauto.
    inv Hv2.
    inv H9.
    edestruct (subenv_get_lists H5 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_letapp_xs_subset.

    assert (Hlen : length xs' = length vs2).
    {
      erewrite <- (Forall2_length _ vs vs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto.
    }
    destruct (set_lists_length3 (M.set f' (Tag w (Vfun f' ρ0 xs' e)) ρ0) _ _ Hlen) as [ρ2' Heqρ2'].
    assert (wf_val (Tag w (Vfun f' ρ0 xs' e))) by (eapply wf_env_get; eauto).

    destruct (IHbstep _ H12 ρ2') as [r2 [Hr2 [Hs Hr]]]; auto.
    + eapply (wf_env_set_lists (M.set f' (Tag w (Vfun f' ρ0 xs' e)) ρ0)) with (xs := xs') (vs := vs2) ; eauto.
      eapply wf_env_set; eauto.
      inv H6.
      inv H10; auto.
      eapply wf_env_get_list; eauto.
    + eapply subenv_set_lists; eauto.
      eapply subenv_set; eauto.
    + inv Hs.
      exists OOT; split; auto.
      econstructor; eauto.
      intros.
      eapply subval_exposed_Forall; eauto.

  - edestruct (subenv_get_lists H3 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_constr_xs_subset.

    assert (occurs_free e \subset (x |: Γ)) by (eapply free_constr_k_inv; eauto).
    destruct (IHbstep _ H4 (M.set x (Tag w (Vconstr t vs2)) ρ2)) as [r2 [Hr2 [Hs Hr]]].
    + eapply wf_env_set; eauto.
      apply wf_val_Vconstr; auto.
      eapply wf_env_get_list; eauto.
      intros.
      eapply subval_exposed_Forall; eauto.
    + eapply subenv_set; eauto.
      eapply subval_Vconstr; eauto.
    + exists r2; split; auto.
      econstructor; eauto.
      intros.
      eapply subval_exposed_Forall; eauto.

  - edestruct (subenv_get H3 y) as [f2 [Heqf2 Hf2]]; eauto.
    edestruct (subval_Vconstr_inv_l Hf2) as [vs2 [Heqvs2 Hvs2]]; eauto; subst.
    edestruct (Forall2_nth_error H0 Hvs2) as [v' [Heqv' Hv]]; eauto.
    assert (occurs_free e \subset (x |: Γ)) by (eapply free_proj_k_inv; eauto).
    destruct (IHbstep _ H4 (M.set x v' ρ2)) as [r2 [Hr2 [Hs Hr]]].
    + eapply wf_env_set; eauto.
      eapply nth_error_In in Heqv'.
      assert (wf_val (Tag w (Vconstr t vs2))) by (eapply wf_env_get; eauto).
      destruct (wf_val_Vconstr_inv H5) as [HF HW].
      eapply Forall_forall; eauto.
    + eapply subenv_set; eauto.
    + exists r2; split; auto.
      econstructor; eauto.

  - edestruct (subenv_get H3 x) as [v2 [Heqv2 Hv2]]; eauto.
    edestruct (subval_Vconstr_inv_l Hv2) as [vs2 [Heqvs2 Hvs2]]; eauto; subst.
    edestruct IHbstep as [r2 [Hr2 [Hs Hr]]]; eauto.
    eapply free_case_e_inv; eauto.

  - exists OOT; split; auto.

  - edestruct IHbstep as [r2 [Hr2 [Hs Hr]]]; eauto.
    assert (if ex then exposed_res r2 else True).
    {
      destruct ex; auto.
      eapply subres_exposed; eauto.
    }
    exists r2; split; auto.
Qed.

Lemma bstep_fuel_subenv ex Γ ρ1 ρ2 e c r1:
  wf_env ρ2 ->
  (occurs_free e) \subset Γ ->
  subenv Γ ρ1 ρ2 ->
  bstep_fuel ex ρ1 e c r1 ->
  (exists r2, bstep_fuel ex ρ2 e c r2 /\ subres r1 r2 /\ wf_res r2).
Proof.
  intros.
  inv H2.
  - exists OOT; split; constructor; auto.
  - destruct (bstep_subenv H H0 H1 H3) as [r2 [Hr2 [Hs Hr]]]; eauto.
    assert (if ex then exposed_res r2 else True).
    {
      destruct ex; auto.
      eapply subres_exposed; eauto.
    }
    exists r2; split; auto.
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

| Web_constr1 :
  forall x w c xs e,
    has_web (Econstr x w c xs e) w

| Web_constr2 :
  forall x w w' c xs e,
    has_web e w' ->
    has_web (Econstr x w c xs e) w'

| Web_proj1 :
  forall x w i y e,
    has_web (Eproj x w i y e) w

| Web_proj2 :
  forall x w w' i y e,
    has_web e w' ->
    has_web (Eproj x w i y e) w'

| Web_case1 :
  forall x w cl,
    has_web (Ecase x w cl) w

| Web_case2 :
  forall x w w' c e cl,
    has_web e w' ->
    has_web (Ecase x w ((c, e) :: cl)) w'

| Web_case3 :
  forall x w w' c e cl,
    has_web (Ecase x w cl) w' ->
    has_web (Ecase x w ((c, e) :: cl)) w'.

Hint Constructors has_web : core.

(* Identifiers *)
Inductive has_id : exp -> vars :=
| Id_ret :
  forall x,
    has_id (Eret x) x

| Id_fun1 :
  forall f w xs e k,
    has_id (Efun f w xs e k) f

| Id_fun2 :
  forall x f w xs e k,
    In x xs ->
    has_id (Efun f w xs e k) x

| Id_fun3 :
  forall x f w xs e k,
    has_id e x ->
    has_id (Efun f w xs e k) x

| Id_fun4 :
  forall x f w xs e k,
    has_id k x ->
    has_id (Efun f w xs e k) x

| Id_app1 :
  forall f w xs,
    has_id (Eapp f w xs) f

| Id_app2 :
  forall x f w xs,
    In x xs ->
    has_id (Eapp f w xs) x

| Id_letapp1 :
  forall x f w xs k,
    has_id (Eletapp x f w xs k) x

| Id_letapp2 :
  forall x f w xs k,
    has_id (Eletapp x f w xs k) f

| Id_letapp3 :
  forall y x f w xs k,
    In y xs ->
    has_id (Eletapp x f w xs k) y

| Id_letapp4 :
  forall y x f w xs k,
    has_id k y ->
    has_id (Eletapp x f w xs k) y

| Id_constr1 :
  forall x w c xs e,
    has_id (Econstr x w c xs e) x

| Id_constr2 :
  forall y x w c xs e,
    In y xs ->
    has_id (Econstr x w c xs e) y

| Id_constr3 :
  forall y x w c xs e,
    has_id e y ->
    has_id (Econstr x w c xs e) y

| Id_proj1 :
  forall x w i y e,
    has_id (Eproj x w i y e) x

| Id_proj2 :
  forall x w  i y e,
    has_id (Eproj x w i y e) y

| Id_proj3 :
  forall z y x w i e,
    has_id e z ->
    has_id (Eproj x w i y e) z

| Id_case1 :
  forall x w cl,
    has_id (Ecase x w cl) x

| Id_case2 :
  forall y x w c e cl,
    has_id e y ->
    has_id (Ecase x w ((c, e) :: cl)) y.

Hint Constructors has_id : core.

Inductive bound_var : exp -> vars :=
| Bound_Econstr1 :
    forall x w t ys e,
      bound_var (Econstr x w t ys e) x

| Bound_Econstr2 :
    forall y x w t ys e,
      bound_var e y ->
      bound_var (Econstr x w t ys e) y

| Bound_Eproj1 :
    forall x y w i e,
      bound_var (Eproj x w i y e) x

| Bound_Eproj2 :
    forall y x w i y' e,
      bound_var e y ->
      bound_var (Eproj x w i y' e) y

| Bound_Eletapp1 :
    forall x f w ys e,
      bound_var (Eletapp x f w ys e) x

| Bound_Eletapp2 :
    forall y x f w ys e,
      bound_var e y ->
      bound_var (Eletapp x f w ys e) y

| Bound_Ecase :
    forall x y w c e cl,
      bound_var e y ->
      List.In (c, e) cl ->
      bound_var (Ecase x w cl) y

| Bound_Efun1 :
    forall f w xs e k,
      bound_var (Efun f w xs e k) f

| Bound_Efun2 :
    forall y f w xs e k,
      List.In y xs ->
      bound_var (Efun f w xs e k) y

| Bound_Efun3 :
    forall y f w xs e k,
      bound_var e y ->
      bound_var (Efun f w xs e k) y.

Hint Constructors bound_var : core.

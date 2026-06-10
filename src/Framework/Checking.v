From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Util W0 ANF ANF1.

Definition web_map := M.t web.

(* Checking Semantics *)

(* Tagged Value *)
Inductive ctag A : Type :=
| CTAG : label -> web_map -> A -> ctag A.

Hint Constructors tag : core.

(* Value *)
Inductive cval : Type :=
| CVfun : var -> M.t (ctag cval) -> list var -> exp -> cval
| CVconstr : ctor_tag -> list (ctag cval) -> cval.

Hint Constructors cval : core.

Definition clval := ctag cval.

Definition CTag l W cv := CTAG cval l W cv.

(* Environment *)
Definition cenv := M.t clval.

(* Result *)
Inductive cres : Type :=
| COOT
| CRes : clval -> cres.

Hint Constructors cres : core.

Inductive to_exposed : clval -> Prop :=
| ToExp_cfun :
  forall W l w f ρ xs e,
    W ! l = Some w ->
    (w \in Exposed) ->
    to_exposed (CTag l W (CVfun f ρ xs e))

| ToExp_cconstr :
  forall W l w c vs,
    W ! l = Some w ->
    (w \in Exposed) ->
    Forall to_exposed vs ->
    to_exposed (CTag l W (CVconstr c vs)).

Hint Constructors to_exposed : core.

(* Exposed Result *)
Inductive to_exposed_cres : cres -> Prop :=
| ToExp_OOT :
  to_exposed_cres COOT

| Exp_Res :
  forall wv,
    to_exposed wv ->
    to_exposed_cres (CRes wv).

Hint Constructors to_exposed_cres : core.

(* Well-formed Value and Environment *)
Inductive wf_cval : clval -> Prop :=
| WF_TAG :
  forall W l w v,
    W ! l = Some w ->
    (w \in Exposed -> to_exposed (CTag l W v)) ->
    wf_cval' v ->
    wf_cval (CTag l W v)

with wf_cval' : cval -> Prop :=
| WF_CVfun:
  forall f ρ xs e,
    wf_cenv ρ ->
    wf_cval' (CVfun f ρ xs e)

| WF_CVconstr_nil :
  forall c,
    wf_cval' (CVconstr c [])

| WF_CVconstr :
  forall c v vs,
    wf_cval v ->
    wf_cval' (CVconstr c vs) ->
    wf_cval' (CVconstr c (v :: vs))

with wf_cenv : cenv -> Prop :=
| WF_cenv :
  forall ρ,
    (forall x v, ρ ! x = Some v -> wf_cval v) ->
    wf_cenv ρ.

Hint Constructors wf_cval : core.
Hint Constructors wf_cval' : core.
Hint Constructors wf_cenv : core.

Scheme wf_cval_mut := Induction for wf_cval Sort Prop
    with wf_cval'_mut := Induction for wf_cval' Sort Prop
                        with wf_cenv_mut := Induction for wf_cenv Sort Prop.

(* Well-formed Result *)
Inductive wf_cres : cres -> Prop :=
| WF_COOT :
  wf_cres COOT

| WF_CRes :
  forall v,
    wf_cval v ->
    wf_cres (CRes v).

Hint Constructors wf_cres : core.

(* Checking Semantics *)
(* `W` is a valid analysis result with respect to the checking big-step semantics *)
Inductive cbstep (W : web_map) (ex : bool) (ρ : cenv) : exp -> fuel -> cres -> Prop :=
| Cbstep_ret :
  forall {x v},
    M.get x ρ = Some v ->
    cbstep W ex ρ (Eret x) 0 (CRes v)

| Cbstep_fun :
  forall {f l w xs e k c r},
    W ! l = Some w ->
    cbstep_fuel W ex (M.set f (CTag l W (CVfun f ρ xs e)) ρ) k c r ->
    cbstep W ex ρ (Efun f l xs e k) c r

| Cbstep_app :
  forall {W' f f' l l' w xs ρ' xs' e vs ρ'' c r},
    M.get f ρ = Some (CTag l' W' (CVfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (CTag l' W' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    W ! l = Some w -> (* W controls caller *)
    W' ! l' = Some w -> (* W' controls callee *)
    (w \in Exposed -> Forall to_exposed vs /\ to_exposed_cres r) -> (* Doesn't matter which W as long as `vs` and `r` are mapped to exposed web ids. *)
    cbstep_fuel W' (exposedb w) ρ'' e c r ->
    cbstep W ex ρ (Eapp f l xs) c r

| Cbstep_letapp_Res :
  forall {W' x f f' l l' w xs k ρ' xs' e vs ρ'' c c' v r},
    M.get f ρ = Some (CTag l' W' (CVfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (CTag l' W' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    W ! l = Some w ->
    W' ! l' = Some w ->
    cbstep_fuel W' (exposedb w) ρ'' e c (CRes v) ->
    cbstep_fuel W ex (M.set x v ρ) k c' r ->
    (w \in Exposed -> Forall to_exposed vs /\ to_exposed v) ->
    cbstep W ex ρ (Eletapp x f l xs k) (c + c') r

| Cbstep_letapp_OOT :
  forall {W' x f f' l l' w xs k ρ' xs' e vs ρ'' c},
    M.get f ρ = Some (CTag l' W' (CVfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (CTag l' W' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    W ! l = Some w ->
    W' ! l' = Some w ->
    cbstep_fuel W' (exposedb w) ρ'' e c COOT ->
    (w \in Exposed -> Forall to_exposed vs) ->
    cbstep W ex ρ (Eletapp x f l xs k) c COOT

| Cbstep_constr :
  forall {x l w t xs e r vs c},
    get_list xs ρ = Some vs ->
    W ! l = Some w ->
    (w \in Exposed -> Forall to_exposed vs) ->
    cbstep_fuel W ex (M.set x (CTag l W (CVconstr t vs)) ρ) e c r ->
    cbstep W ex ρ (Econstr x l t xs e) c r

| Cbstep_proj :
  forall {W' x l l' w t i y e c r v vs},
    M.get y ρ = Some (CTag l' W' (CVconstr t vs)) ->
    nth_error vs i = Some v ->
    W ! l = Some w ->
    W' ! l' = Some w ->
    cbstep_fuel W ex (M.set x v ρ) e c r ->
    cbstep W ex ρ (Eproj x l i y e) c r

| Cbstep_case :
  forall {W' x l l' w cl t e r c vs},
    M.get x ρ = Some (CTag l' W' (CVconstr t vs)) ->
    find_tag cl t e ->
    W ! l = Some w ->
    W' ! l' = Some w ->
    cbstep_fuel W ex ρ e c r ->
    cbstep W ex ρ (Ecase x l cl) c r

with cbstep_fuel (W : web_map) (ex : bool) (ρ : cenv) : exp -> fuel -> cres -> Prop :=
| CbstepF_OOT :
  forall {e},
    cbstep_fuel W ex ρ e 0 COOT

| CbstepF_Step :
  forall {e c r},
    cbstep W ex ρ e c r ->
    (if ex then to_exposed_cres r else True) ->
    cbstep_fuel W ex ρ e (S c) r.

Hint Constructors cbstep : core.
Hint Constructors cbstep_fuel : core.

Scheme cbstep_ind' := Minimality for cbstep Sort Prop
    with cbstep_fuel_ind' := Minimality for cbstep_fuel Sort Prop.

Lemma cbstep_deterministic_aux v v' {W ex ρ e c c' r r'}:
  cbstep W ex ρ e c r ->
  cbstep W ex ρ e c' r' ->
  r = CRes v ->
  r' = CRes v' ->
  (v = v' /\ c = c').
Proof.
  intros H.
  generalize dependent v'.
  generalize dependent r'.
  generalize dependent c'.
  generalize dependent v.
  induction H using cbstep_ind' with (P := fun W ex ρ e c r =>
                                             forall v c' r' v',
                                               cbstep W ex ρ e c' r' ->
                                               r = CRes v -> r' = CRes v' ->
                                               v = v' /\ c = c')
                                     (P0 := fun W ex ρ e c r =>
                                              forall v c' r' v',
                                                cbstep_fuel W ex ρ e c' r' ->
                                                r = CRes v -> r' = CRes v' ->
                                                v = v' /\ c = c');
    intros; subst.
  - inv H0; inv H1; invc; auto.
  - inv H1.
    edestruct IHcbstep; eauto.
  - inv H6; invc.
    edestruct IHcbstep; eauto.
  - inv H7; invc.
    edestruct IHcbstep; eauto.
    subst.
    edestruct IHcbstep0; eauto.
  - inv H7.
  - inv H3; invc.
    edestruct IHcbstep; eauto.
  - inv H4; invc.
    edestruct IHcbstep; eauto.
  - inv H4; invc.
    destruct (find_tag_deterministic H0 H9); subst.
    edestruct IHcbstep; eauto.
  - inv H0.
  - destruct ex; inv H1;
      edestruct IHcbstep; eauto.
Qed.

Lemma cbstep_fuel_deterministic_aux v v' {W ex ρ e c c' r r'}:
  cbstep_fuel W ex ρ e c r ->
  cbstep_fuel W ex ρ e c' r' ->
  r = CRes v ->
  r' = CRes v' ->
  (v = v' /\ c = c').
Proof.
  intros.
  inv H; inv H0; try discriminate.
  edestruct (cbstep_deterministic_aux v v' H3 H); eauto.
Qed.

Theorem cbstep_deterministic v v' {W ex ρ e c c'}:
  cbstep W ex ρ e c (CRes v) ->
  cbstep W ex ρ e c' (CRes v') ->
  (v = v' /\ c = c').
Proof. srun eauto using cbstep_deterministic_aux. Qed.

Theorem cbstep_fuel_deterministic v v' {W ex ρ e c c'}:
  cbstep_fuel W ex ρ e c (CRes v) ->
  cbstep_fuel W ex ρ e c' (CRes v') ->
  (v = v' /\ c = c').
Proof. srun eauto using cbstep_fuel_deterministic_aux. Qed.

Lemma cbstep_lt_Res_not_OOT_aux W ex ρ e c r v :
  cbstep W ex ρ e c r ->
  r = CRes v ->
  forall c0,
    c <= c0 ->
    ~ (cbstep W ex ρ e c0 COOT).
Proof.
  intros.
  generalize dependent c0.
  generalize dependent v.
  induction H using cbstep_ind' with
    (P := fun W ex ρ e c r =>
            forall v,
              r = CRes v ->
              forall c0,
                c <= c0 ->
                ~ cbstep W ex ρ e c0 COOT)
    (P0 := fun W ex ρ e c r =>
             forall v,
               r = CRes v ->
               forall c0,
                 c <= c0 ->
                 ~ cbstep_fuel W ex ρ e c0 COOT);
    intros; intro Hc.
  - (* Cbstep_ret: 1 premise (M.get), equality = H0 *)
    inv H0. inv Hc.
  - (* Cbstep_fun: 2 premises (W!l, cbstep_fuel+IH), equality = H1 *)
    inv H1. inv Hc.
    eapply IHcbstep; eauto.
  - (* Cbstep_app: 7 premises (M.get,get_list,set_lists,W!l,W'!l',Exposed,cbstep_fuel+IH), equality = H6 *)
    inv H6. inv Hc; invc.
    eapply IHcbstep; eauto.
  - (* Cbstep_letapp_Res: 8 premises (...,cbstep_fuel+IH,cbstep_fuel+IH0,Exposed), equality = H7 *)
    inv H7.
    inv Hc; invc.
    2 : { eapply IHcbstep with (c0 := c0); eauto; lia. }
    assert (Hcv : v = v1 /\ c = c1).
    { eapply cbstep_fuel_deterministic; eauto. }
    inv Hcv.
    eapply IHcbstep0 with (c0 := c'0); eauto; lia.
  - (* Cbstep_letapp_OOT: r = COOT, equality = H6 → contradiction *)
    inv H6.
  - (* Cbstep_constr: 4 premises (get_list,W!l,Exposed,cbstep_fuel+IH), equality = H3 *)
    inv H3. inv Hc; invc.
    eapply IHcbstep; eauto.
  - (* Cbstep_proj: 5 premises (M.get,nth_error,W!l,W'!l',cbstep_fuel+IH), equality = H4 *)
    inv H4. inv Hc; invc.
    eapply IHcbstep; eauto.
  - (* Cbstep_case: 5 premises (M.get,find_tag,W!l,W'!l',cbstep_fuel+IH), equality = H4 *)
    inv H4. inv Hc; invc.
    assert (He : e = e0). { eapply find_tag_deterministic; eauto. }
    inv He.
    eapply IHcbstep; eauto.
  - (* CbstepF_OOT: 0 premises, r = COOT, equality = H → contradiction *)
    inv H.
  - (* CbstepF_Step: 2 premises (cbstep+IH, exposed), equality = H1, ineq = H2 *)
    inv H1. inv Hc. inv H2.
    eapply IHcbstep with (c0 := c1); eauto; lia.
Qed.

Lemma cbstep_lt_Res_not_OOT W ex ρ e c v :
  cbstep W ex ρ e c (CRes v) ->
  forall c0,
    c <= c0 ->
    ~ (cbstep W ex ρ e c0 COOT).
Proof. eauto using cbstep_lt_Res_not_OOT_aux. Qed.

Lemma cbstep_fuel_lt_Res_not_OOT W ex ρ e c v :
  cbstep_fuel W ex ρ e c (CRes v) ->
  forall c0,
    c <= c0 ->
    ~ (cbstep_fuel W ex ρ e c0 COOT).
Proof.
  intros.
  inv H.
  intro Hc.
  inv Hc.
  inv H0.
  eapply cbstep_lt_Res_not_OOT with (c0 := c); eauto; lia.
Qed.

Lemma cbstep_fuel_exposed_inv W ρ e k r :
  cbstep_fuel W true ρ e k r ->
  to_exposed_cres r.
Proof.
  intro H.
  induction H; eauto.
Qed.

(* Lemmas about [wf_val] and [wf_env] *)
Lemma wf_cenv_get ρ :
  wf_cenv ρ ->
  forall x v,
    ρ ! x = Some v ->
    wf_cval v.
Proof. fcrush. Qed.

Lemma wf_cenv_get_list ρ :
  wf_cenv ρ ->
  forall xs vs,
    get_list xs ρ = Some vs ->
    Forall wf_cval vs.
Proof.
  intros Henv xs.
  induction xs; simpl; intros; fcrush.
Qed.

Lemma wf_cenv_set ρ x v :
  wf_cenv ρ ->
  wf_cval v ->
  wf_cenv (M.set x v ρ).
Proof.
  intros.
  inv H.
  constructor; intros.
  destruct (M.elt_eq x x0); subst.
  - rewrite M.gss in *; fcrush.
  - rewrite M.gso in *; fcrush.
Qed.

Lemma wf_cenv_set_lists :
  forall ρ,
    wf_cenv ρ ->
    forall vs xs ρ',
      Forall wf_cval vs ->
      set_lists xs vs ρ = Some ρ' ->
      wf_cenv ρ'.
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
    + rewrite M.gss in *; fcrush.
    + rewrite M.gso in *; fcrush.
Qed.

Lemma wf_cval_CVconstr W c l w vs :
  Forall wf_cval vs ->
  W ! l = Some w ->
  (w \in Exposed -> Forall to_exposed vs) ->
  wf_cval (CTag l W (CVconstr c vs)).
Proof.
  intros H.
  induction H; simpl; auto; intros.
  fcrush.

  assert (Hwf : wf_cval (CTag l W (CVconstr c l0))).
  {
    eapply IHForall; eauto.
    fcrush.
  }

  inv Hwf; invc; eauto.
Qed.

Lemma wf_cval_CVconstr_inv {W w l c vs} :
  wf_cval (CTag l W (CVconstr c vs)) ->
  W ! l = Some w ->
  (Forall wf_cval vs /\ (w \in Exposed -> Forall to_exposed vs)).
Proof.
  intros.
  remember (CTag l W (CVconstr c vs)) as v.
  revert c vs Heqv.
  induction H using wf_cval_mut with (P0 := fun v wf =>
                                              forall c vs,
                                                v = (CVconstr c vs) ->
                                                Forall wf_cval vs)
                                     (P1 := fun ρ wf => True);
    intros; eauto.
  - inv Heqv; invc.
    split; eauto; intros.
    fcrush.
  - fcrush.
  - fcrush.
  - fcrush.
Qed.

Lemma cbstep_wf_res W ex ρ e c r :
  wf_cenv ρ ->
  cbstep W ex ρ e c r ->
  wf_cres r.
Proof.
  intros Hw H.
  induction H using cbstep_ind' with
    (P0 := fun W ex ρ e c r => wf_cenv ρ -> wf_cres r);
    intros; auto.

  - (* Cbstep_ret *)
    constructor.
    eapply wf_cenv_get; eauto.

  - (* Cbstep_fun *)
    apply IHcbstep.
    eapply wf_cenv_set; eauto.

  - (* Cbstep_app *)
    assert (Hwfclo : wf_cval (CTag l' W' (CVfun f' ρ' xs' e))).
    { eapply wf_cenv_get; eauto. }
    assert (Hwfρ' : wf_cenv ρ').
    { inv Hwfclo.
      match goal with [Hv : wf_cval' _ |- _] => inv Hv end; auto. }
    assert (Hwfvs : Forall wf_cval vs).
    { eapply wf_cenv_get_list. apply Hw. eassumption. }
    assert (Hwfρf : wf_cenv (M.set f' (CTag l' W' (CVfun f' ρ' xs' e)) ρ')).
    { eapply wf_cenv_set; eauto. }
    apply IHcbstep.
    eapply wf_cenv_set_lists
      with (ρ := M.set f' (CTag l' W' (CVfun f' ρ' xs' e)) ρ'); eauto.

  - (* Cbstep_letapp_Res *)
    assert (Hwfclo : wf_cval (CTag l' W' (CVfun f' ρ' xs' e))).
    { eapply wf_cenv_get; eauto. }
    assert (Hwfρ' : wf_cenv ρ').
    { inv Hwfclo.
      match goal with [Hv : wf_cval' _ |- _] => inv Hv end; auto. }
    assert (Hwfvs : Forall wf_cval vs).
    { eapply wf_cenv_get_list. apply Hw. eassumption. }
    assert (Hwfρf : wf_cenv (M.set f' (CTag l' W' (CVfun f' ρ' xs' e)) ρ')).
    { eapply wf_cenv_set; eauto. }
    assert (Hwfρ'' : wf_cenv ρ'').
    { eapply wf_cenv_set_lists
        with (ρ := M.set f' (CTag l' W' (CVfun f' ρ' xs' e)) ρ'); eauto. }
    assert (Hwfres : wf_cres (CRes v)) by (apply IHcbstep; auto).
    inv Hwfres.
    apply IHcbstep0.
    eapply wf_cenv_set; eauto.

  - (* Cbstep_constr *)
    apply IHcbstep.
    eapply wf_cenv_set; eauto.
    eapply wf_cval_CVconstr; eauto.
    eapply wf_cenv_get_list; eauto.

  - (* Cbstep_proj *)
    apply IHcbstep.
    eapply wf_cenv_set; eauto.
    assert (Hwfvc : wf_cval (CTag l' W' (CVconstr t vs))).
    { eapply wf_cenv_get; eauto. }
    destruct (wf_cval_CVconstr_inv Hwfvc H2) as [Hwfvs _].
    eapply Forall_nth_error; eauto.
Qed.

Lemma cbstep_fuel_wf_res W ex ρ e c r :
  wf_cenv ρ ->
  cbstep_fuel W ex ρ e c r ->
  wf_cres r.
Proof.
  intros.
  inv H0; eauto using cbstep_wf_res.
Qed.

(* Sub Value and Environment for the Checking Semantics *)
(* Analogous to subval/subenv in ANF.v *)
Inductive csubval : clval -> clval -> Prop :=
| CSub_clval :
  forall l W v1 v2,
    csubval' v1 v2 ->
    csubval (CTag l W v1) (CTag l W v2)

with csubval' : cval -> cval -> Prop :=
| CSub_fun :
  forall Γ f xs e ρ1 ρ2,
    (occurs_free e) \subset (FromList xs :|: (f |: Γ)) ->
    csubenv Γ ρ1 ρ2 ->
    csubval' (CVfun f ρ1 xs e) (CVfun f ρ2 xs e)

| CSub_constr_nil :
  forall c,
    csubval' (CVconstr c []) (CVconstr c [])

| CSub_constr_cons :
  forall c v1 v2 vs1 vs2,
    csubval v1 v2 ->
    csubval' (CVconstr c vs1) (CVconstr c vs2) ->
    csubval' (CVconstr c (v1 :: vs1)) (CVconstr c (v2 :: vs2))

with csubenv : vars -> cenv -> cenv -> Prop :=
| CSub_env :
  forall Γ ρ1 ρ2,
    (forall x,
        (x \in Γ) ->
        forall v1,
          M.get x ρ1 = Some v1 ->
          exists v2,
            M.get x ρ2 = Some v2 /\
            csubval v1 v2) ->
    csubenv Γ ρ1 ρ2.

Hint Constructors csubval : core.
Hint Constructors csubval' : core.
Hint Constructors csubenv : core.

Scheme csubval_mut := Induction for csubval Sort Prop
  with csubval'_mut := Induction for csubval' Sort Prop
  with csubenv_mut := Induction for csubenv Sort Prop.

Inductive csubres : cres -> cres -> Prop :=
| CSub_COOT :
  csubres COOT COOT

| CSub_CRes :
  forall {v1 v2},
    csubval v1 v2 ->
    csubres (CRes v1) (CRes v2).

Hint Constructors csubres : core.

Lemma csubenv_set {x v1 v2 Γ ρ1 ρ2}:
  csubval v1 v2 ->
  csubenv Γ ρ1 ρ2 ->
  csubenv (x |: Γ) (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  intros Hv Hρ.
  constructor; intros y Hy w1 Hgw.
  destruct (M.elt_eq x y); subst.
  - rewrite M.gss in *. inv Hgw.
    exists v2. eauto.
  - rewrite M.gso in * by auto.
    inv Hρ.
    assert (Hy' : y \in Γ).
    { inv Hy; auto. inv H0; contradiction. }
    edestruct (H _ Hy' _ Hgw) as [w2 [Hgw2 Hwv]].
    exists w2. fcrush.
Qed.

Lemma csubenv_get {Γ ρ1 ρ2} :
  csubenv Γ ρ1 ρ2 ->
  forall x,
    (x \in Γ) ->
    forall {v1},
      ρ1 ! x = Some v1 ->
      exists v2,
        ρ2 ! x = Some v2 /\
        csubval v1 v2.
Proof. intros; inv H; eauto. Qed.

Lemma csubenv_subset Γ1 {Γ2 ρ1 ρ2} :
  csubenv Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  csubenv Γ2 ρ1 ρ2.
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  constructor; intros.
  eapply csubenv_get; eauto.
Qed.

Lemma csubenv_set_lists Γ ρ1 ρ2:
  csubenv Γ ρ1 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 csubval vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    csubenv (FromList xs :|: Γ) ρ3 ρ4.
Proof.
  intros Hs xs.
  induction xs; simpl; intros;
    destruct vs1; destruct vs2; try discriminate.
  - inv H0; inv H1.
    constructor; intros.
    eapply csubenv_get; eauto.
    inv H0; auto.
    inv H2.
  - destruct (set_lists xs vs1 ρ1) eqn:Heq1;
      destruct (set_lists xs vs2 ρ2) eqn:Heq2;
      try discriminate.
    inv H; inv H0; inv H1.
    eapply (csubenv_subset (a |: (FromList xs :|: Γ))).
    eapply csubenv_set; eauto.
    rewrite FromList_cons; eauto.
    rewrite <- Union_assoc.
    eapply Included_refl.
Qed.

Lemma csubenv_get_lists {Γ ρ1 ρ2}:
  csubenv Γ ρ1 ρ2 ->
  forall xs,
    (FromList xs \subset Γ) ->
    forall {vs1},
      get_list xs ρ1 = Some vs1 ->
      exists vs2,
        get_list xs ρ2 = Some vs2 /\
        Forall2 csubval vs1 vs2.
Proof.
  intros Hs xs.
  induction xs; simpl; intros.
  - inv H0; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq2; try discriminate.
    inv H0.
    rewrite FromList_cons in H.
    edestruct (csubenv_get Hs a) as [v2 [Heqv2 Hv2]]; eauto.
    edestruct IHxs as [vs2 [Heqvs2 Hvs]]; eauto.
    apply Union_Included_r in H; auto.
    rewrite Heqv2.
    rewrite Heqvs2.
    eexists; split; eauto.
Qed.

Lemma csubval_to_exposed v1 v2 :
  csubval v1 v2 ->
  to_exposed v1 ->
  to_exposed v2.
Proof.
  intros H.
  induction H using csubval_mut with
    (P0 := fun v1' v2' sub =>
             match v1', v2' with
             | CVfun _ _ _ _, CVfun _ _ _ _ => True
             | CVconstr _ vs1, CVconstr _ vs2 =>
                 Forall to_exposed vs1 -> Forall to_exposed vs2
             | _, _ => False
             end)
    (P1 := fun _ _ _ _ => True);
    intros; auto.
  inv c.
  - inv H; econstructor; eauto.
  - inv H; econstructor; eauto.
  - inv H; econstructor; eauto.
  - inv H0; constructor; auto.
Qed.

Lemma csubval_to_exposed_Forall vs1 vs2 :
  Forall2 csubval vs1 vs2 ->
  Forall to_exposed vs1 ->
  Forall to_exposed vs2.
Proof.
  intros H.
  induction H; simpl; intros; auto.
  inv H1; constructor; auto.
  eapply csubval_to_exposed; eauto.
Qed.

Lemma csubres_to_exposed_cres r1 r2 :
  csubres r1 r2 ->
  to_exposed_cres r1 ->
  to_exposed_cres r2.
Proof.
  intros.
  inv H; auto.
  inv H0; constructor.
  eapply csubval_to_exposed; eauto.
Qed.

Lemma csubval_CVconstr l W c vs1 vs2 :
  Forall2 csubval vs1 vs2 ->
  csubval (CTag l W (CVconstr c vs1)) (CTag l W (CVconstr c vs2)).
Proof.
  intros H.
  induction H; simpl; auto.
  inv IHForall2; auto.
Qed.

Lemma csubval_CVconstr_inv_l {l W c vs1 v2} :
  csubval (CTag l W (CVconstr c vs1)) v2 ->
  exists vs2,
    v2 = (CTag l W (CVconstr c vs2)) /\
    Forall2 csubval vs1 vs2.
Proof.
  intros.
  remember (CTag l W (CVconstr c vs1)) as v1.
  generalize dependent vs1.
  induction H using csubval_mut with
    (P0 := fun v1' v2' sub =>
             match v1', v2' with
             | CVfun _ _ _ _, CVfun _ _ _ _ => True
             | CVconstr _ vs1, CVconstr _ vs2 => Forall2 csubval vs1 vs2
             | _, _ => False
             end)
    (P1 := fun _ _ _ _ => True);
    intros; auto.
  inv Heqv1.
  destruct v2; try contradiction.
  inv c0; eauto.
Qed.

Lemma csubval_refl v :
  wf_cval v ->
  csubval v v.
Proof.
  intros H.
  induction H using wf_cval_mut with
    (P0 := fun v wf =>
             match v with
             | CVfun f ρ xs e => csubenv (occurs_free e) ρ ρ
             | CVconstr c vs => Forall2 csubval vs vs
             end)
    (P1 := fun ρ wf => forall Γ, csubenv Γ ρ ρ);
    eauto.
  - destruct v.
    + constructor; auto.
      eapply (CSub_fun (occurs_free e0)); eauto.
      unfold Ensembles.Included, Ensembles.In, FromList.
      intros.
      repeat apply Union_intror; auto.
    + eapply csubval_CVconstr; eauto.
Qed.

Lemma csubval_refl_Forall vs :
  Forall wf_cval vs ->
  Forall2 csubval vs vs.
Proof.
  intros H.
  induction H; constructor; auto.
  apply csubval_refl; auto.
Qed.

Lemma csubres_refl r :
  wf_cres r ->
  csubres r r.
Proof.
  intros H. inv H; constructor.
  apply csubval_refl; auto.
Qed.

(* Semantic Weakening for the Checking Semantics *)
Lemma cbstep_subenv {W ex Γ ρ1 ρ2 e c r1}:
  wf_cenv ρ2 ->
  (occurs_free e) \subset Γ ->
  csubenv Γ ρ1 ρ2 ->
  cbstep W ex ρ1 e c r1 ->
  (exists r2, cbstep W ex ρ2 e c r2 /\ csubres r1 r2 /\ wf_cres r2).
Proof.
  intros Hρ2. intros.
  generalize dependent ρ2.
  generalize dependent Γ.
  induction H1 using cbstep_ind' with
    (P0 := fun W ex ρ1 e c r1 =>
             forall Γ,
               occurs_free e \subset Γ ->
               forall ρ2,
                 wf_cenv ρ2 ->
                 csubenv Γ ρ1 ρ2 ->
                 exists r2, cbstep_fuel W ex ρ2 e c r2 /\ csubres r1 r2 /\ wf_cres r2);
    intros; subst.

  - (* Cbstep_ret *)
    edestruct (csubenv_get H1 x) as [v2' [Heqv2' Hv]]; eauto.
    exists (CRes v2'); repeat split; auto.
    constructor.
    eapply wf_cenv_get; eauto.

  - (* Cbstep_fun *)
    assert (HFk : occurs_free k \subset (f |: Γ)) by (eapply free_fun_k_inv; eauto).
    assert (HFe : occurs_free e \subset FromList xs :|: (f |: Γ)) by (eapply free_fun_e_inv; eauto).
    rename W into W0.
    set (clos1 := CTag l W0 (CVfun f ρ xs e)).
    set (clos2 := CTag l W0 (CVfun f ρ2 xs e)).
    assert (Hclos : csubval clos1 clos2).
    { unfold clos1, clos2.
      constructor.
      eapply CSub_fun with (Γ := Γ); eauto. }
    assert (Hsub' : csubenv (f |: Γ) (M.set f clos1 ρ) (M.set f clos2 ρ2))
      by (eapply csubenv_set; eauto).
    destruct (IHcbstep _ HFk (M.set f clos2 ρ2)) as [r2 [Hr2 [Hs Hr]]].
    + eapply wf_cenv_set; eauto.
      unfold clos2.
      econstructor; eauto.
    + assumption.
    + exists r2; split; auto.
      econstructor; eauto.

  - (* Cbstep_app *)
    edestruct (csubenv_get H7 f) as [vf2 [Heqvf2 Hvf2]]; eauto.
    inv Hvf2.
    inv H12.
    edestruct (csubenv_get_lists H7 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_app_xs_subset.

    assert (Hlen : length xs' = length vs2).
    { erewrite <- (Forall2_length _ _ _ Hvs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto. }
    rename ρ0 into ρ4.
    destruct (set_lists_length3
                (M.set f' (CTag l' W' (CVfun f' ρ4 xs' e)) ρ4)
                _ _ Hlen) as [ρ2'' Heqρ2''].

    assert (Hwfvf : wf_cval (CTag l' W' (CVfun f' ρ4 xs' e))) by (eapply wf_cenv_get; eauto).
    assert (Hwfρ'' : wf_cenv ρ2'').
    { eapply wf_cenv_set_lists
        with (xs := xs') (vs := vs2)
             (ρ := M.set f' (CTag l' W' (CVfun f' ρ4 xs' e)) ρ4); eauto.
      - eapply wf_cenv_set; eauto.
        inv Hwfvf. inv H13; auto.
      - eapply wf_cenv_get_list; eauto. }
    assert (Hclos : csubval (CTag l' W' (CVfun f' ρ' xs' e)) (CTag l' W' (CVfun f' ρ4 xs' e))).
    { constructor. eapply CSub_fun with (Γ := Γ0); eauto. }
    assert (Hsub' : csubenv (FromList xs' :|: (f' |: Γ0)) ρ'' ρ2'').
    { eapply csubenv_set_lists; eauto.
      eapply csubenv_set; eauto. }
    edestruct (IHcbstep _ H14 ρ2'') as [r2 [Hr2 [Hs Hr]]]; eauto.

    exists r2; repeat split; auto.
    econstructor; eauto; intros.
    edestruct H4 as [Hexpvs Hexpr]; auto.
    split.
    + eapply csubval_to_exposed_Forall; eauto.
    + eapply csubres_to_exposed_cres; eauto.

  - (* Cbstep_letapp_Res *)
    edestruct (csubenv_get H8 f) as [vf2 [Heqvf2 Hvf2]]; eauto.
    inv Hvf2.
    inv H13.
    edestruct (csubenv_get_lists H8 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_letapp_xs_subset.

    assert (Hlen : length xs' = length vs2).
    { erewrite <- (Forall2_length _ _ _ Hvs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto. }
    rename ρ0 into ρ4.
    destruct (set_lists_length3
                (M.set f' (CTag l' W' (CVfun f' ρ4 xs' e)) ρ4)
                _ _ Hlen) as [ρ2'' Heqρ2''].

    assert (Hwfvf : wf_cval (CTag l' W' (CVfun f' ρ4 xs' e))) by (eapply wf_cenv_get; eauto).
    assert (Hwfρ'' : wf_cenv ρ2'').
    { eapply wf_cenv_set_lists
        with (xs := xs') (vs := vs2)
             (ρ := M.set f' (CTag l' W' (CVfun f' ρ4 xs' e)) ρ4); eauto.
      - eapply wf_cenv_set; eauto.
        inv Hwfvf. inv H14; auto.
      - eapply wf_cenv_get_list; eauto. }
    assert (Hclos : csubval (CTag l' W' (CVfun f' ρ' xs' e)) (CTag l' W' (CVfun f' ρ4 xs' e))).
    { constructor. eapply CSub_fun with (Γ := Γ0); eauto. }
    assert (Hsub' : csubenv (FromList xs' :|: (f' |: Γ0)) ρ'' ρ2'').
    { eapply csubenv_set_lists; eauto.
      eapply csubenv_set; eauto. }
    edestruct (IHcbstep _ H15 ρ2'') as [r2 [Hr2 [Hs Hr]]]; eauto.
    inv Hs.
    assert (HFk : occurs_free k \subset (x |: Γ)) by (eapply free_letapp_k_inv; eauto).
    edestruct (IHcbstep0 _ HFk (M.set x v2 ρ2)) as [r3 [Hr3 [Hs' Hr']]].
    + eapply wf_cenv_set; eauto. inv Hr; auto.
    + eapply csubenv_set; eauto.
    + exists r3; repeat split; auto.
      econstructor; eauto; intros.
      edestruct H6 as [Hexpvs Hexpv]; auto.
      split.
      * eapply csubval_to_exposed_Forall; eauto.
      * assert (Hr2_exp : csubres (CRes v) (CRes v2)) by (constructor; auto).
        eapply csubres_to_exposed_cres in Hr2_exp; auto.
        inv Hr2_exp; auto.

  - (* Cbstep_letapp_OOT *)
    edestruct (csubenv_get H7 f) as [vf2 [Heqvf2 Hvf2]]; eauto.
    inv Hvf2.
    inv H12.
    edestruct (csubenv_get_lists H7 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_letapp_xs_subset.

    assert (Hlen : length xs' = length vs2).
    { erewrite <- (Forall2_length _ _ _ Hvs2); eauto.
      rewrite <- (set_lists_length_eq _ _ _ _ H1); auto. }
    rename ρ0 into ρ4.
    destruct (set_lists_length3
                (M.set f' (CTag l' W' (CVfun f' ρ4 xs' e)) ρ4)
                _ _ Hlen) as [ρ2'' Heqρ2''].

    assert (Hwfvf : wf_cval (CTag l' W' (CVfun f' ρ4 xs' e))) by (eapply wf_cenv_get; eauto).
    assert (Hwfρ'' : wf_cenv ρ2'').
    { eapply wf_cenv_set_lists
        with (xs := xs') (vs := vs2)
             (ρ := M.set f' (CTag l' W' (CVfun f' ρ4 xs' e)) ρ4); eauto.
      - eapply wf_cenv_set; eauto.
        inv Hwfvf. inv H13; auto.
      - eapply wf_cenv_get_list; eauto. }
    assert (Hclos : csubval (CTag l' W' (CVfun f' ρ' xs' e)) (CTag l' W' (CVfun f' ρ4 xs' e))).
    { constructor. eapply CSub_fun with (Γ := Γ0); eauto. }
    assert (Hsub' : csubenv (FromList xs' :|: (f' |: Γ0)) ρ'' ρ2'').
    { eapply csubenv_set_lists; eauto.
      eapply csubenv_set; eauto. }
    edestruct (IHcbstep _ H14 ρ2'') as [r2 [Hr2 [Hs Hr]]]; eauto.
    inv Hs.
    exists COOT; repeat split; auto.
    econstructor; eauto; intros.
    eapply csubval_to_exposed_Forall; eauto.

  - (* Cbstep_constr *)
    edestruct (csubenv_get_lists H4 xs) as [vs2 [Heqvs2 Hvs2]]; eauto.
    eapply Included_trans; eauto.
    apply free_constr_xs_subset.

    assert (HFk : occurs_free e \subset (x |: Γ)) by (eapply free_constr_k_inv; eauto).
    rename W into W0.
    edestruct (IHcbstep _ HFk (M.set x (CTag l W0 (CVconstr t vs2)) ρ2))
      as [r2 [Hr2 [Hs Hr]]].
    + eapply wf_cenv_set; eauto.
      eapply wf_cval_CVconstr; eauto.
      eapply wf_cenv_get_list; eauto.
      intros. eapply csubval_to_exposed_Forall; eauto.
    + eapply csubenv_set; eauto.
      eapply csubval_CVconstr; eauto.
    + exists r2; repeat split; auto.
      econstructor; eauto; intros.
      eapply csubval_to_exposed_Forall; eauto.

  - (* Cbstep_proj *)
    edestruct (csubenv_get H5 y) as [vy2 [Heqvy2 Hvy2]]; eauto.
    edestruct (csubval_CVconstr_inv_l Hvy2) as [vs2 [Heqvs2 Hvs2]]; subst.
    edestruct (Forall2_nth_error H0 Hvs2) as [v' [Heqv' Hv]].
    assert (HFk : occurs_free e \subset (x |: Γ)) by (eapply free_proj_k_inv; eauto).
    edestruct (IHcbstep _ HFk (M.set x v' ρ2)) as [r2 [Hr2 [Hs Hr]]].
    + eapply wf_cenv_set; eauto.
      assert (Hwfvy : wf_cval (CTag l' W' (CVconstr t vs2))) by (eapply wf_cenv_get; eauto).
      destruct (wf_cval_CVconstr_inv Hwfvy H2) as [Hwfvs _].
      eapply Forall_forall; eauto.
      eapply nth_error_In; eauto.
    + eapply csubenv_set; eauto.
    + exists r2; repeat split; auto.
      econstructor; eauto.

  - (* Cbstep_case *)
    edestruct (csubenv_get H5 x) as [vx2 [Heqvx2 Hvx2]]; eauto.
    edestruct (csubval_CVconstr_inv_l Hvx2) as [vs2 [Heqvs2 Hvs2]]; subst.
    edestruct IHcbstep as [r2 [Hr2 [Hs Hr]]]; eauto.
    + eapply free_case_e_inv; eauto.

  - (* CbstepF_OOT *)
    exists COOT; repeat split; auto.

  - (* CbstepF_Step *)
    edestruct IHcbstep as [r2 [Hr2 [Hs Hr]]]; eauto.
    assert (Hex : if ex then to_exposed_cres r2 else True).
    { destruct ex; auto. eapply csubres_to_exposed_cres; eauto. }
    exists r2; repeat split; auto.
Qed.

Lemma cbstep_fuel_subenv {W ex Γ ρ1 ρ2 e c r1}:
  wf_cenv ρ2 ->
  (occurs_free e) \subset Γ ->
  csubenv Γ ρ1 ρ2 ->
  cbstep_fuel W ex ρ1 e c r1 ->
  (exists r2, cbstep_fuel W ex ρ2 e c r2 /\ csubres r1 r2 /\ wf_cres r2).
Proof.
  intros.
  inv H2.
  - exists COOT; repeat split; auto.
  - destruct (cbstep_subenv H H0 H1 H3) as [r2 [Hr2 [Hs Hr]]].
    assert (Hex : if ex then to_exposed_cres r2 else True).
    { destruct ex; auto. eapply csubres_to_exposed_cres; eauto. }
    exists r2; repeat split; auto.
Qed.

(* Value Refinement *)
Inductive refine_val : wval -> clval -> Prop :=
| Refine_wval :
  forall l v v' W,
    refine_val' v v' ->
    refine_val (Tag l v) (CTag l W v')

with refine_val' : val -> cval -> Prop :=
| Refine_fun :
  forall Γ f ρ ρ' xs e,
    (occurs_free e) \subset (FromList xs :|: (f |: Γ)) ->
    refine_env Γ ρ ρ' ->
    refine_val' (Vfun f ρ xs e) (CVfun f ρ' xs e)

| Refine_constr_nil :
  forall c,
    refine_val' (Vconstr c []) (CVconstr c [])

| Refine_constr :
  forall c v vs v' vs',
    refine_val v v' ->
    refine_val' (Vconstr c vs) (CVconstr c vs') ->
    refine_val' (Vconstr c (v :: vs)) (CVconstr c (v' :: vs'))

with refine_env : vars -> env -> cenv -> Prop :=
| Refine_env :
  forall Γ ρ ρ',
    (forall x,
        (x \in Γ) ->
        exists v1 v2,
          M.get x ρ = Some v1 /\
          M.get x ρ' = Some v2 /\
          refine_val v1 v2) ->
    refine_env Γ ρ ρ'.

Hint Constructors refine_val : core.
Hint Constructors refine_val' : core.
Hint Constructors refine_env : core.

Scheme refine_val_mut := Induction for refine_val Sort Prop
with refine_val'_mut := Induction for refine_val' Sort Prop
with refine_env_mut := Induction for refine_env Sort Prop.

Inductive refine_res : res -> cres -> Prop :=
| Refine_COOT :
  refine_res OOT COOT

| Refine_CRes :
  forall v v',
    refine_val v v' ->
    refine_res (Res v) (CRes v').

Hint Constructors refine_res : core.

(* Helper lemmas on refine_env / refine_val *)
Lemma refine_env_get x v {Γ ρ1 ρ2} :
  refine_env Γ ρ1 ρ2 ->
  x \in Γ ->
  ρ1 ! x = Some v ->
  exists v', ρ2 ! x = Some v' /\ refine_val v v'.
Proof.
  intros Henv Hget Hr1. inv Henv.
  edestruct H as [v1 [v2 [Heqv1 [Heqv2 Href]]]]; eauto; invc; eauto.
Qed.

Lemma refine_env_subset Γ1 {Γ2 ρ1 ρ2} :
  refine_env Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  refine_env Γ2 ρ1 ρ2.
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  constructor; intros.
  inv H; fcrush.
Qed.

Lemma refine_env_get_list xs vs {Γ ρ1 ρ2} :
  refine_env Γ ρ1 ρ2 ->
  FromList xs \subset Γ ->
  get_list xs ρ1 = Some vs ->
  exists vs', get_list xs ρ2 = Some vs' /\ Forall2 refine_val vs vs'.
Proof.
  intros Henv. revert vs.
  induction xs as [|x xs IH]; intros vs HS Hget; simpl in *.
  - inv Hget. exists []; split; auto.
  - destruct (ρ1 ! x) as [v|] eqn:Hx; [|discriminate].
    destruct (get_list xs ρ1) as [vs0|] eqn:Hxs; [|discriminate].
    inv Hget.
    edestruct (refine_env_get x v Henv) as [v' [Hv' Hrv]]; eauto.
    + unfold Ensembles.Included, Ensembles.In in *.
      fcrush.
    + edestruct (IH vs0) as [vs' [Hvs' Hrvs]]; eauto.
      unfold Ensembles.Included, Ensembles.In in *.
      fcrush.
      rewrite Hv', Hvs'. exists (v' :: vs'); split; auto.
Qed.

Lemma refine_env_set x v v' {Γ ρ1 ρ2} :
  refine_env Γ ρ1 ρ2 ->
  refine_val v v' ->
  refine_env (x |: Γ) (M.set x v ρ1) (M.set x v' ρ2).
Proof.
  intros Henv Hrv. constructor. intros y Hy.
  destruct (M.elt_eq x y) as [<-|Hne].
  - repeat (rewrite M.gss in *); invc.
    fcrush.
  - repeat (rewrite M.gso in * by auto).
    inv Henv.
    edestruct H as [w' [Hw' Hrw]]; eauto.
    unfold Ensembles.Included, Ensembles.In in *.
    fcrush.
Qed.

Lemma refine_env_set_lists xs vs vs' {Γ ρ1 ρ2 ρ1' ρ2'} :
  Forall2 refine_val vs vs' ->
  refine_env Γ ρ1 ρ2 ->
  set_lists xs vs ρ1 = Some ρ1' ->
  set_lists xs vs' ρ2 = Some ρ2' ->
  refine_env (FromList xs :|: Γ) ρ1' ρ2'.
Proof.
  intros Hf2. revert xs ρ1 ρ2 ρ1' ρ2'.
  induction Hf2 as [|v v' vs_rest vs_rest' Hrv _ IH];
    intros xs ρ1 ρ2 ρ1' ρ2' Henv Hset1 Hset2.
  - destruct xs as [|x xs_rest]; simpl in *.
    + inv Hset1; inv Hset2; auto.
      eapply refine_env_subset; eauto.
      rewrite FromList_nil.
      rewrite Union_Empty_set_neut_l.
      fcrush.
    + discriminate.
  - destruct xs as [|x xs_rest]; simpl in *; [discriminate|].
    destruct (set_lists xs_rest vs_rest ρ1) as [ρ3|] eqn:H3; [|discriminate].
    destruct (set_lists xs_rest vs_rest' ρ2) as [ρ4|] eqn:H4; [|discriminate].
    inv Hset1; inv Hset2.
    eapply (refine_env_subset (x |: (FromList xs_rest :|: Γ))).
    + eapply refine_env_set; eauto.
    + rewrite FromList_cons.
      rewrite <- Union_assoc.
      apply Included_refl.
Qed.

Lemma refine_val_Vfun_inv {l f ρ xs e v''} :
  refine_val (Tag l (Vfun f ρ xs e)) v'' ->
  exists W ρ' Γ,
    v'' = CTag l W (CVfun f ρ' xs e) /\
    occurs_free e \subset (FromList xs :|: (f |: Γ)) /\
    refine_env Γ ρ ρ'.
Proof.
  intros H.
  inv H.
  match goal with [Hv : refine_val' _ _ |- _] => inv Hv end.
  do 3 eexists. eauto.
Qed.

Lemma refine_val'_Vconstr_inv {t vs v''} :
  refine_val' (Vconstr t vs) v'' ->
  exists vs', v'' = CVconstr t vs' /\ Forall2 refine_val vs vs'.
Proof.
  intros H. remember (Vconstr t vs) as v0 eqn:Heq.
  revert t vs Heq.
  induction H; intros t0 vs0 Heq; inv Heq.
  - exists []; split; auto.
  - destruct (IHrefine_val' t0 vs eq_refl) as [vs1 [Heq Hr]].
    inv Heq. exists (v' :: vs1); split; auto.
Qed.

Lemma refine_val_Vconstr_inv {l t vs v''} :
  refine_val (Tag l (Vconstr t vs)) v'' ->
  exists W vs', v'' = CTag l W (CVconstr t vs') /\ Forall2 refine_val vs vs'.
Proof.
  intros H. inv H. apply refine_val'_Vconstr_inv in H3 as [vs' [-> Hr]]; eauto.
Qed.

Lemma refine_val'_Vconstr {t vs vs'} :
  Forall2 refine_val vs vs' ->
  refine_val' (Vconstr t vs) (CVconstr t vs').
Proof. intros Hr. induction Hr; auto. Qed.

Lemma refine_val_Vconstr {l W t vs vs'} :
  Forall2 refine_val vs vs' ->
  refine_val (Tag l (Vconstr t vs)) (CTag l W (CVconstr t vs')).
Proof. intros Hr. constructor. apply refine_val'_Vconstr; auto. Qed.

(* [refine_val] commutes with [subval] *)
Lemma refine_val_csubval v0 v v' :
  refine_val v0 v ->
  csubval v v' ->
  refine_val v0 v'
with refine_val'_csubval' v0 v v' :
  refine_val' v0 v ->
  csubval' v v' ->
  refine_val' v0 v'
with refine_env_csubenv Γ Γ' ρa ρc ρc' :
  refine_env Γ ρa ρc ->
  csubenv Γ' ρc ρc' ->
  refine_env (Γ :&: Γ') ρa ρc'.
Proof.
  - (* refine_val_csubval *)
    intros Href Hsub.
    inv Href. inv Hsub. constructor.
    eapply refine_val'_csubval'; eauto.

  - (* refine_val'_csubval' *)
    intros Href Hsub.
    inv Href.
    + (* Refine_fun *)
      inversion Hsub as [Γb fb xsb eb ρcb1 ρcb2 HFVb Hsubenv | |]; subst.
      eapply Refine_fun with (Γ := Γ :&: Γb).
      * (* FV inclusion *)
        unfold Ensembles.Included, Ensembles.In in *.
        intros z Hz.
        assert (Hza := H _ Hz).
        assert (Hzb := HFVb _ Hz).
        inv Hza; [left; auto|].
        inv Hzb; [left; auto|].
        rename H1 into Hzfa. rename H2 into Hzfb.
        right.
        inv Hzfa; [left; auto|].
        inv Hzfb; [left; auto|].
        right. constructor; auto.
      * eapply refine_env_csubenv; eauto.
    + (* Refine_constr_nil *)
      inv Hsub. constructor.
    + (* Refine_constr (cons) *)
      inv Hsub. constructor.
      * eapply refine_val_csubval; eauto.
      * eapply refine_val'_csubval'; eauto.

  - (* refine_env_csubenv *)
    intros Href Hsub.
    constructor; intros y Hy.
    inversion Hy as [a Hy_Γ Hy_Γ' Ha]; subst.
    inv Href.
    edestruct (H y Hy_Γ) as [va [vc [Hgva [Hgvc Hrvc]]]]; eauto; invc.
    inv Hsub.
    edestruct (H0 y Hy_Γ' vc Hgvc) as [vc' [Hgvc' Hsvc]].
    exists va, vc'; repeat (split; auto).
    eapply refine_val_csubval; eauto.
Qed.

Lemma refine_res_csubres r0 r r' :
  refine_res r0 r ->
  csubres r r' ->
  refine_res r0 r'.
Proof.
  intros Hr Hs.
  inv Hr; inv Hs; auto.
  constructor. eapply refine_val_csubval; eauto.
Qed.

Lemma refine_val_subval v0 v0' v :
  refine_val v0 v ->
  subval v0 v0' ->
  refine_val v0' v
with refine_val'_subval' v0 v0' v :
  refine_val' v0 v ->
  subval' v0 v0' ->
  refine_val' v0' v
with refine_env_subenv Γ Γ' ρa ρa' ρc :
  refine_env Γ ρa ρc ->
  subenv Γ' ρa ρa' ->
  refine_env (Γ :&: Γ') ρa' ρc.
Proof.
  - (* refine_val_subval *)
    intros Hr Hs. inv Hr. inv Hs. constructor.
    eapply refine_val'_subval'; eauto.

  - (* refine_val'_subval' *)
    intros Hr Hs.
    inv Hr.
    + (* Refine_fun *)
      inversion Hs as [Γb fb xsb eb ρab1 ρab2 HFVb Hsubenv | |]; subst.
      eapply Refine_fun with (Γ := Γ :&: Γb).
      * (* FV inclusion: same reasoning as subval_trans *)
        unfold Ensembles.Included, Ensembles.In in *.
        intros z Hz.
        assert (Hz0 := H _ Hz).
        assert (Hz1 := HFVb _ Hz).
        inv Hz0; [left; auto|].
        inv Hz1; [left; auto|].
        rename H1 into Hzfa. rename H2 into Hzfb.
        right. inv Hzfa; [left; auto|]. inv Hzfb; [left; auto|].
        right. constructor; auto.
      * eapply refine_env_subenv; eauto.
    + (* Refine_constr_nil *)
      inv Hs. constructor.
    + (* Refine_constr *)
      inv Hs. constructor.
      * eapply refine_val_subval; eauto.
      * eapply refine_val'_subval'; eauto.

  - (* refine_env_subenv *)
    intros Hr Hs.
    constructor; intros y Hy.
    inversion Hy as [a Hy_Γ Hy_Γ' Ha]; subst.
    (* From refine_env Γ ρa ρc: ρa(y) = v_a, ρc(y) = v_c *)
    inv Hr.
    edestruct (H y Hy_Γ) as [va [vc [Hgva [Hgvc Hrf]]]].
    (* From subenv Γ' ρa ρa': ρa(y) = v_a → ρa'(y) = v_a' with subval *)
    inv Hs.
    edestruct (H0 y Hy_Γ' va Hgva) as [va' [Hgva' Hsubval]].
    exists va', vc. repeat split; auto.
    eapply refine_val_subval; eauto.
Qed.

Lemma refine_res_subres r0 r0' r :
  refine_res r0 r ->
  subres r0 r0' ->
  refine_res r0' r.
Proof.
  intros Hr Hs.
  inv Hr; inv Hs; auto.
  constructor.
  eapply refine_val_subval; eauto.
Qed.

(* Correlation lemmas: bstep and cbstep that both terminate on the same expression agree on fuel and value. *)
Lemma bstep_cbstep_aux v1 v2 {W ex ρ1 ρ2 e c1 r1 c2 r2} :
  bstep ρ1 e c1 r1 ->
  refine_env (occurs_free e) ρ1 ρ2 ->
  cbstep W ex ρ2 e c2 r2 ->
  r1 = Res v1 ->
  r2 = CRes v2 ->
  c1 = c2 /\ refine_val v1 v2.
Proof.
  intros Hb.
  revert v1 v2 ρ2 W ex c2 r2.
  induction Hb using bstep_ind'
    with (P := fun ρ1 e c1 r1 =>
                 forall v1 v2 ρ2 W ex c2 r2,
                   refine_env (occurs_free e) ρ1 ρ2 ->
                   cbstep W ex ρ2 e c2 r2 ->
                   r1 = Res v1 -> r2 = CRes v2 ->
                   c1 = c2 /\ refine_val v1 v2)
         (P0 := fun ρ1 e c1 r1 =>
                  forall v1 v2 ρ2 W ex c2 r2,
                    refine_env (occurs_free e) ρ1 ρ2 ->
                    cbstep_fuel W ex ρ2 e c2 r2 ->
                    r1 = Res v1 -> r2 = CRes v2 ->
                    c1 = c2 /\ refine_val v1 v2);
    intros v1 v2 ρ2 W0 ex c2 r2 Henv Hc Heq1 Heq2; subst.

  - (* BStep_ret: FV(Eret x) = {x} *)
    inv Heq1. inv Hc.
    edestruct (refine_env_get x v1 Henv (ltac:(constructor)) H) as [v' [Hv' Hrv]].
    invc; fcrush.

  - (* BStep_fun: FV(Efun f l xs e_body k) *)
    inv Hc.
    assert (Href_clos : refine_val (Tag w (Vfun f ρ xs e))
                          (CTag w W0 (CVfun f ρ2 xs e))).
    { constructor. econstructor.
      - eapply free_fun_e_inv. apply Included_refl.
      - exact Henv. }
    eapply IHHb.
    + (* FV(k) ⊆ f |: FV(Efun) via free_fun_k_subset; refine_env_set + subset *)
      eapply refine_env_subset.
      * eapply refine_env_set; eauto.
      * apply free_fun_k_subset.
    + eauto. + eauto. + eauto.

  - (* BStep_app: FV(Eapp f l xs) = {f} ∪ xs *)
    inv Hc.
    edestruct (refine_env_get f (Tag w' (Vfun f' ρ' xs' e)) Henv (ltac:(constructor)) H) as [vf [Hvf Hrf]].
    invc.
    destruct (refine_val_Vfun_inv Hrf) as [W'' [ρ_2' [Γ_c [Heq [HFVe Hre]]]]].
    inv Heq.
    edestruct (refine_env_get_list xs _ Henv
                 (ltac:(unfold Ensembles.Included, Ensembles.In; intros z Hz; constructor; auto))
                 H0) as [vs2 [Hvs2 Hrvs]].
    invc.
    assert (Href_f : refine_val (Tag w' (Vfun f' ρ' xs' e))
                       (CTag w' W'' (CVfun f' ρ_2' xs' e))).
    { constructor. econstructor; eauto. }
    assert (Hrenv : refine_env (f' |: Γ_c)
                      (M.set f' (Tag w' (Vfun f' ρ' xs' e)) ρ')
                      (M.set f' (CTag w' W'' (CVfun f' ρ_2' xs' e)) ρ_2')).
    { apply refine_env_set; eauto. }
    pose proof (refine_env_set_lists xs' vs vs2 Hrvs Hrenv H1 H8) as Hre''.
    eapply IHHb; eauto.
    eapply refine_env_subset; eauto.

  - (* BStep_letapp_Res *)
    inv Hc.
    + (* Cbstep_letapp_Res *)
      edestruct (refine_env_get f (Tag w' (Vfun f' ρ' xs' e)) Henv (ltac:(apply Free_letapp2)) H) as [vf [Hvf Hrf]].
      invc.
      destruct (refine_val_Vfun_inv Hrf) as [W'' [ρ_2' [Γ_c [Heq [HFVe Hre]]]]].
      inv Heq.
      assert (Hxs_in : FromList xs \subset occurs_free (Eletapp x f w xs k))
        by (apply free_letapp_xs_subset).
      edestruct (refine_env_get_list xs _ Henv Hxs_in H0) as [vs2 [Hvs2 Hrvs]].
      invc.
      assert (Href_f : refine_val (Tag w' (Vfun f' ρ' xs' e))
                           (CTag w' W'' (CVfun f' ρ_2' xs' e))).
        { constructor. econstructor; eauto. }
        assert (Hrenv : refine_env (f' |: Γ_c)
                          (M.set f' (Tag w' (Vfun f' ρ' xs' e)) ρ')
                          (M.set f' (CTag w' W'' (CVfun f' ρ_2' xs' e)) ρ_2')).
        { apply refine_env_set; eauto. }
        pose proof (refine_env_set_lists xs' vs vs2 Hrvs Hrenv H1 H11) as Hre''.
        edestruct (IHHb v v0) as [Hc0 Hrv0]; eauto.
        { eapply refine_env_subset; eauto. }
        edestruct (IHHb0 v1 v2) as [Hc0' Hrv2]; eauto.
        { eapply refine_env_subset.
          - apply refine_env_set; eauto.
          - apply free_letapp_k_subset. }

  - fcrush.

  - (* BStep_constr: FV(Econstr x l t xs e) *)
    inv Hc.
    edestruct (refine_env_get_list xs _ Henv
                 (ltac:(unfold Ensembles.Included, Ensembles.In; intros z Hz; constructor; auto))
                 H) as [vs2 [Hvs2 Hrvs]].
    invc.
    eapply IHHb; eauto.
    eapply refine_env_subset.
    + apply refine_env_set; [exact Henv | apply refine_val_Vconstr; auto].
    + apply free_constr_k_subset.

  - (* BStep_proj: FV(Eproj x l i y e) *)
    inv Hc.
    edestruct (refine_env_get y (Tag w' (Vconstr t vs)) Henv (ltac:(constructor)) H) as [vc [Hvc Hrc]].
    invc.
      destruct (refine_val_Vconstr_inv Hrc) as [W'' [vs' [Heq Hrvs]]].
      inv Heq.
      edestruct (Forall2_nth_error H0 Hrvs) as [v' [Hnv' Hrv']]; eauto.
      unfold clval in *; invc.
      eapply IHHb; eauto.
      eapply refine_env_subset.
      * apply refine_env_set; [exact Henv | exact Hrv'].
      * apply free_proj_k_subset.

  - (* BStep_case *)
    inv Hc.
    edestruct (refine_env_get x (Tag w' (Vconstr t vs)) Henv (ltac:(constructor)) H) as [vc [Hvc Hrc]].
    invc.
      destruct (refine_val_Vconstr_inv Hrc) as [W'' [vs' [Heq _]]].
      inv Heq.
      destruct (find_tag_deterministic H0 H6); subst.
      eapply IHHb; eauto.
      eapply refine_env_subset; [exact Henv |].
      eapply free_case_e_inv; eauto. apply Included_refl.

  - discriminate.

  - inv Hc. edestruct IHHb as [Hc0 Hrv0]; eauto.
Qed.

Lemma bstep_cbstep_refine W ex ρ1 ρ2 e c1 c2 v1 v2 :
  bstep ρ1 e c1 (Res v1) ->
  refine_env (occurs_free e) ρ1 ρ2 ->
  cbstep W ex ρ2 e c2 (CRes v2) ->
  c1 = c2 /\ refine_val v1 v2.
Proof. intros; eapply bstep_cbstep_aux; eauto. Qed.

Lemma bstep_fuel_cbstep_fuel_refine W ex ρ1 ρ2 e c1 c2 v1 v2 :
  bstep_fuel ρ1 e c1 (Res v1) ->
  refine_env (occurs_free e) ρ1 ρ2 ->
  cbstep_fuel W ex ρ2 e c2 (CRes v2) ->
  c1 = c2 /\ refine_val v1 v2.
Proof.
  intros Hb Henv Hc. inv Hb. inv Hc.
  edestruct bstep_cbstep_refine as [Heq Hrv]; eauto.
Qed.

(* Valid web_map Specification *)
(* This essentially says `has_label e` ⊆ Dom_map W *)
Inductive web_map_spec (W : web_map) (Γ : vars) : exp -> Prop :=
| Web_Map_Spec_ret :
  forall x,
    (x \in Γ) ->
    web_map_spec W Γ (Eret x)

| Web_Map_Spec_fun :
  forall {f l w xs e k},
    W ! l = Some w ->
    web_map_spec W (FromList xs :|: (f |: Γ)) e ->
    web_map_spec W (f |: Γ) k ->
    web_map_spec W Γ (Efun f l xs e k)

| Web_Map_Spec_app :
  forall {f l w xs},
    W ! l = Some w ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    web_map_spec W Γ (Eapp f l xs)

| Web_Map_Spec_letapp :
  forall {x f l w xs k},
    W ! l = Some w ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    web_map_spec W (x |: Γ) k ->
    web_map_spec W Γ (Eletapp x f l xs k)

| Web_Map_Spec_constr :
  forall {x l w t xs k},
    W ! l = Some w ->
    (FromList xs \subset Γ) ->
    web_map_spec W (x |: Γ) k ->
    web_map_spec W Γ (Econstr x l t xs k)

| Web_Map_Spec_proj :
  forall {l w x y k n},
    W ! l = Some w ->
    (y \in Γ) ->
    web_map_spec W (x |: Γ) k ->
    web_map_spec W Γ (Eproj x l n y k)

| Web_Map_Spec_case_nil :
  forall {l w x},
    W ! l = Some w ->
    (x \in Γ) ->
    web_map_spec W Γ (Ecase x l [])

| Web_Map_Spec_case_cons :
  forall {x l w e t cl},
    W ! l = Some w ->
    (x \in Γ) ->
    web_map_spec W Γ e ->
    web_map_spec W Γ (Ecase x l cl) ->
    web_map_spec W Γ (Ecase x l ((t, e) :: cl)).

Hint Constructors web_map_spec : core.

Lemma web_map_total W e :
  (has_label e \subset Dom_map W) ->
  web_map_spec W (occurs_free e) e.
Proof.
  enough (Hstrong : forall Γ,
             has_label e \subset Dom_map W ->
             occurs_free e \subset Γ ->
             web_map_spec W Γ e).
  { intros; apply Hstrong; auto; apply Included_refl. }
  induction e using exp_ind'; intros Γ Hlabel Hfree.
  - (* Eret x *)
    constructor. apply Hfree. constructor.
  - (* Eapp x w xs *)
    assert (Hl : w \in Dom_map W) by (apply Hlabel; auto).
    destruct Hl as [web Hw].
    econstructor; eauto.
    eapply free_app_xs_inv; eauto.
  - (* Efun f w xs e k *)
    assert (Hl : w \in Dom_map W) by (apply Hlabel; auto).
    destruct Hl as [web Hw].
    econstructor; eauto.
    + apply IHe1.
      * eauto using Included_trans, has_label_fun_body.
      * eapply free_fun_e_inv; eauto.
    + apply IHe2.
      * eauto using Included_trans, has_label_fun_cont.
      * eapply free_fun_k_inv; eauto.
  - (* Eletapp x f w xs k *)
    assert (Hl : w \in Dom_map W) by (apply Hlabel; auto).
    destruct Hl as [web Hw].
    econstructor; eauto.
    + eapply free_letapp_xs_inv; eauto.
    + apply IHe.
      * eauto using Included_trans, has_label_letapp_cont.
      * eapply free_letapp_k_inv; eauto.
  - (* Econstr x w c xs k *)
    assert (Hl : w \in Dom_map W) by (apply Hlabel; auto).
    destruct Hl as [web Hw].
    econstructor; eauto.
    + eapply Included_trans; eauto.
      eapply free_constr_xs_subset; eauto.
    + apply IHe.
      * eauto using Included_trans, has_label_constr_cont.
      * eapply free_constr_k_inv; eauto.
  - (* Ecase x w [] *)
    assert (Hl : w \in Dom_map W) by (apply Hlabel; auto).
    destruct Hl as [web Hw].
    econstructor; eauto.
  - (* Ecase x w ((c,e)::cl) *)
    assert (Hl : w \in Dom_map W) by (apply Hlabel; auto).
    destruct Hl as [web Hw].
    econstructor; eauto.
    + apply IHe.
      * eauto using Included_trans, has_label_case_hd.
      * eapply Included_trans; eauto.
        eapply free_case_hd_subset.
    + apply IHe0.
      * eauto using Included_trans, has_label_case_tl.
      * eapply Included_trans; eauto.
        apply free_case_tl_subset.
  - (* Eproj x w n v0 e *)
    assert (Hl : w \in Dom_map W) by (apply Hlabel; auto).
    destruct Hl as [web Hw].
    econstructor; eauto.
    + apply IHe.
      * eauto using Included_trans, has_label_proj_body.
      * eapply free_proj_k_inv; eauto.
Qed.

(* Cross-semantics Logical Relations *)
Definition R' (P : nat -> wval -> clval -> Prop) (i : nat) (r1 : res) (r2 : cres) :=
  match r1, r2 with
  | OOT, COOT => True
  | Res v1, CRes v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> wval -> clval -> Prop) (W : web_map) (ex : bool) (i : nat) (ρ1 : env) (ρ2 : cenv) (e : exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    bstep_fuel ρ1 e j1 r1 ->
    exists j2 r2,
      cbstep_fuel W ex ρ2 e j2 r2 /\
        R' P (i - j1) r1 r2.

(* W is sound for a particular program trace of e *)
Definition web_map_sound W Γ ex ρ1 ρ2 e :=
  forall i r1,
    bstep_fuel ρ1 e i r1 ->
    refine_env Γ ρ1 ρ2 ->
    exists r2,
      cbstep_fuel W ex ρ2 e i r2 /\
        refine_res r1 r2.

Fixpoint V (i : nat) (wv : wval) (cv : clval) {struct i} : Prop :=
  wf_val wv /\
  wf_cval cv /\
    refine_val wv cv /\
    match wv, cv with
    | TAG _ l1 v1, CTAG _ l2 W v2 =>
        l1 = l2 /\
          exists w2, W ! l2 = Some w2 /\
                       (w2 \in Exposed -> to_exposed cv) /\
                       match v1, v2 with
                       | Vconstr c1 vs1, CVconstr c2 vs2 =>
                           c1 = c2 /\
                             length vs1 = length vs2 /\
                             match i with
                             | 0 => True
                             | S i0 => Forall2 (V i0) vs1 vs2
                             end

                       | Vfun f1 ρ1 xs1 e1, CVfun f2 ρ2 xs2 e2 =>
                           f1 = f2 /\
                             xs1 = xs2 /\
                             e1 = e2 /\
                             match i with
                             | 0 => True
                             | S i0 =>
                                 forall j vs1 vs2 ρ3 ρ4,
                                   j <= i0 ->
                                   (w2 \in Exposed -> Forall to_exposed vs2) ->
                                   Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                                   set_lists xs1 vs1 (M.set f1 (Tag l1 (Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                                   set_lists xs2 vs2 (M.set f2 (CTag l2 W (CVfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                                   web_map_sound W (occurs_free e1) (exposedb w2) ρ3 ρ4 e1 ->
                                   E' V W (exposedb w2) (i0 - (i0 - j)) ρ3 ρ4 e1
                             end

                       | _, _ => False
                       end
    end.

Definition R := (R' V).

Definition E := (E' V).

(* Lemmas about [wf_cval], [wf_cres], and [wf_cenv] *)
Lemma V_wf_val_l {i v1 v2}:
  V i v1 v2 ->
  wf_val v1.
Proof. intros; destruct i; simpl in *; fcrush. Qed.

Lemma V_wf_val_Forall_l {i vs1 vs2} :
  Forall2 (V i) vs1 vs2 ->
  Forall wf_val vs1.
Proof. intros H. induction H; eauto using V_wf_val_l. Qed.

Lemma V_wf_res_l {i v1 v2}:
  V i v1 v2 ->
  wf_res (Res v1).
Proof. intros; eauto using V_wf_val_l; eauto. Qed.

Lemma R_wf_res_l {i r1 r2} :
  R i r1 r2 ->
  wf_res r1.
Proof.
  unfold R.
  intros.
  destruct r1; destruct r2; try contradiction;
    eauto using V_wf_val_l.
Qed.

Lemma V_wf_cval_r {i v1 v2}:
  V i v1 v2 ->
  wf_cval v2.
Proof. intros; destruct i; simpl in *; fcrush. Qed.

Lemma V_wf_cval_Forall_r {i vs1 vs2} :
  Forall2 (V i) vs1 vs2 ->
  Forall wf_cval vs2.
Proof. intros H. induction H; eauto using V_wf_cval_r. Qed.

Lemma V_wf_cres_r {i v1 v2}:
  V i v1 v2 ->
  wf_cres (CRes v2).
Proof. intros; eauto using V_wf_cval_r; eauto. Qed.

Lemma R_wf_cres_r {i r1 r2} :
  R i r1 r2 ->
  wf_cres r2.
Proof.
  unfold R.
  intros.
  destruct r1; destruct r2; try contradiction;
    eauto using V_wf_cval_r.
Qed.

Lemma V_refine_val {i v1 v2} :
  V i v1 v2 ->
  refine_val v1 v2.
Proof. intros; destruct i; simpl in *; fcrush. Qed.

Lemma V_refine_val_Forall {i vs1 vs2} :
  Forall2 (V i) vs1 vs2 ->
  Forall2 refine_val vs1 vs2.
Proof.
  eapply Forall2_impl; eauto.
  eauto using V_refine_val.
Qed.

Lemma R_refine_res {i r1 r2} :
  R i r1 r2 ->
  refine_res r1 r2.
Proof.
  unfold R, R'.
  intros.
  destruct r1; destruct r2; try contradiction; eauto.
  eauto using V_refine_val.
Qed.

(* Inversion Lemmas *)
Lemma R_res_inv_l i v1 r2 :
  R i (Res v1) r2 ->
  exists v2, r2 = CRes v2 /\ V i v1 v2.
Proof. intros. fcrush. Qed.

Lemma R_res_inv_l_V v1 r2 :
  (forall k, R k (Res v1) r2) ->
  exists v2, r2 = CRes v2 /\ (forall k, V k v1 v2).
Proof. intros. hauto. Qed.

(* Environment Relation *)
Definition G i Γ1 ρ1 ρ2 :=
  wf_env ρ1 /\
  wf_cenv ρ2 /\
    refine_env Γ1 ρ1 ρ2 /\
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

Lemma G_wf_env_l {i Γ1 ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  wf_env ρ1.
Proof. unfold G. fcrush. Qed.

Lemma G_wf_cenv_r {i Γ1 ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  wf_cenv ρ2.
Proof. unfold G. fcrush. Qed.

Lemma G_refine_env {i Γ1 ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  refine_env Γ1 ρ1 ρ2.
Proof. unfold G. fcrush. Qed.

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
  destruct H as [Hwf [Href HG]].
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

  destruct HG as [Hwf [Href HG]].
  split.
  eapply wf_env_set; eauto.
  eapply V_wf_val_l; eauto.

  split.
  eapply wf_cenv_set; eauto.
  eapply V_wf_cval_r; eauto.

  split.
  eapply refine_env_set; eauto.
  eapply G_refine_env; eauto.
  eapply V_refine_val; eauto.

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
  forall i j (V : nat -> wval -> clval -> Prop) vs1 vs2,
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
  destruct v1; destruct v2.
  destruct i; simpl in H0;
    destruct j; simpl; intros;
    rename w into W;
    destruct H0 as [Hwf1 [Hwf2 [Href [Heql [w [Hw [Hex HV]]]]]]]; subst.
  - destruct v; destruct c; fcrush.
  - fcrush.
  - repeat (split; auto).
    eexists; split; eauto.
    destruct v; destruct c; try contradiction.
    + destruct HV.
      destruct (exposed_reflect w); fcrush.
    + destruct HV as [Hc [Hlen HV]]; subst.
      destruct (exposed_reflect w); fcrush.
  - repeat (split; auto).
    destruct v; destruct c; try contradiction.
    + destruct HV as [Heqv [Heql [Heqe HV]]]; subst.
      eexists; repeat (split; eauto); intros.
      destruct (exposed_reflect w); intros.
      * specialize (HV j0 vs1 vs2 ρ3 ρ4).
        rewrite normalize_step in *; try lia.
        apply HV; eauto; lia.
      * specialize (HV j0 vs1 vs2 ρ3 ρ4).
        rewrite normalize_step in *; try lia.
        eapply HV; eauto; lia.
    + destruct HV as [Heqc [Hlen HV]]; subst.
      eexists; repeat (split; eauto).
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

Lemma E_mono {W ex ρ1 ρ2 e} i j:
  E W ex i ρ1 ρ2 e ->
  j <= i ->
  E W ex j ρ1 ρ2 e.
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
  destruct H as [Hwf1 [Hwf2 [Href HG]]].
  repeat (split; auto); intros.
  edestruct HG as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto; invc.
  eexists; repeat (split; eauto).
  eauto using V_mono.
Qed.

(* Compatibility Lemmas *)
Definition well_annotated W Γ e :=
  occurs_free e \subset Γ /\
  forall ex i ρ1 ρ2,
    web_map_sound W Γ ex ρ1 ρ2 e ->
    G i Γ ρ1 ρ2 ->
    E W ex i ρ1 ρ2 e.

Lemma ret_compat W Γ x :
  (x \in Γ) ->
  well_annotated W Γ (Eret x).
Proof.
  unfold well_annotated, web_map_sound, E, E', R, R', Ensembles.Included, Ensembles.In.
  split.
  fcrush.

  intros; simpl.
  specialize (H0 _ _ H3).
  inv H3.
  - exists 0, COOT; split; auto.
  - destruct r1.
    fcrush.
    destruct H0 as [cv [Hcbstep Href]].
    eapply G_refine_env; eauto.
    inv Href.
    eexists; eexists; split; eauto; simpl.
    inv H4; inv Hcbstep.
    inv H4.
    edestruct (G_get H1) as [v2 [Heqv2 HV]]; eauto.
    invc.
    eapply V_mono; eauto; lia.
Qed.

Lemma web_map_sound_subset W Γ1 Γ2 ex ρ1 ρ2 e :
  web_map_sound W Γ1 ex ρ1 ρ2 e ->
  Γ1 \subset Γ2 ->
  web_map_sound W Γ2 ex ρ1 ρ2 e.
Proof.
  unfold web_map_sound.
  intros.
  eapply H; eauto.
  eapply refine_env_subset; eauto.
Qed.

Lemma Vfun_V W Γ f l w xs e  :
  W ! l = Some w ->
  well_annotated W (FromList xs :|: (f |: Γ)) e ->
  forall {i ρ1 ρ2},
    wf_val (Tag l (Vfun f ρ1 xs e)) ->
    wf_cval (CTag l W (CVfun f ρ2 xs e)) ->
    refine_val (Tag l (Vfun f ρ1 xs e)) (CTag l W (CVfun f ρ2 xs e)) ->
    G i Γ ρ1 ρ2 ->
    V i (Tag l (Vfun f ρ1 xs e)) (CTag l W (CVfun f ρ2 xs e)).
Proof.
  unfold well_annotated.
  intros HW He i.
  induction i; simpl; intros; auto;
    repeat (split; auto);
    intros; (repeat split; auto);
    eexists; repeat (split; eauto); intros.
  destruct He as [HS He].
  apply (He _ (i - (i - j)) ρ3 ρ4); auto.

  eapply web_map_sound_subset; eauto.

  eapply G_subset; eauto.
  eapply G_set_lists; eauto.
  eapply G_set; eauto.
  + apply G_mono with (S i); eauto; lia.
  + apply V_mono with i; try lia.
    eapply IHi; eauto.
    apply G_mono with (S i); eauto; lia.
  + fcrush.
Qed.

Lemma web_map_sound_fun_inv_k W Γ ex ρ1 ρ2 f l xs e k:
  web_map_sound W Γ ex ρ1 ρ2 (Efun f l xs e k) ->
  refine_env Γ ρ1 ρ2 ->
  web_map_sound W (f |: Γ) ex (M.set f (Tag l (Vfun f ρ1 xs e)) ρ1) (M.set f (CTag l W (CVfun f ρ2 xs e)) ρ2) k.
Proof.
  unfold web_map_sound.
  intros.
  edestruct (H (S i) r1) as [r2 [Hcbstep Href]]; eauto.
  eexists; split; eauto.
  fcrush.
Qed.

Lemma fun_compat W Γ e k f l w xs :
  W ! l = Some w ->
  well_annotated W (FromList xs :|: (f |: Γ)) e ->
  well_annotated W (f |: Γ) k ->
  well_annotated W Γ (Efun f l xs e k).
Proof.
  unfold well_annotated, E, E'.
  intros HWl [HSe He] [HSk Hk].
  split; intros.
  {
    unfold Ensembles.Included, Ensembles.In in *.
    intros.
    inv H; fcrush.
  }

  pose proof H2 as Hbstep.
  inv H2.
  - exists 0, COOT; split; simpl; eauto.
  - destruct r1.
    fcrush.
    assert (Hwfρ1 : wf_env ρ1) by eauto using G_wf_env_l.
    assert (Hwfρ2 : wf_cenv ρ2) by eauto using G_wf_cenv_r.
    assert (Hrefρ : refine_env Γ ρ1 ρ2) by eauto using G_refine_env.
    edestruct (H (S c) (Res w0)) as [cv [Hcbstep Href]]; eauto.

    inv Hcbstep; inv H3.
    inv H4; invc.
    edestruct (Hk ex (i - 1) (M.set f (Tag l (Vfun f ρ1 xs e)) ρ1) (M.set f (CTag l W (CVfun f ρ2 xs e)) ρ2)) with (j1 := c) (r1 := (Res w0)) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eauto using web_map_sound_fun_inv_k.
    + eapply G_subset.
      eapply G_set; eauto.
      eapply G_mono with i; eauto; lia.
      * eapply Vfun_V; eauto.
        -- econstructor; eauto.
        -- apply G_mono with i; eauto; lia.
      * apply Included_refl.
    + exists (S j2), r2; split; auto.
      * econstructor; simpl; eauto.
        destruct ex; simpl in *; auto.
        destruct r2; fcrush.
      * eapply R_mono; eauto; lia.
Qed.

Lemma app_compat W Γ xs f l w :
  (W ! l = Some w) ->
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  well_annotated W Γ (Eapp f l xs).
Proof.
  unfold well_annotated, E, E'.
  intros HW Hf Hxs.
  intros; simpl.
  split; intros.
  {
    unfold FromList, Ensembles.Included, Ensembles.In in *.
    intros.
    inv H; fcrush.
  }

  pose proof H2 as Hbstep.
  inv H2.
  - exists 0, COOT; split; simpl; auto.
  - destruct r1.
    fcrush.
    assert (Hrefρ : refine_env _ ρ1 ρ2) by eauto using G_refine_env.
    edestruct (H (S c) (Res w0)) as [cv [Hcbstep Href]]; eauto.
    inv Hcbstep; inv H3; inv Href.
    inv H4; invc.
    edestruct (G_get H0 f) as [fv2 [Heqfv2 HV]]; eauto.
    destruct i.
    inv H1.
    rename w0 into v.
    destruct fv2; simpl in HV; invc;
      rename w into W';
      destruct HV as [Hwf1 [Hwf2 [Hrefv [Heql [w2 [HW' [Hex [Heqf [Heqxs [Heqe HV]]]]]]]]]]; subst; invc.

    edestruct (G_get_list H0 xs vs) as [vs2 [Heqvs2 Vvs]]; eauto; invc.

    destruct (set_lists_length3 (M.set f'0 (CTag l0 W' (CVfun f'0 ρ'0 xs'0 e0)) ρ'0) xs'0 vs2) as [ρ4 Heqρ4].
    unfold clval in *.
    rewrite <- (set_lists_length_eq _ _ _ _ H14); auto.

    assert (HE : E W' (exposedb w2) (i - (i - i)) ρ'' ρ4 e0).
    {
      eapply (HV i vs vs2); eauto.
      intros.
      destruct H19; auto.
      apply V_mono_Forall with (S i); auto; lia.

      unfold web_map_sound; intros.
      edestruct (H (S i0) r1) as [r2 [Hcbstep2 Hrefr2]]; eauto.
      inv Hrefr2.
      - inv Hcbstep2.
        inv H7.
        unfold clval in *.
        invc; eauto.
      - inv Hcbstep2.
        inv H15.
        unfold clval in *.
        invc; fcrush.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E, E' in HE.
    destruct (HE c (Res v)) as [j2 [r2 [He0 Rr]]]; try lia; auto.
    exists (S j2), r2; split; eauto.

    edestruct (R_res_inv_l _ _ _ Rr) as [cv' [Heqcv' HV']]; eauto; subst.
    assert (Heq : v' = cv' /\ c = j2).
    {
      unfold clval in *; invc.
      eapply cbstep_fuel_deterministic; eauto.
    }
    inv Heq; eauto.
Qed.

Lemma letapp_compat W Γ k xs x f l w :
  W ! l = Some w ->
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  well_annotated W (x |: Γ) k ->
  well_annotated W Γ (Eletapp x f l xs k).
Proof.
  unfold well_annotated, web_map_sound, E, E'.
  intros HWl Hf Hxs [HSk Hk].
  split; intros.
  {
    unfold FromList, Ensembles.Included, Ensembles.In in *.
    intros.
    inv H; fcrush.
  }

  intros; simpl.
  assert (Hrefρ : refine_env _ ρ1 ρ2) by eauto using G_refine_env.
  pose proof H2 as Hbstep.

  inv H2.
  - exists 0, COOT; split; simpl; auto.
  - destruct r1.
    fcrush.
    edestruct (H (S c) (Res w0)) as [cv [Hcbstep Href]]; eauto.
    inv Href.
    inv H3; inv Hcbstep.
    inv H3; invc.

    edestruct (G_get H0 f) as [fv2 [Heqfv2 HV]]; eauto.
    destruct i. inv H1.
    destruct fv2; simpl in HV; invc;
      rename w into W';
      destruct HV as [Hv1 [Hv2 [Href [Hl' [w2 [HW' [Hex [Heqf [Heqxs [Heqe HV]]]]]]]]]]; invc.

    edestruct (G_get_list H0 xs vs) as [vs2 [Heqvs2 Vvs]]; eauto; invc.

    destruct (set_lists_length3 (M.set f'0 (CTag l0 W' (CVfun f'0 ρ'0 xs'0 e0)) ρ'0) xs'0 vs2) as [ρ4 Heqρ4].
    {
      unfold clval in *.
      rewrite <- (Forall2_length _ _ _ Vvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H13); auto.
    }

    assert (Hc : c0 = c /\ refine_val v v0).
    {
      eapply bstep_fuel_cbstep_fuel_refine; eauto.
      assert (HVs : Forall2 refine_val vs vs2) by eauto using V_refine_val_Forall.
      inv Href.
      inv H3.

      eapply refine_env_subset; eauto.
      assert (Hrefenv : refine_env (f'0 |: Γ0) (M.set f'0 (Tag l0 (Vfun f'0 ρ' xs'0 e0)) ρ') (M.set f'0 (CTag l0 W' (CVfun f'0 ρ'0 xs'0 e0)) ρ'0)).
      {
        eapply refine_env_set; eauto.
      }
      eapply refine_env_set_lists; eauto.
    }
    assert (Hc' : c'0 = c') by lia.
    inv Hc.
    unfold clval in *; invc.

    assert (HE : E W' (exposedb w2) (i - (i - i)) ρ'' ρ4 e0).
    {
      eapply (HV i vs vs2); eauto.
      intros.
      destruct H24; auto.
      apply V_mono_Forall with (S i); auto; lia.

      unfold web_map_sound; intros.
      destruct r1.
      - edestruct (H (S i0) OOT) as [r2 [Hcbstep_e Hrefr]]; eauto.
        inv Hcbstep_e.
        inv Hrefr.
        inv H8.
        unfold clval in *; invc.

        assert (Hc : c = c0 /\ refine_val v v1).
        {
          eapply bstep_fuel_cbstep_fuel_refine; eauto.
        }
        inv Hc.
        eapply bstep_fuel_lt_Res_not_OOT with (c0 := (c0 + c'0)) in H14; eauto; try lia.
        contradiction.

        unfold clval in *; invc; eauto.
      - assert (Hcv : v = w /\ c = i0).
        {
          eapply bstep_fuel_deterministic; eauto.
        }
        inv Hcv.

        edestruct (H (S (i0 + c')) (Res w0)) as [r2 [Hcbstep_e Hrefr]]; eauto.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E in HE.
    destruct (HE c (Res v)) as [j1 [ra [Hap Rra]]]; try lia; auto.

    simpl in Rra.
    destruct ra; try contradiction.

    assert (Heq : c0 = v0 /\ j1 = c).
    {
      eapply cbstep_fuel_deterministic; eauto.
    }
    inv Heq.

    edestruct (Hk ex (i - c) (M.set x v ρ1) (M.set x v0 ρ2))
      with (j1 := c') (r1 := (Res w0)) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + intros.

      edestruct (H (S (c + i0)) r1) as [r2 [Hcbstep2 Href2]]; eauto.
      inv Hcbstep2.
      inv H8; unfold clval in *; invc.

      * assert (Hcv : v0 = v1 /\ c = c0).
        {
          eapply cbstep_fuel_deterministic; eauto.
        }
        inv Hcv.
        rewrite_math (c'0 = i0); eauto.
      * inv Href2.
        eapply cbstep_fuel_lt_Res_not_OOT with (c0 := (c + i0)) in Hap; eauto; try lia.
        contradiction.
    + eapply G_subset.
      ++ eapply G_set; eauto.
         eapply G_mono with (S i); eauto; lia.
      ++ apply Included_refl.
    + exists (S (c + j2)), r2; split.
      ++ constructor; auto.
         ** econstructor; eauto.
         ** destruct ex; simpl in *; auto.
            unfold R' in Rr.
            destruct r2; try contradiction; auto.
            eauto using cbstep_fuel_exposed_inv.
      ++ eapply R_mono; eauto; lia.
Qed.

Lemma case_nil_compat W Γ x l w :
  W ! l = Some w ->
  (x \in Γ) ->
  well_annotated W Γ (Ecase x l []).
Proof.
  unfold well_annotated, E, E'.
  intros HWl Hx.
  split; intros.
  {
    unfold FromList, Ensembles.Included, Ensembles.In in *.
    intros.
    inv H; fcrush.
  }
  inv H2; fcrush.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {W Γ e}:
  web_map_spec W Γ e -> well_annotated W Γ e.
Proof.
  intros.
  induction H; intros.
  - eapply ret_compat; eauto.
  - eapply fun_compat; eauto.
  - eapply app_compat; eauto.
  - eapply letapp_compat; eauto.
  - admit. (* eapply constr_compat; eauto. *)
  - admit. (* eapply proj_compat; eauto. *)
  - eapply case_nil_compat; eauto.
  - admit. (* eapply case_cons_compat; eauto.*)
Admitted.

(* Top Level *)

(* Top-level Compilation Unit & Linking *)
Inductive cexp : Type :=
| CEexp : web_map -> exp -> cexp
| CElink : var -> cexp -> cexp -> cexp.

Hint Constructors cexp : core.

(* Linking *)
Definition clink x e1 e2 : cexp := CElink x e1 e2.

Inductive occurs_free_top : cexp -> vars :=
| Free_cexp :
  forall W e x,
    occurs_free e x ->
    occurs_free_top (CEexp W e) x

| Free_clink1 :
  forall v x e1 e2,
    occurs_free_top e1 x ->
    occurs_free_top (CElink v e1 e2) x

| Free_clink2 :
  forall v x e1 e2,
    v <> x ->
    occurs_free_top e2 x ->
    occurs_free_top (CElink v e1 e2) x.

Hint Constructors occurs_free_top : core.

Lemma occurs_free_top_cexp W e :
  (occurs_free_top (CEexp W e)) <--> (occurs_free e).
Proof. split; unfold Ensembles.Included, Ensembles.In; fcrush. Qed.

(* Top-level Checking Semantics *)
Inductive cbstep_top (ρ : cenv) : cexp -> fuel -> cres -> Prop :=
| Cbstep_exp_top :
  forall {W e c r},
    cbstep W true ρ e c r ->
    cbstep_top ρ (CEexp W e) c r

| Cbstep_link_top_trivial :
  forall {x e k},
    cbstep_top ρ (CElink x e k) 0 COOT

| Cbstep_link_top_Res :
  forall {x e k c' c r v},
    cbstep_top_fuel ρ e c (CRes v) ->
    cbstep_top_fuel (M.set x v ρ) k c' r ->
    cbstep_top ρ (CElink x e k) (S (c + c')) r

| Cbstep_link_top_OOT :
  forall {x e k c},
    cbstep_top_fuel ρ e c COOT ->
    cbstep_top ρ (CElink x e k) (S c) COOT

with cbstep_top_fuel (ρ : cenv) : cexp -> fuel -> cres -> Prop :=
| CbstepTF_OOT :
  forall {e},
    cbstep_top_fuel ρ e 0 COOT

| CbstepTF_Step :
  forall {e c r},
    cbstep_top ρ e c r ->
    to_exposed_cres r ->
    cbstep_top_fuel ρ e (S c) r.

Hint Constructors cbstep_top : core.
Hint Constructors cbstep_top_fuel : core.

(* The step-index is aligned between the two semantics. *)
Lemma cbstep_fuel_cbstep_top_fuel W ρ e j r:
  cbstep_fuel W true ρ e j r ->
  cbstep_top_fuel ρ (CEexp W e) j r.
Proof.
  intros H; inv H; eauto.
Qed.

Lemma cbstep_top_fuel_cbstep_fuel W ρ e j r:
  cbstep_top_fuel ρ (CEexp W e) j r ->
  cbstep_fuel W true ρ e j r.
Proof.
  intros H; inv H; eauto.
  match goal with
  | [ H : cbstep_top _ _ _ _ |- _ ] => inv H
  end; eauto.
Qed.

Lemma cbstep_top_fuel_exposed_inv ρ e j r :
  cbstep_top_fuel ρ e j r ->
  to_exposed_cres r.
Proof. intros. inv H; eauto. Qed.

Lemma cbstep_top_wf_res ρ e c r :
  wf_cenv ρ ->
  cbstep_top ρ e c r ->
  wf_cres r
with cbstep_top_fuel_wf_res ρ e c r :
  wf_cenv ρ ->
  cbstep_top_fuel ρ e c r ->
  wf_cres r.
Proof.
  - intros Hw H. inv H.
    + (* Cbstep_exp_top *)
      eapply cbstep_wf_res; eauto.
    + (* Cbstep_link_top_trivial *)
      constructor.
    + (* Cbstep_link_top_Res *)
      assert (Hwfv : wf_cres (CRes v))
        by (eapply cbstep_top_fuel_wf_res; eauto).
      inv Hwfv.
      assert (Hwfρx : wf_cenv (M.set x v ρ)) by (eapply wf_cenv_set; eauto).
      eapply cbstep_top_fuel_wf_res; eauto.
    + (* Cbstep_link_top_OOT *)
      constructor.
  - intros Hw H. inv H.
    + (* CbstepTF_OOT *)
      constructor.
    + (* CbstepTF_Step *)
      eapply cbstep_top_wf_res; eauto.
Qed.

(* Semantic Weakening for the Top-level Checking Semantics.
   Mirrors [cbstep_subenv]: closures may differ in captured envs as long as
   they agree on the body's free vars. The proof is a mutual induction on
   cbstep_top / cbstep_top_fuel; the CEexp case delegates to [cbstep_subenv]. *)
Lemma cbstep_top_subenv {Γ ρ1 ρ2 e c r1}:
  wf_cenv ρ2 ->
  (occurs_free_top e) \subset Γ ->
  csubenv Γ ρ1 ρ2 ->
  cbstep_top ρ1 e c r1 ->
  (exists r2, cbstep_top ρ2 e c r2 /\ csubres r1 r2 /\ wf_cres r2)
with cbstep_top_fuel_subenv {Γ ρ1 ρ2 e c r1}:
  wf_cenv ρ2 ->
  (occurs_free_top e) \subset Γ ->
  csubenv Γ ρ1 ρ2 ->
  cbstep_top_fuel ρ1 e c r1 ->
  (exists r2, cbstep_top_fuel ρ2 e c r2 /\ csubres r1 r2 /\ wf_cres r2).
Proof.
  - (* cbstep_top_subenv *)
    intros Hρ2 HFV Hsub Hcb.
    inv Hcb.
    + (* Cbstep_exp_top *)
      assert (HFV' : occurs_free e0 \subset Γ).
      { unfold Ensembles.Included, Ensembles.In in *. intros z Hz.
        apply HFV. constructor; auto. }
      edestruct (cbstep_subenv Hρ2 HFV' Hsub H) as [r2 [Hr2 [Hsr Hwfr]]].
      exists r2; repeat split; auto.
    + (* Cbstep_link_top_trivial *)
      exists COOT; repeat split; auto.
    + (* Cbstep_link_top_Res *)
      assert (HFVe : occurs_free_top e0 \subset Γ).
      { unfold Ensembles.Included, Ensembles.In in *. intros z Hz.
        apply HFV. econstructor; eauto. }
      edestruct (cbstep_top_fuel_subenv _ _ _ _ _ _ Hρ2 HFVe Hsub H)
        as [re1 [Hre1 [Hsre1 Hwfre1]]].
      inv Hsre1.
      assert (HFVk : occurs_free_top k \subset (x |: Γ)).
      { unfold Ensembles.Included, Ensembles.In in *. intros z Hz.
        destruct (M.elt_eq z x) as [<-|Hne].
        - left; auto.
        - right. apply HFV. eapply Free_clink2; eauto. }
      assert (Hwfρ2x : wf_cenv (M.set x v2 ρ2))
        by (eapply wf_cenv_set; eauto; inv Hwfre1; auto).
      assert (Hsubx : csubenv (x |: Γ) (M.set x v ρ1) (M.set x v2 ρ2))
        by (eapply csubenv_set; eauto).
      edestruct (cbstep_top_fuel_subenv _ _ _ _ _ _ Hwfρ2x HFVk Hsubx H0)
        as [re2 [Hre2 [Hsre2 Hwfre2]]].
      exists re2; repeat split; auto.
      econstructor; eauto.
    + (* Cbstep_link_top_OOT *)
      assert (HFVe : occurs_free_top e0 \subset Γ).
      { unfold Ensembles.Included, Ensembles.In in *. intros z Hz.
        apply HFV. econstructor; eauto. }
      edestruct (cbstep_top_fuel_subenv _ _ _ _ _ _ Hρ2 HFVe Hsub H)
        as [re1 [Hre1 [Hsre1 Hwfre1]]].
      inv Hsre1.
      exists COOT; repeat split; auto.

  - (* cbstep_top_fuel_subenv *)
    intros Hρ2 HFV Hsub Hcb.
    inv Hcb.
    + exists COOT; repeat split; auto.
    + edestruct (cbstep_top_subenv _ _ _ _ _ _ Hρ2 HFV Hsub H)
        as [r2 [Hr2 [Hsr Hwfr]]].
      exists r2; repeat split; auto.
      constructor; auto.
      eapply csubres_to_exposed_cres; eauto.
Qed.

Lemma cbstep_top_fuel_drop_unused {f val ρ e c r}:
  ~ (f \in occurs_free_top e) ->
  wf_cenv ρ ->
  cbstep_top_fuel (M.set f val ρ) e c r ->
  exists r', cbstep_top_fuel ρ e c r' /\ csubres r r' /\ wf_cres r'.
Proof.
  intros Hf Hwf Hcb.
  eapply @cbstep_top_fuel_subenv with (Γ := occurs_free_top e); eauto.
  - apply Included_refl.
  - constructor; intros z Hz w Hgw.
    destruct (M.elt_eq z f) as [<-|Hne]; [contradiction|].
    rewrite M.gso in Hgw by auto.
    exists w; split; auto.
    apply csubval_refl. eapply wf_cenv_get; eauto.
Qed.

(* Cross-language Logical Relations *)

Definition E_top' (P : nat -> wval -> clval -> Prop) (i : nat) (ρ1 : env) (e1 : exp) (ρ2 : cenv) (e2 : cexp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    bstep_fuel ρ1 e1 j1 r1 ->
    exists j2 r2,
      cbstep_top_fuel ρ2 e2 j2 r2 /\
      R' P (i - j1) r1 r2.

Fixpoint V_top (i : nat) (wv : wval) (cv : clval) {struct i} : Prop :=
  wf_val wv /\
  wf_cval cv /\
    refine_val wv cv /\
    to_exposed cv /\
    match wv, cv with
    | TAG _ l1 v1, CTAG _ l2 W v2 =>
        l1 = l2 /\
          match v1, v2 with
          | Vconstr c1 vs1, CVconstr c2 vs2 =>
              c1 = c2 /\
                length vs1 = length vs2 /\
                match i with
                | 0 => True
                | S i0 => Forall2 (V_top i0) vs1 vs2
                end

          | Vfun f1 ρ1 xs1 e1, CVfun f2 ρ2 xs2 e2 =>
              f1 = f2 /\
                xs1 = xs2 /\
                e1 = e2 /\
                match i with
                | 0 => True
                | S i0 =>
                    forall j vs1 vs2 ρ3 ρ4,
                      j <= i0 ->
                      Forall to_exposed vs2 ->
                      Forall2 (V_top (i0 - (i0 - j))) vs1 vs2 ->
                      set_lists xs1 vs1 (M.set f1 (Tag l1 (Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                      set_lists xs2 vs2 (M.set f2 (CTag l2 W (CVfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                      web_map_sound W (occurs_free e1) true ρ3 ρ4 e1 ->
                      E_top' V_top (i0 - (i0 - j)) ρ3 e1 ρ4 (CEexp W e1)
                end

          | _, _ => False
          end
    end.

Lemma V_V_top_Forall :
  forall i,
    (forall m : nat,
        m < S i ->
        forall v1 v2,
          to_exposed v2 ->
          V m v1 v2 <-> V_top m v1 v2) ->
    forall j vs1 vs2,
      j <= i ->
      Forall to_exposed vs2 ->
      Forall2 (V j) vs1 vs2 <-> Forall2 (V_top j) vs1 vs2.
Proof.
  intros.
  revert vs1 j H0.
  induction H1; simpl; intros.
  - split; intros; inv H1; auto.
  - split; intros; inv H3; constructor; auto;
      solve [ eapply H; try lia; eauto |
              eapply IHForall; eauto ].
Qed.

Lemma V_V_top :
  forall i v1 v2,
    to_exposed v2 ->
    (V i v1 v2 <-> V_top i v1 v2).
Proof.
  intro i.
  induction i using lt_wf_rec; intros.
  split; intros.
  - destruct i; simpl in *.
    + destruct v1; destruct v2.
      destruct v; destruct c; try firstorder.
    + destruct v1; destruct v2.
      destruct v; destruct c; try firstorder;
        rename w into W.
      * destruct H1 as [Hwf1 [Hwf2 [Href [Heql [w [HW [Hex [Heqv [Heqxs [Heqw HV]]]]]]]]]]; subst.
        repeat (split; eauto); intros.

        assert (HEV : E' V W (exposedb w) (i - (i - j)) ρ3 ρ4 e0).
        {
          eapply HV; eauto.
          eapply V_V_top_Forall; eauto; try lia.
          inv H0; invc.
          destruct (exposed_reflect w0); fcrush.
        }
        unfold E_top' in *; intros.
        edestruct HEV as [j2 [r2 [Hstep HR]]]; eauto.
        inv H0; invc.
        destruct (exposed_reflect w0); try contradiction.

        exists j2, r2; split; eauto.
        eapply cbstep_fuel_cbstep_top_fuel; eauto.
        unfold R' in *.
        destruct r1; destruct r2; auto.
        eapply H; eauto; try lia.
        eapply cbstep_fuel_exposed_inv in Hstep; eauto; fcrush.
      * eapply V_V_top_Forall; fcrush.
  - destruct i; simpl in *;
      destruct H1 as [Hwf1 [Hwf2 [Href [Hex HV]]]].
    + destruct v1; destruct v2.
      destruct v; destruct c; try firstorder; subst; invc.
      * inv Hex.
        eexists; repeat (split; eauto); fcrush.
      * inv Hex.
        eexists; repeat (split; eauto); fcrush.
    + destruct v1; destruct v2.
      destruct v; destruct c; try firstorder; subst; invc.
      * inv Hex.
        eexists; repeat (split; eauto); intros.
        rename w into W.

        inv H0; invc.
        assert (HEV : E_top' V_top (i - (i - j)) ρ3 e0 ρ4 (CEexp W e0)).
        {
          eapply (H5 _ vs1 vs2); eauto.
          eapply V_V_top_Forall; eauto; try lia.
          destruct (exposed_reflect w); fcrush.
        }
        unfold E' in *; intros.
        edestruct HEV as [j2 [r2 [Hstep HR]]]; eauto.
        destruct (exposed_reflect w); try contradiction.

        exists j2, r2; split; eauto.
        eapply cbstep_top_fuel_cbstep_fuel; eauto.

        unfold R' in *.
        destruct r1; destruct r2; auto.
        eapply H; eauto; try lia.
        eapply cbstep_top_fuel_exposed_inv in Hstep; eauto; fcrush.
      * inv Hex.
        eexists; (repeat split; eauto).
        eapply V_V_top_Forall; eauto.
Qed.

Definition R_top := (R' V_top).

Lemma R_R_top :
  forall i r1 r2,
    to_exposed_cres r2 ->
    (R i r1 r2 <-> R_top i r1 r2).
Proof.
  unfold R, R_top, R'.
  intros.
  split; destruct r1; destruct r2; try contradiction;
    inv H; intros; eauto;
    eapply V_V_top; eauto.
Qed.

Definition E_top := (E_top' V_top).

Lemma E_E_top W i ρ1 ρ2 e :
  E W true i ρ1 ρ2 e ->
  E_top i ρ1 e ρ2 (CEexp W e).
Proof.
  unfold E, E_top, E', E_top'.
  intros.
  edestruct H as [j2 [r2 [Hcbstep HR]]]; eauto.
  exists j2, r2; split; eauto.
  - eapply cbstep_fuel_cbstep_top_fuel; eauto.
  - eapply R_R_top; eauto.
    eapply cbstep_fuel_exposed_inv; eauto.
Qed.

Lemma E_top_E W i ρ1 ρ2 e :
  E_top i ρ1 e ρ2 (CEexp W e) ->
  E W true i ρ1 ρ2 e.
Proof.
  unfold E, E_top, E', E_top'.
  intros.
  edestruct H as [j2 [r2 [Hcbstep HR]]]; eauto.
  exists j2, r2; split; eauto.
  - eapply cbstep_top_fuel_cbstep_fuel; eauto.
  - eapply R_R_top; eauto.
    eapply cbstep_top_fuel_exposed_inv; eauto.
Qed.

Lemma V_top_refine_val {i v1 v2}:
  V_top i v1 v2 ->
  refine_val v1 v2.
Proof.
  intros HV.
  destruct i; simpl in *; fcrush.
Qed.

Lemma V_top_wf_val_l {i v1 v2}:
  V_top i v1 v2 ->
  wf_val v1.
Proof.
  intros HV.
  destruct i; simpl in *; fcrush.
Qed.

Lemma V_top_wf_val_Forall_l {i vs1 vs2} :
  Forall2 (V_top i) vs1 vs2 ->
  Forall wf_val vs1.
Proof.
  intros.
  induction H; auto.
  constructor; auto.
  eapply V_top_wf_val_l; eauto.
Qed.

Lemma V_top_wf_res_l {i v1 v2}:
  V_top i v1 v2 ->
  wf_res (Res v1).
Proof.
  intros HV.
  constructor.
  eapply V_top_wf_val_l; eauto.
Qed.

Lemma V_top_wf_cval_r {i v1 v2}:
  V_top i v1 v2 ->
  wf_cval v2.
Proof.
  intros HV.
  destruct i; simpl in *; fcrush.
Qed.

Lemma V_top_wf_cval_Forall_r {i vs1 vs2} :
  Forall2 (V_top i) vs1 vs2 ->
  Forall wf_cval vs2.
Proof.
  intros.
  induction H; auto.
  constructor; auto.
  eapply V_top_wf_cval_r; eauto.
Qed.

Lemma V_top_wf_cres_r {i v1 v2}:
  V_top i v1 v2 ->
  wf_cres (CRes v2).
Proof.
  intros HV.
  constructor.
  eapply V_top_wf_cval_r; eauto.
Qed.

Lemma V_top_exposed_r {i v1 v2}:
  V_top i v1 v2 ->
  to_exposed v2.
Proof.
  intros.
  destruct i; destruct v2;
    simpl in *; fcrush.
Qed.

Lemma V_top_exposed_Forall_r {i vs1 vs2} :
  Forall2 (V_top i) vs1 vs2 ->
  Forall to_exposed vs2.
Proof.
  intros.
  induction H; auto.
  constructor; auto.
  eapply V_top_exposed_r; eauto.
Qed.

Lemma R_top_wf_cres_l {i r1 r2} :
  R_top i r1 r2 ->
  wf_cres r2.
Proof.
  unfold R.
  intros.
  destruct r1; destruct r2; try contradiction; auto.
  constructor.
  eapply V_top_wf_cval_r; eauto.
Qed.

(* Top-level Inversion Lemmas *)
Lemma R_top_res_inv_l i v1 r2 :
  R_top i (Res v1) r2 ->
  exists v2, r2 = CRes v2 /\ V_top i v1 v2.
Proof.
  intros.
  destruct r2; simpl in *; try contradiction.
  eexists; split; eauto.
Qed.

Lemma R_top_res_inv_l_V v1 r2 :
  (forall k, R_top k (Res v1) r2) ->
  exists v2, r2 = CRes v2 /\ (forall k, V_top k v1 v2).
Proof. intros. hauto. Qed.

Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  wf_env ρ1 /\
  wf_cenv ρ2 /\
    refine_env Γ1 ρ1 ρ2 /\
    Γ2 \subset Γ1 /\
    forall x,
      (x \in Γ1) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
          M.get x ρ2 = Some v2 /\
          to_exposed v2 /\
          V_top i v1 v2.

Lemma G_top_wf_env_l i Γ1 ρ1 Γ2 ρ2 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  wf_env ρ1.
Proof. unfold G_top. intros; tauto. Qed.

Lemma G_top_wf_cenv_r i Γ1 ρ1 Γ2 ρ2 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  wf_cenv ρ2.
Proof. unfold G_top. intros; tauto. Qed.

Lemma G_top_refine_env i Γ1 ρ1 Γ2 ρ2 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  refine_env Γ1 ρ1 ρ2.
Proof. unfold G_top. intros; tauto. Qed.

Lemma G_top_subset_inv i Γ1 ρ1 Γ2 ρ2 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  Γ2 \subset Γ1.
Proof. unfold G_top; intros; tauto. Qed.

Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  Γ3 \subset Γ1 ->
  Γ4 \subset Γ3 ->
  G_top i Γ3 ρ1 Γ4 ρ2.
Proof.
  unfold G_top.
  intros.
  destruct H as [Hwf1 [Hwf2 [Href [Hs HG]]]].
  repeat (split; auto); intros.
  edestruct HG as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto; invc.
  fcrush.
Qed.

(* Top-level Environment Lemmas *)
Lemma G_top_get {Γ1 Γ2 i ρ1 ρ2}:
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  forall x,
    (x \in Γ1) ->
    exists v1 v2,
      M.get x ρ1 = Some v1 /\
        M.get x ρ2 = Some v2 /\
        V_top i v1 v2.
Proof.
  unfold G_top.
  intros.
  destruct H as [Hwf1 [Hwf2 [Href [Hs HG]]]].
  edestruct HG as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto.
Qed.

Lemma G_top_get_list {i Γ1 ρ1 Γ2 ρ2} :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  forall xs,
    (FromList xs) \subset Γ1 ->
    exists vs1 vs2,
      get_list xs ρ1 = Some vs1 /\
        get_list xs ρ2 = Some vs2 /\
        Forall2 (V_top i) vs1 vs2.
Proof.
  intros HG xs.
  intros.
  induction xs; simpl; intros.
  - eexists; eexists; repeat split; eauto.
  - rewrite FromList_cons in H.
    edestruct (G_top_get HG) as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto.

    edestruct IHxs as [vs1 [vs2 [Heqvs1 [Heqvs2 HVs]]]]; eauto.
    eapply Included_trans; eauto.
    apply Included_Union_r.

    rewrite Heqv1.
    rewrite Heqvs1.
    rewrite Heqv2.
    rewrite Heqvs2.
    exists (v1 :: vs1), (v2 :: vs2); repeat (split; auto).
Qed.

Lemma G_top_set {i Γ1 ρ1 Γ2 ρ2}:
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  forall {x v1 v2},
    V_top i v1 v2 ->
    G_top i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
Proof.
  intros.
  unfold G_top; intros.

  split.
  eapply wf_env_set; eauto.
  eapply G_top_wf_env_l; eauto.
  eapply V_top_wf_val_l; eauto.

  split.
  eapply wf_cenv_set; eauto.
  eapply G_top_wf_cenv_r; eauto.
  eapply V_top_wf_cval_r; eauto.

  split.
  eapply refine_env_set; eauto.
  eapply G_top_refine_env; eauto.
  eapply V_top_refine_val; eauto.

  split.
  apply Included_Union_compat; auto.
  apply Included_refl.
  eapply G_top_subset_inv; eauto.

  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss.
    eexists; eexists; repeat split; eauto.
    eapply V_top_exposed_r; eauto.
  - repeat (rewrite M.gso; auto).
    assert (x0 \in Γ1) by fcrush.
    edestruct (G_top_get H x0) as [v1' [v2' [Heqv1' [Heqv2' HV]]]]; eauto; invc.
    eexists; eexists; repeat (split; eauto).
    eapply V_top_exposed_r; eauto.
Qed.

Lemma G_top_set_lists {i Γ1 ρ1 Γ2 ρ2}:
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 (V_top i) vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    G_top i (FromList xs :|: Γ1) ρ3 (FromList xs :|: Γ2) ρ4.
Proof.
  intros HG xs.
  assert (HΓ : Γ2 \subset Γ1) by (eapply G_top_subset_inv; eauto).
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    inv H0; inv H1.
    eapply G_top_subset; eauto.
    normalize_sets.
    rewrite Union_Empty_set_neut_l; eauto.
    apply Included_refl.
    eapply Included_Union_compat; eauto.
    apply Included_refl.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
    inv H; inv H0; inv H1.
    eapply G_top_subset with (Γ1 := (a |: (FromList xs :|: Γ1))) (Γ2 := (a |: (FromList xs :|: Γ2))); eauto.
    eapply G_top_set; eauto.
    normalize_sets.
    rewrite Union_assoc.
    apply Included_refl.
    eapply Included_Union_compat; eauto.
    apply Included_refl.
Qed.

(* G_top is stronger than G *)
Lemma G_top_G :
  forall {i Γ1 ρ1 Γ2 ρ2},
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    G i Γ1 ρ1 ρ2.
Proof.
  unfold G_top, G.
  intros.
  destruct H as [Hwf1 [Hwf2 [Href [Hs HG]]]].
  unfold Ensembles.Included, Ensembles.In, Dom_map in *.
  repeat (split; auto); intros.
  edestruct HG as [v1' [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto; invc.
  eexists; eexists; repeat (split; eauto).
  eapply V_V_top; eauto.
Qed.

Lemma G_G_top i Γ1 ρ1 Γ2 ρ2 :
  G i Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  G_top i Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G, G_top.
  intros.
  destruct H as [Hwf1 [Href HG]].
  repeat (split; auto); intros.
Abort.

(* Top-level Monotonicity Lemmas *)
Lemma V_top_mono i :
  forall {j v1 v2},
    V_top i v1 v2 ->
    j <= i ->
    V_top j v1 v2.
Proof.
  intros.
  eapply V_V_top; eauto.
  eapply V_top_exposed_r; eauto.
  eapply V_mono; eauto.
  eapply V_V_top; eauto.
  eapply V_top_exposed_r; eauto.
Qed.

Lemma V_top_mono_Forall {vs1 vs2} i j :
  Forall2 (V_top i) vs1 vs2 ->
  j <= i ->
  Forall2 (V_top j) vs1 vs2.
Proof.
  intros H.
  revert j.
  induction H; simpl; intros; auto.
  constructor; eauto.
  eapply V_top_mono; eauto.
Qed.

Lemma R_top_mono {r1 r2} i j :
  R_top i r1 r2 ->
  j <= i ->
  R_top j r1 r2.
Proof.
  unfold R.
  intros.
  destruct r1; auto.
  destruct r2; auto.
  eapply V_top_mono; eauto.
Qed.

Lemma E_top_mono {ρ1 ρ2 e1 e2} i j:
  E_top i ρ1 e1 ρ2 e2 ->
  j <= i ->
  E_top j ρ1 e1 ρ2 e2.
Proof.
  unfold E_top, E_top'.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; eauto.
  apply R_top_mono with (i - j1); try lia; auto.
Qed.

Lemma G_top_mono {Γ1 Γ2 ρ1 ρ2} i j:
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  j <= i ->
  G_top j Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G_top.
  intros.
  destruct H as [Hwf1 [Hwf2 [Href [HS HG]]]].
  repeat (split; eauto); intros.
  edestruct HG as [v1 [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto.
  eexists; eexists; repeat (split; eauto).
  apply V_top_mono with i; eauto.
Qed.

(* V_top and subval *)
Lemma V_top_subval_Forall :
  forall i,
    (forall m : nat,
        m < S i ->
        forall v1 v2 v3,
          subval v1 v2 ->
          V_top m v1 v3 <-> V_top m v2 v3) ->
    forall j vs1 vs2 vs3,
      j <= i ->
      Forall2 subval vs1 vs2 ->
      Forall2 (V_top j) vs1 vs3 <-> Forall2 (V_top j) vs2 vs3.
Proof.
  intros.
  revert vs3 j H0.
  induction H1; simpl; intros.
  - split; intros; inv H1; auto.
  - split; intros; inv H3; constructor; auto.
    eapply H with (v1 := x) (v2 := y); eauto; try lia.
    eapply IHForall2; eauto.
    eapply H with (v1 := x) (v2 := y); eauto; try lia.
    eapply IHForall2; eauto.
Qed.

Lemma V_top_subval :
  forall i v1 v2 v3,
    subval v1 v2 ->
    V_top i v1 v3 <-> V_top i v2 v3.
Proof.
  intro i.
  induction i using lt_wf_rec; intros v1 v2 v3 Hsub.
Admitted.

(* W is sound for *every* program trace of an open program e *)
Definition web_map_sound_top e e' :=
  forall i ρ1 ρ2 r1,
    bstep_fuel ρ1 e i r1 ->
    refine_env (occurs_free e) ρ1 ρ2 ->
    wf_env ρ1 ->
    wf_cenv ρ2 ->
    exists r2,
      cbstep_top_fuel ρ2 e' i r2 /\
        refine_res r1 r2.

Lemma web_map_sound_top_web_map_sound W e :
  web_map_sound_top e (CEexp W e) ->
  forall ρ1 ρ2,
    wf_env ρ1 ->
    wf_cenv ρ2 ->
    web_map_sound W (occurs_free e) true ρ1 ρ2 e.
Proof.
  unfold web_map_sound_top, web_map_sound.
  intros.
  edestruct H as [r2 [Hcbstep_top Href]]; eauto.
  eexists; split; eauto.
  eapply cbstep_top_fuel_cbstep_fuel; eauto.
Qed.

Lemma web_map_sound_web_map_sound_top W e :
  (forall ρ1 ρ2,
      wf_env ρ1 ->
      wf_cenv ρ2 ->
      web_map_sound W (occurs_free e) true ρ1 ρ2 e) ->
  web_map_sound_top e (CEexp W e).
Proof.
  unfold web_map_sound_top, web_map_sound.
  intros.
  edestruct H as [r2 [Hcbstep_top Href]]; eauto.
  eexists; split; eauto.
  eapply cbstep_fuel_cbstep_top_fuel; eauto.
Qed.

Definition trans_correct_top e e' :=
  (occurs_free_top e') \subset (occurs_free e) /\
  web_map_sound_top e e' /\
  forall i ρ1 ρ2,
    G_top i (occurs_free e) ρ1 (occurs_free_top e') ρ2 ->
    E_top i ρ1 e ρ2 e'.

Lemma trans_correct_top_subset e1 e2 :
  trans_correct_top e1 e2 ->
  occurs_free_top e2 \subset occurs_free e1.
Proof. unfold trans_correct_top. fcrush. Qed.

Lemma cexp_compat_top W e :
  web_map_spec W (occurs_free e) e ->
  web_map_sound_top e (CEexp W e) ->
  trans_correct_top e (CEexp W e).
Proof.
  unfold trans_correct_top.
  intros.
  split.
  eapply occurs_free_top_cexp; eauto.
  split; eauto; intros.
  eapply E_E_top; eauto.
  eapply fundamental_property; eauto.
  eapply web_map_sound_top_web_map_sound; eauto.
  eapply G_top_wf_env_l; eauto.
  eapply G_top_wf_cenv_r; eauto.
  eapply G_top_G; eauto.
Qed.

Theorem top W etop:
  (has_label etop \subset (Dom_map W)) ->
  web_map_sound_top etop (CEexp W etop) ->
  trans_correct_top etop (CEexp W etop).
Proof.
  intros H; intros.
  eauto using cexp_compat_top, web_map_total.
Qed.

(* Linking Preservation *)

(* well_annotated is strictly stronger than trans_correct_top, since G_top requires to_exposed *)
Lemma trans_correct_top_trans_correct W e :
  web_map_sound_top e (CEexp W e) ->
  trans_correct_top e (CEexp W e) ->
  well_annotated W (occurs_free e) e.
Proof.
Abort.

Lemma web_map_sound_top_preserves_linking f x e1 e1' e2 e2' :
  f <> x ->
  ~ (f \in occurs_free e1) ->
  ~ (f \in occurs_free e2) ->
  ~ (f \in occurs_free_top e1') ->
  ~ (f \in occurs_free_top e2') ->
  web_map_sound_top e1 e1' ->
  web_map_sound_top e2 e2' ->
  web_map_sound_top (link f x e1 e2) (clink x e1' e2').
Proof.
  intros Hfx Hf1 Hf2 Hf1' Hf2' H1 H2.
  unfold link, link.
  unfold web_map_sound_top in *.
  intros i ρ1 ρ2 r1 Hbstep Href Hwfρ1 Hwfρ2.
  inv Hbstep.
  { exists COOT; split; eauto. }
  match goal with
  | [ H : bstep _ _ _ _ |- _ ] => inv H
  end.
  match goal with
  | [ H : bstep_fuel _ (Eletapp _ _ _ _ _) _ _ |- _ ] => inv H
  end.
  { (* trivially-OOT Eletapp: source fuel = 1 *)
    exists COOT; split; [|constructor].
    apply CbstepTF_Step; [apply Cbstep_link_top_trivial | constructor]. }
  match goal with
  | [ H : bstep _ (Eletapp _ _ _ _ _) _ _ |- _ ] => inv H
  end;
    match goal with
    | [ H : M.get _ (M.set _ _ _) = Some _ |- _ ] =>
        rewrite M.gss in H; inv H
    end;
    match goal with
    | [ H : get_list [] _ = Some _ |- _ ] => simpl in H; inv H
    end;
    match goal with
    | [ H : set_lists [] [] _ = Some _ |- _ ] => simpl in H; inv H
    end.
  - (* BStep_letapp_Res *)
    match goal with
    | [ Hb : bstep_fuel _ _ _ (Res _) |- _ ] => rename Hb into Hbody
    end.
    match goal with
    | [ Hk : bstep_fuel _ e2 _ _ |- _ ] => rename Hk into Hcont
    end.
    rename f' into f.
    rename ρ' into ρ1.
    rename e into e1.

    edestruct (bstep_fuel_drop_unused Hf1 Hwfρ1 Hbody) as [r1' [Hbstep_e1 Hsub']]; eauto.
    inv Hsub'.

    edestruct H1 as [r2 [Hcbstep_e1' Href']]; eauto.
    eapply refine_env_subset; eauto.
    {
      unfold Ensembles.Included, Ensembles.In in *.
      fcrush.
    }
    inv Href'.

    rewrite (set_set x f) in Hcont; auto.

    assert (Hwfv : wf_res (Res v)).
    {
      eapply bstep_fuel_wf_res; eauto.
    }

    assert (Hwf2 : wf_env (M.set x v ρ1)).
    {
      eapply wf_env_set; eauto.
      inv Hwfv; auto.
    }

    edestruct (bstep_fuel_drop_unused Hf2 Hwf2 Hcont) as [r2' [Hbstep_e2 Hsub2']]; eauto.

    assert (Hsub3 : subenv (x |: occurs_free e2) (M.set x v ρ1) (M.set x v2 ρ1)).
    {
      eapply subenv_set; eauto.
      eapply subenv_refl; eauto.
    }

    edestruct @bstep_fuel_subenv with (Γ := (x |: occurs_free e2)) as [r2'' [Hbstep_e2' Hsub2'']]; eauto.
    fcrush.

    edestruct (H2 c' (M.set x v2 ρ1) (M.set x v' ρ2)) as [r2''' [Hcbstep_e2' Href'']]; eauto.
    eapply refine_env_subset; eauto.
    eapply refine_env_set; eauto.
    {
      unfold Ensembles.Included, Ensembles.In in *.
      intros.
      destruct (M.elt_eq x x0); subst.
      - fcrush.
      - apply Union_intror.
        fcrush.
    }
    eapply wf_env_set; eauto.
    assert (Hwfv2 : wf_res (Res v2)).
    {
      eapply (bstep_fuel_wf_res ρ1); eauto.
    }
    inv Hwfv2; auto.
    eapply wf_cenv_set; eauto.

    assert (Hwfv' : wf_cres (CRes v')).
    {
      eapply cbstep_top_fuel_wf_res; eauto.
    }
    inv Hwfv'; auto.

    exists r2'''; split; eauto.
    econstructor; eauto.
    inv Hcbstep_e2'; auto.

    assert (Hsubres : subres r1 r2'') by eauto using subres_trans.
    (* need a lemma for refine_res and subres *)
    admit.
Admitted.

Lemma preserves_linking f x e1 e1' e2 e2' :
  f <> x ->
  ~ (f \in occurs_free e1) ->
  ~ (f \in occurs_free e2) ->
  ~ (f \in occurs_free_top e1') ->
  ~ (f \in occurs_free_top e2') ->
  trans_correct_top e1 e1' ->
  trans_correct_top e2 e2' ->
  trans_correct_top (link f x e1 e2) (link x e1' e2').
Proof.
  intros Hfx Hf1 Hf2 Hf1' Hf2' Htr1 Htr2.
  destruct Htr1 as [HFV1 [Hsnd1 HE1]].
  destruct Htr2 as [HFV2 [Hsnd2 HE2]].
  unfold trans_correct_top.
  repeat split.

  - (* FV inclusion: occurs_free_top (link x e1' e2') ⊆ occurs_free (link f x e1 e2) *)
    unfold link, link.
    unfold Ensembles.Included, Ensembles.In.
    intros z Hz.
    inv Hz.
    + (* Free_clink1: z ∈ FV(e1'); need z ∈ FV(Efun f l0 [] e1 _) via Free_fun2 *)
      assert (Hne : z <> f) by (intros ?; subst; apply Hf1'; auto).
      apply Free_fun2.
      * auto.
      * intros Hin; inv Hin.
      * apply HFV1; auto.
    + (* Free_clink2: z ≠ x ∧ z ∈ FV(e2'); need z ∈ FV(Efun ...) via Free_fun1 + Free_letapp1 *)
      assert (Hne : z <> f) by (intros ?; subst; apply Hf2'; auto).
      apply Free_fun1.
      * auto.
      * apply Free_letapp1; auto.
        apply HFV2; auto.

  - eapply web_map_sound_top_preserves_linking; eauto.

  - intros i ρ1 ρ2 HG.
    unfold link, link, E_top, E_top' in *.
    intros.
    inv H0.
    fcrush.
    inv H1.
    inv H8.
    fcrush.
    inv H0.
    2 : { fcrush. }
    rewrite M.gss in *; invc.
    rename f' into f.
    rename ρ' into ρ1.

    assert (Hwf1 : wf_env ρ1) by admit.

    edestruct (bstep_fuel_drop_unused Hf1 Hwf1 H11) as [r1' [Hbstep_e1 Hsub']]; eauto.
    inv Hsub'.

    edestruct (HE1 i ρ1 ρ2) with (j1 := c) as [j1 [r1' [Hcbstep_e1' HR1']]]; eauto; try lia.
    eapply G_top_subset; eauto.
    {
      unfold Ensembles.Included, Ensembles.In in *.
      fcrush.
    }

    edestruct R_top_res_inv_l as [v2' [Heqv2' HV]]; eauto; subst.

    rewrite (set_set x f) in H12; auto.

    assert (Hwfv : wf_res (Res v)) by eauto using bstep_fuel_wf_res; eauto.

    assert (Hwf2 : wf_env (M.set x v ρ1)).
    {
      eapply wf_env_set; eauto.
      inv Hwfv; auto.
    }

    edestruct (bstep_fuel_drop_unused Hf2 Hwf2 H12) as [r2' [Hbstep_e2 Hsub']]; eauto.

    assert (Hsub3 : subenv (x |: occurs_free e2) (M.set x v ρ1) (M.set x v2 ρ1)).
    {
      eapply subenv_set; eauto.
      eapply subenv_refl; eauto.
    }

    edestruct @bstep_fuel_subenv with (Γ := (x |: occurs_free e2)) as [r2'' [Hbstep_e2' Hsub2'']]; eauto.
    fcrush.

    edestruct (HE2 (i - c) (M.set x v2 ρ1) (M.set x v2' ρ2)) with (j1 := c') as [j2'' [r2''' [Hcbstep_e2' Href'']]]; eauto; try lia.
    eapply G_top_subset; eauto.
    eapply G_top_set; eauto.
    eapply G_top_mono; eauto; lia.

    {
      unfold Ensembles.Included, Ensembles.In in *.
      intros.
      destruct (M.elt_eq x x0); subst.
      - fcrush.
      - apply Union_intror.
        unfold Ensembles.In.
        fcrush.
    }

    exists (S (S (j1 + j2''))), r2'''; split; eauto.
    econstructor; eauto.
    eapply cbstep_top_fuel_exposed_inv; eauto.

    assert (Hsubres : subres r1 r2'') by eauto using subres_trans.

    (* need a lemma for V_top and subval *)
    (* eapply R_top_mono; eauto. *)

    admit.
Admitted.

From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From SemAnnotate Require Import LabeledANF ValueSetAnalysis.
From LambdaWeb Require Import Base.

Module An := ValueSetAnalysis.

(* Simple Web Assignment With Only Two Webs *)

(* Sound web assignment guarantees the exposed constraints in LambdaWeb *)

Definition web_map := M.t web.

Parameter w_int : web.
Parameter w_int_internal : ~ (w_int \in Exposed).

Parameter w_ext : web.
Parameter w_ext_exposed : forall w, w \in Exposed <-> w = w_ext.

Definition web_map_assign (W : web_map) :=
  forall l w,
    M.get l W = Some w ->
    w = w_int \/ w = w_ext.

(* Exposed Labels *)
(* `aexposed A` over-approximates the labels that LambdaWeb forces to be exposed:
   - the unknown sides, and everything that escapes to the context;
   - closed under interactions in both directions, since an introduction and
     its elimination must share a web;
   - closed under flow through exposed closures, since the arguments and the
     results of an exposed closure must be exposed. *)
Inductive aexposed (A : An.analysis_result) : labels :=
| AExp_top_intro :
  aexposed A An.l_top_intro

| AExp_top_elim :
  aexposed A An.l_top_elim

| AExp_esc :
  forall av,
    (av \in An.ai_esc A) ->
    aexposed A (An.label_of av)

| AExp_int_l :
  forall l1 l2,
    ((l1, l2) \in An.ai_int A) ->
    aexposed A l1 ->
    aexposed A l2

| AExp_int_r :
  forall l1 l2,
    ((l1, l2) \in An.ai_int A) ->
    aexposed A l2 ->
    aexposed A l1

| AExp_param :
  forall l f xs e x av,
    (An.AVfun l f xs e \in An.ai_env A f) ->
    aexposed A l ->
    List.In x xs ->
    (av \in An.ai_env A x) ->
    aexposed A (An.label_of av)

| AExp_ret :
  forall l av,
    aexposed A l ->
    (av \in An.ai_ret A l) ->
    aexposed A (An.label_of av).

Hint Constructors aexposed : core.

(* Exposed webs are consistent with `aexposed` *)
Definition web_map_exposed (W : web_map) (A : An.analysis_result) : Prop :=
  forall l w,
    M.get l W = Some w ->
    (w = w_ext <-> l \in aexposed A).

(* every label in `avs` is exposed *)
Definition aexposed_avals A avs := forall av, (av \in avs) -> (An.label_of av \in aexposed A).

(* Web Map Context *)
Definition web_map_context := An.color -> web_map.

(* *Static* Web Map Invariants *)
Definition valid_web_map_context (ω : web_map_context) (θ : An.analysis_context) : Prop :=
  forall (c : An.color) , web_map_assign (ω c) /\ web_map_exposed (ω c) (θ c).

(* The two ends of a predicted interaction share a web:
   `aexposed` is closed under interactions in both directions, and there are only two webs. *)
Lemma web_map_interact_eq {W A l1 l2 w1 w2} :
  web_map_assign W ->
  web_map_exposed W A ->
  ((l1, l2) \in An.ai_int A) ->
  W ! l1 = Some w1 ->
  W ! l2 = Some w2 ->
  w1 = w2.
Proof.
  intros Hassign Hexp Hint Hw1 Hw2.
  destruct (Hassign _ _ Hw1) as [-> | ->];
    destruct (Hassign _ _ Hw2) as [-> | ->]; auto; exfalso;
    apply w_int_internal; apply w_ext_exposed.
  - (* l2 is exposed, hence so is l1 *)
    apply (Hexp _ _ Hw1).
    eapply AExp_int_r; [exact Hint |].
    apply (Hexp _ _ Hw2); reflexivity.
  - (* l1 is exposed, hence so is l2 *)
    apply (Hexp _ _ Hw2).
    eapply AExp_int_l; [exact Hint |].
    apply (Hexp _ _ Hw1); reflexivity.
Qed.

(* Tagged Value *)
Inductive ctag A : Type :=
| CTAG : label -> web_map -> A -> ctag A.

Hint Constructors ctag : core.

(* Value *)
Inductive cval : Type :=
| CVfun : var -> M.t (ctag cval) -> list var -> exp -> cval
| CVconstr : ctor_tag -> list (ctag cval) -> cval.

Hint Constructors cval : core.

Definition clval := ctag cval.

(* TODO: swap l and W *)
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

(* Checking Semantics With Respect To Web Map, `W` *)
(* `W` is a valid web assignment mapping with respect to the checking big-step semantics *)
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

Lemma cbstep_fuel_to_exposed_cres W ρ e k r :
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

(* Cross-semantics Logical Relations *)
Section LRBase.

  Variable θ : analysis_context.
  Hypothesis θ_escape_ok : analysis_context_escape_ok θ.

  (* Web map of each unit, consistent with its analysis result *)
  Variable ω : web_map_context.
  Hypothesis ω_valid : valid_web_map_context ω θ.

  Definition R'(P : nat -> An.clval -> clval -> Prop) (i : nat) (r1 : An.cres) (r2 : cres) :=
    match r1, r2 with
    | An.COOT, COOT => True
    | An.CRes v1, CRes v2 => P i v1 v2
    | _, _ => False
    end.

  Definition E' (P : nat -> An.clval -> clval -> Prop) (A : An.analysis_result) (c : An.color) (bdr : bool) (Rs : An.avals) (W : web_map) (ex : bool) (i : nat) (ρ1 : An.cenv) (ρ2 : cenv) (e : exp) : Prop :=
    forall j1 r1 I1,
      j1 <= i ->
      An.cbstep_fuel A c bdr ρ1 e j1 Rs r1 I1 ->
      exists j2 r2,
        cbstep_fuel W ex ρ2 e j2 r2 /\
        R' P (i - j1) r1 r2.

  Fixpoint V (i : nat) (cv1 : An.clval) (cv2 : clval) {struct i} : Prop :=
    An.wf_cval θ cv1 /\
    wf_cval cv2 /\
    match cv1, cv2 with
    | An.CTAG _ A1 (c1, l1) v1, CTAG _ l2 W2 v2 =>
        l1 = l2 /\
        (* the web map is the one of the defining unit *)
        W2 = ω c1 /\
        exists w2, W2 ! l2 = Some w2 /\
        match v1, v2 with
          (*
        | Vconstr c1 vs1, CVconstr c2 vs2 =>
            c1 = c2 /\
              length vs1 = length vs2 /\
              match i with
              | 0 => True
              | S i0 => Forall2 (V i0) vs1 vs2
              end
           *)

        | An.CVfun f1 ρ1 xs1 e1, CVfun f2 ρ2 xs2 e2 =>
            f1 = f2 /\ xs1 = xs2 /\ e1 = e2 /\

              (* every label of the body is assigned a web *)
              (has_label e1 \subset Dom_map W2) /\

              (* We need to carry over the following invariants to show `aexposed` *)
              (* the closure is recorded at its defining unit *)
              (An.AVfun l1 f1 xs1 e1 \in An.ai_env A1 f1) /\
              (* the source closure environment invariants *)
              An.cescaped_env c1 (An.fun_fv f1 xs1 e1) ρ1 /\
              An.cbinding_env c1 A1 (An.fun_fv f1 xs1 e1) ρ1 /\

              match i with
              | 0 => True
              | S i0 =>
                  forall (bdr : bool) j c vs1 vs2 ρ3 ρ4,
                    j <= i0 ->
                    Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                    set_lists xs1 vs1 (M.set f1 (An.CTag A1 c1 l1 (An.CVfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                    set_lists xs2 vs2 (M.set f2 (CTag l2 W2 (CVfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->

                    (* invariants for escaped values and variable bindings *)
                    Forall (An.cescaped c1) vs1 ->
                    Forall2 (An.cbinding c1 A1) xs1 vs1 ->

                    (* foreign call: the closure has escaped its unit *)
                    (c1 <> c -> AVfun l2 f2 xs2 e2 \in ai_esc A1) ->

                    (* exposed closure: the arguments are exposed *)
                    (w2 \in Exposed -> Forall to_exposed vs2) ->

                    (* closures that may cross the program boundary *)
                    (if bdr then An.AVfun l1 f1 xs1 e1 \in An.ai_esc A1 else True) ->

                    E' V A1 c1 bdr (An.ai_ret A1 l1) W2 (exposedb w2) (i0 - (i0 - j)) ρ3 ρ4 e1
              end

        | _, _ => False
        end
    end.

  Definition R := (R' V).

  Definition E := (E' V).

  (* Lemmas about [wf_cval], [wf_cres], and [wf_cenv] *)
  Lemma V_wf_cval_l {i v1 v2}:
    V i v1 v2 ->
    An.wf_cval θ v1.
  Proof. intros; destruct i; simpl in *; fcrush. Qed.

  Lemma V_wf_cval_Forall_l {i vs1 vs2} :
    Forall2 (V i) vs1 vs2 ->
    Forall (An.wf_cval θ) vs1.
  Proof. intros H. induction H; eauto using V_wf_cval_l. Qed.

  Lemma V_wf_cres_l {i v1 v2}:
    V i v1 v2 ->
    An.wf_cres θ (An.CRes v1).
  Proof. intros; eauto using V_wf_cval_l; eauto. Qed.

  Lemma R_wf_cres_l {i r1 r2} :
    R i r1 r2 ->
    An.wf_cres θ r1.
  Proof.
    unfold R.
    intros.
    destruct r1; destruct r2; try contradiction;
      eauto using V_wf_cval_l.
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

  (* Inversion Lemmas *)
  Lemma R_res_inv_l i v1 r2 :
    R i (An.CRes v1) r2 ->
    exists v2, r2 = CRes v2 /\ V i v1 v2.
  Proof. intros. fcrush. Qed.

  Lemma R_res_inv_l_V v1 r2 :
    (forall k, R k (An.CRes v1) r2) ->
    exists v2, r2 = CRes v2 /\ (forall k, V k v1 v2).
  Proof. intros. hauto. Qed.

  (* Environment Relation *)
  Definition G c i Γ1 ρ1 ρ2 :=
    An.wf_cenv θ ρ1 /\
      wf_cenv ρ2 /\
      An.cescaped_env c Γ1 ρ1 /\
      An.cbinding_env c (θ c) Γ1 ρ1 /\
      forall x,
        (x \in Γ1) ->
        exists v1 v2,
          M.get x ρ1 = Some v1 /\
            M.get x ρ2 = Some v2 /\
            V i v1 v2.

  (* Environment Lemmas *)
  Lemma G_subset Γ1 Γ2 {c i ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    Γ2 \subset Γ1 ->
    G c i Γ2 ρ1 ρ2.
  Proof.
    unfold G.
    intros [Hwf1 [Hwf2 [Hesc [Hbind HG]]]] Hsub.
    split; [exact Hwf1 | split; [exact Hwf2 | split; [| split]]].
    - eapply An.cescaped_env_subset; eauto.
    - eapply An.cbinding_env_subset; eauto.
    - intros x Hx; apply HG; apply Hsub; exact Hx.
  Qed.

  Lemma G_wf_cenv_l {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    An.wf_cenv θ ρ1.
  Proof. unfold G. fcrush. Qed.

  Lemma G_wf_cenv_r {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    wf_cenv ρ2.
  Proof. unfold G. fcrush. Qed.

  Lemma G_cescaped_env {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    An.cescaped_env c Γ1 ρ1.
  Proof. unfold G. intros [_ [_ [Hesc _]]]. exact Hesc. Qed.

  Lemma G_cbinding_env {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    An.cbinding_env c (θ c) Γ1 ρ1.
  Proof. unfold G. intros [_ [_ [_ [Hbind _]]]]. exact Hbind. Qed.

  Lemma G_get {c Γ1 i ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    forall x v1,
      (x \in Γ1) ->
      M.get x ρ1 = Some v1 ->
      exists v2,
        M.get x ρ2 = Some v2 /\
          V i v1 v2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hwf [Href [Hesc [Hex HG]]]].
    edestruct HG as [v1' [v2 [Heqv1 [Heqv2 HV]]]]; eauto; invc.
    fcrush.
  Qed.

  Lemma G_get_list {c i Γ1 ρ1 ρ2} :
    G c i Γ1 ρ1 ρ2 ->
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

  Lemma G_set {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    forall {x v1 v2},
      V i v1 v2 ->
      An.cescaped c v1 ->
      An.cbinding c (θ c) x v1 ->
      G c i (x |: Γ1) (M.set x v1 ρ1) (M.set x v2 ρ2).
  Proof.
    unfold G.
    intro HG.
    pose proof HG as HG'.
    intros.

    destruct HG as [Hwf [Href [Hesc [Hex HG]]]].
    split.
    eapply An.wf_cenv_set; eauto.
    eapply V_wf_cval_l; eauto.

    split.
    eapply wf_cenv_set; eauto.
    eapply V_wf_cval_r; eauto.

    split.
    eapply An.cescaped_env_set; eauto.

    split.
    eapply An.cbinding_env_set; eauto.

    intros.
    destruct (M.elt_eq x0 x); subst.
    - repeat rewrite M.gss in *.
      fcrush.
    - repeat (rewrite M.gso in *; auto).
      fcrush.
  Qed.

  Lemma G_set_lists {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    forall {xs vs1 vs2 ρ3 ρ4},
      Forall2 (V i) vs1 vs2 ->
      Forall (An.cescaped c) vs1 ->
      Forall2 (An.cbinding c (θ c)) xs vs1 ->
      set_lists xs vs1 ρ1 = Some ρ3 ->
      set_lists xs vs2 ρ2 = Some ρ4 ->
      G c i (FromList xs :|: Γ1) ρ3 ρ4.
  Proof.
    intros HG xs.
    induction xs; simpl; intros.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      invc.
      eapply G_subset; eauto; normalize_sets;
        rewrite Union_Empty_set_neut_l; eauto;
        apply Included_refl.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
      destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
      invc.
      inv H; inv H0; inv H1.
      eapply G_subset with (Γ1 := (a |: (FromList xs :|: Γ1))); eauto;
        try (normalize_sets;
             rewrite Union_assoc;
             apply Included_refl).
      eapply G_set; eauto.
  Qed.

  (* Monotonicity Lemmas *)
  Lemma V_mono_Forall_aux :
    forall i j (V : nat -> An.clval -> clval -> Prop) vs1 vs2,
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
      destruct H0 as [Hwf1 [Hwf2 HV]];
      rename w into W;
      destruct c; destruct HV as [Heql [HwqW [w2 [Heqw2 HV]]]]; subst.
    - destruct c0; destruct c1; try contradiction.
      sfirstorder.
    - fcrush.
(*    - repeat (split; auto).
      destruct v; destruct c0; try contradiction.
      + fcrush.
      + fcrush. *)
    - repeat (split; auto).
      eexists; split; eauto.
      destruct c0; destruct c1; try contradiction.
      sfirstorder.
    - repeat (split; auto).
      eexists; split; eauto.
      destruct c0; destruct c1; try contradiction.
      destruct HV as [Heqv [Heql [Heqe [Hsub [Hsite [Hesc [Hloc HV]]]]]]]; subst.
      repeat (split; eauto); intros.
      specialize (HV bdr j0 c0 vs1 vs2 ρ3 ρ4).
      rewrite normalize_step in *; try lia.
      eapply HV; eauto; try lia.
      (* + destruct HV as [Heqc [Hlen HV]]; subst.
        eexists; repeat (split; eauto).
        eapply V_mono_Forall_aux; eauto; lia. *)
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

  Lemma E_mono {A Rs c bdr W ex ρ1 ρ2 e} i j:
    E A c bdr Rs W ex i ρ1 ρ2 e ->
    j <= i ->
    E A c bdr Rs W ex j ρ1 ρ2 e.
  Proof.
    unfold E, R, E', R'.
    intros.
    destruct (H j1 r1 I1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
    exists j2, r2; split; eauto.
    apply R_mono with (i - j1); try lia; auto.
  Qed.

  Lemma G_mono {c Γ1 ρ1 ρ2} i j:
    G c i Γ1 ρ1 ρ2 ->
    j <= i ->
    G c j Γ1 ρ1 ρ2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hwf1 [Hwf2 [Hesc [Hex HG]]]].
    repeat (split; auto); intros.
    edestruct HG as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto; invc.
    eexists; repeat (split; eauto).
    eauto using V_mono.
  Qed.

  (* Exposed Lemmas *)

  (* A related value whose label is exposed in its own unit is exposed. *)
  Lemma V_exposed_label {i A1 c1 l1 cv1 v2} :
    V i (An.CTAG _ A1 (c1, l1) cv1) v2 ->
    (l1 \in aexposed A1) ->
    to_exposed v2.
  Proof.
    intros HV Hl.
    pose proof (An.wf_cval_CTag_inv (V_wf_cval_l HV)) as [Hθ _].
    destruct (ω_valid c1) as [_ Hexp].
    unfold web_map_exposed in *.
    destruct v2 as [l2 W2 cv2].
    destruct i; cbn in HV;
      destruct HV as (_ & _ & Heql & HeqW & w2 & Hw2 & Hcase);
      subst l2 W2;
      destruct cv1, cv2; try contradiction;
      (eapply ToExp_cfun; [exact Hw2 |]);
      apply w_ext_exposed;
      apply (Hexp _ _ Hw2);
      rewrite Hθ; exact Hl.
  Qed.

  (* A value held by the unit wearing `c` that flows into `avs` is exposed,
     provided every label in `avs` is exposed:
     - a foreign value has escaped from its own unit;
     - an own closure is either recorded in `avs`, or has escaped. *)
  Lemma V_exposed {c avs i v1 v2} :
    V i v1 v2 ->
    An.cescaped c v1 ->
    An.cflows c (θ c) avs v1 ->
    aexposed_avals (θ c) avs ->
    to_exposed v2.
  Proof.
    intros HV Hesc Hfl Havs.
    destruct v1 as [A1 [c1 l1] cv1].
    pose proof (An.wf_cval_CTag_inv (V_wf_cval_l HV)) as [Hθ _].
    destruct cv1 as [f ρ xs e | t vs].
    - eapply V_exposed_label; [exact HV |].
      cbn in Hesc, Hfl.
      destruct (Nat.eq_dec c1 c) as [-> | Hneq].
      + destruct (proj1 Hfl eq_refl) as [Hin | [Hin _]];
          rewrite <- Hθ.
        * exact (Havs _ Hin).
        * exact (AExp_esc _ _ Hin).
      + exact (AExp_esc _ _ (Hesc Hneq)).
    - exfalso.
      destruct v2 as [l2 W2 cv2].
      destruct i, cv2; cbn in HV;
        destruct HV as (_ & _ & _ & _ & ? & _ & []).
  Qed.

  (* A value escaping from the unit wearing `c` to the one wearing `c'` is exposed. *)
  Lemma V_exposed_escaped {c c' i v1 v2} :
    c <> c' ->
    V i v1 v2 ->
    An.cescaped c v1 ->
    An.cescaped c' v1 ->
    to_exposed v2.
  Proof.
    intros Hcc' HV Hesc Hesc'.
    destruct v1 as [A1 [c1 l1] cv1].
    destruct cv1 as [f ρ xs e | t vs].
    - eapply V_exposed_label; [exact HV |].
      cbn in Hesc, Hesc'.
      destruct (Nat.eq_dec c1 c) as [-> | Hneq].
      + exact (AExp_esc _ _ (Hesc' Hcc')).
      + exact (AExp_esc _ _ (Hesc Hneq)).
    - exfalso.
      destruct v2 as [l2 W2 cv2].
      destruct i, cv2; cbn in HV;
        destruct HV as (_ & _ & _ & _ & ? & _ & []).
  Qed.

  (* Results returned into an exposed return set are exposed. *)
  Lemma R_exposed {c Rs i r1 r2} :
    R i r1 r2 ->
    An.cresult c (θ c) Rs r1 ->
    aexposed_avals (θ c) Rs ->
    to_exposed_cres r2.
  Proof.
    unfold R, R'.
    intros HR Hres HRs.
    destruct r1 as [| v1], r2 as [| v2]; cbn in HR; try contradiction; constructor.
    destruct Hres as [Hesc Hfl].
    exact (V_exposed HR Hesc Hfl HRs).
  Qed.

  (* Arguments bound to exposed parameters are exposed (e.g. internal calls to
     exposed closures, where the hypothesis on `xs` follows from `AExp_param`). *)
  Lemma V_exposed_Forall_cbinding {c i xs vs1 vs2} :
    Forall2 (V i) vs1 vs2 ->
    Forall (An.cescaped c) vs1 ->
    Forall2 (An.cbinding c (θ c)) xs vs1 ->
    (forall x, List.In x xs -> aexposed_avals (θ c) (An.ai_env (θ c) x)) ->
    Forall to_exposed vs2.
  Proof.
    intros HV.
    revert xs.
    induction HV as [| v1 v2 vs1 vs2 Hv HV IH]; intros xs Hesc Hb Hxs.
    - constructor.
    - inv Hesc; inv Hb.
      constructor.
      + eapply V_exposed;
          [exact Hv | eassumption | eapply An.cbinding_cflows; eassumption |].
        unfold aexposed_avals.
        intros av Hav.
        eapply Hxs; [left; reflexivity | exact Hav].
      + eapply IH; [eassumption | eassumption |].
        unfold aexposed_avals.
        intros x' Hin av Hav.
        eapply Hxs; [right; exact Hin | exact Hav].
  Qed.

  (* Arguments of a foreign call are exposed. *)
  Lemma V_exposed_Forall_escaped {c c' i vs1 vs2} :
    c <> c' ->
    Forall2 (V i) vs1 vs2 ->
    Forall (An.cescaped c) vs1 ->
    Forall (An.cescaped c') vs1 ->
    Forall to_exposed vs2.
  Proof.
    intros Hcc' HV.
    induction HV as [| v1 v2 vs1 vs2 Hv HV IH]; intros Hesc Hesc'.
    - constructor.
    - inv Hesc; inv Hesc'.
      constructor; eauto using V_exposed_escaped.
  Qed.

End LRBase.

(* Scoped web_map *)
(* This essentially combines `well_scoped e` and `has_label e ⊆ Dom_map W`, to aid induction *)
Inductive web_map_well_scoped (W : web_map) (Γ : vars) : exp -> Prop :=
| Web_Map_Well_Scoped_ret :
  forall x,
    (x \in Γ) ->
    web_map_well_scoped W Γ (Eret x)

| Web_Map_Well_Scoped_fun :
  forall {f l w xs e k},
    W ! l = Some w ->
    web_map_well_scoped W (FromList xs :|: (f |: Γ)) e ->
    web_map_well_scoped W (f |: Γ) k ->
    web_map_well_scoped W Γ (Efun f l xs e k)

| Web_Map_Well_Scoped_app :
  forall {f l w xs},
    W ! l = Some w ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    web_map_well_scoped W Γ (Eapp f l xs)

| Web_Map_Well_Scoped_letapp :
  forall {x f l w xs k},
    W ! l = Some w ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    web_map_well_scoped W (x |: Γ) k ->
    web_map_well_scoped W Γ (Eletapp x f l xs k)

| Web_Map_Well_Scoped_constr :
  forall {x l w t xs k},
    W ! l = Some w ->
    (FromList xs \subset Γ) ->
    web_map_well_scoped W (x |: Γ) k ->
    web_map_well_scoped W Γ (Econstr x l t xs k)

| Web_Map_Well_Scoped_proj :
  forall {l w x y k n},
    W ! l = Some w ->
    (y \in Γ) ->
    web_map_well_scoped W (x |: Γ) k ->
    web_map_well_scoped W Γ (Eproj x l n y k)

| Web_Map_Well_Scoped_case_nil :
  forall {l w x},
    W ! l = Some w ->
    (x \in Γ) ->
    web_map_well_scoped W Γ (Ecase x l [])

| Web_Map_Well_Scoped_case_cons :
  forall {x l w e t cl},
    W ! l = Some w ->
    (x \in Γ) ->
    web_map_well_scoped W Γ e ->
    web_map_well_scoped W Γ (Ecase x l cl) ->
    web_map_well_scoped W Γ (Ecase x l ((t, e) :: cl)).

Hint Constructors web_map_well_scoped : core.

Lemma web_map_well_scoped_inv W Γ e:
  web_map_well_scoped W Γ e <->
  (has_label e \subset Dom_map W) /\ well_scoped Γ e.
Proof.
  split.
  - intros H; split.
    + induction H; intros l' Hl; inv Hl;
        try (eexists; eassumption);
        first [ eapply IHweb_map_well_scoped; eassumption
              | eapply IHweb_map_well_scoped1; eassumption
              | eapply IHweb_map_well_scoped2; eassumption ].
    + induction H; constructor; auto.
  - intros [Hl Hs].
    revert Hl.
    induction Hs; intros Hl.
    + constructor; auto.
    + destruct (Hl l (Lab_fun1 _ _ _ _ _)) as [w Hw].
      econstructor; [exact Hw | apply IHHs1 | apply IHHs2];
        intros l' Hl'; apply Hl; eauto.
    + destruct (Hl l (Lab_app1 _ _ _)) as [w Hw].
      econstructor; eauto.
    + destruct (Hl l (Lab_letapp1 _ _ _ _ _)) as [w Hw].
      econstructor; eauto.
      apply IHHs; intros l' Hl'; apply Hl; eauto.
    + destruct (Hl l (Lab_constr1 _ _ _ _ _)) as [w Hw].
      econstructor; eauto.
      apply IHHs; intros l' Hl'; apply Hl; eauto.
    + destruct (Hl l (Lab_proj1 _ _ _ _ _)) as [w Hw].
      econstructor; eauto.
      apply IHHs; intros l' Hl'; apply Hl; eauto.
    + destruct (Hl l (Lab_case1 _ _ _)) as [w Hw].
      econstructor; eauto.
    + destruct (Hl l (Lab_case1 _ _ _)) as [w Hw].
      econstructor; eauto.
      * apply IHHs1; intros l' Hl'; apply Hl; eauto.
      * apply IHHs2; intros l' Hl'; apply Hl; eauto.
Qed.

Lemma web_map_well_scoped_intro W Γ e :
  has_label e \subset Dom_map W ->
  occurs_free e \subset Γ ->
  web_map_well_scoped W Γ e.
Proof.
  intros Hlabel Hfree.
  apply web_map_well_scoped_inv.
  split; [exact Hlabel | apply well_scoped_intro; exact Hfree].
Qed.

Section Compat.

  (* Compatibility Lemmas *)

  (* `Rs` is quantified inside as function bodies are checked against other return sets. *)
  Definition well_annotated A c W Γ e : Prop :=
    forall θ (bdr : bool) Rs ω (ex : bool),
      θ c = A ->
      An.analysis_context_escape_ok θ ->
      (if bdr then (Rs \subset (An.ai_esc A)) else True) ->

      valid_web_map_context ω θ ->
      ω c = W ->

      (* an exposed body returns only exposed values *)
      (if ex then aexposed_avals A Rs else True) ->

      forall i ρ1 ρ2,
        G θ ω c i Γ ρ1 ρ2 -> (* note θ is constrained by the environment as well *)
        E θ ω A c bdr Rs W ex i ρ1 ρ2 e.

  Lemma ret_compat A c W Γ x :
    (x \in Γ) ->
    well_annotated A c W Γ (Eret x).
  Proof.
    unfold well_annotated, E, E', R, R', Ensembles.Included, Ensembles.In.
    intros Hx θ bdr Rs ω ex Heqθ Hescθ Hesc HW Hex; intros.

    inv H2.
    - fcrush.
    - destruct r1.
      fcrush.
      inv H3.
      edestruct (G_get _ _ H0) as [v2 [Heqv2 HV]]; eauto.
      assert (Hwf : wf_cval v2).
      {
        eapply wf_cenv_get; eauto.
        eapply G_wf_cenv_r; eauto.
      }
      rename c0 into v1.

      exists 1, (CRes v2); split; eauto; simpl.
      + econstructor; eauto.
        * destruct ex; auto.
          constructor; auto.
          unfold An.cresult in *.
          eapply V_exposed; fcrush.
      + eapply V_mono; eauto; lia.
  Qed.

  Lemma Vfun_V θ ω W w Γ f l A c xs e  :
    occurs_free e \subset FromList xs :|: (f |: Γ) ->
    has_label e \subset Dom_map W ->
    θ c = A ->
    analysis_context_escape_ok θ ->
    ω c = W ->
    valid_web_map_context ω θ ->
    W ! l = Some w ->
    well_annotated A c W (FromList xs :|: (f |: Γ)) e ->
    forall {i ρ1 ρ2},
      An.wf_cval θ (An.CTag A c l (An.CVfun f ρ1 xs e)) ->
      wf_cval (CTag l W (CVfun f ρ2 xs e)) ->
      (An.AVfun l f xs e) \in (ai_env A f) ->
      G θ ω c i Γ ρ1 ρ2 ->
      V θ ω i (An.CTag A c l (An.CVfun f ρ1 xs e)) (CTag l W (CVfun f ρ2 xs e)).
  Proof.
    unfold well_annotated.
    intros HS HL Hθ Hesc Hω Hweb Hw He i.
    induction i; simpl; subst; intros; auto;
      (* the closure environment invariants, at the free variables of the closure *)
      assert (Hesc_env : An.cescaped_env c (An.fun_fv f xs e) ρ1)
        by (eapply An.cescaped_env_subset;
            [eapply G_cescaped_env; eauto | eapply An.fun_fv_subset; eauto]);
      assert (Hloc_env : An.cbinding_env c (θ c) (An.fun_fv f xs e) ρ1)
        by (eapply An.cbinding_env_subset;
            [eapply G_cbinding_env; eauto | eapply An.fun_fv_subset; eauto]);
      repeat (split; auto);
      eexists; repeat (split; eauto);
      intros; (repeat split; auto).

    eapply (He _ _ _ _ _ eq_refl Hesc) with (i := (i - (i - j))) (ρ1 :=  ρ3) (ρ2 := ρ4); eauto.
    - destruct bdr; auto.
      destruct (Hesc c) as [_ Hres].
      fcrush.
    - destruct (exposed_reflect w) as [Hwx | _]; auto.
      intros av Hav.
      destruct (Hweb c) as [_ Hexp].
      apply AExp_ret with (l := l); [| exact Hav].
      apply (Hexp _ _ Hw).
      apply w_ext_exposed; exact Hwx.
    - eapply G_subset; eauto.
      eapply G_set_lists; eauto.
      eapply G_set; eauto.
      + apply G_mono with (S i); eauto; lia.
      + eapply V_mono with i; try lia; eauto.
        eapply IHi; eauto.
        apply G_mono with (S i); eauto; lia.
      + eauto using cescaped_defining.
      + unfold cbinding; simpl.
        split; intros; fcrush.
      + eapply Included_refl; eauto.
  Qed.

  Lemma fun_compat A c W w Γ e k f l xs :
    W ! l = Some w ->
    occurs_free e \subset FromList xs :|: (f |: Γ) ->
    has_label e \subset Dom_map W ->
    well_annotated A c W (FromList xs :|: (f |: Γ)) e ->
    well_annotated A c W (f |: Γ) k ->
    well_annotated A c W Γ (Efun f l xs e k).
  Proof.
    unfold well_annotated, E, E'.
    intros HL HS HLe He Hk θ bdr Rs ω ex Heqθ Hescθ Hbdr Hω HW Hex; intros.

    inv H1.
    - fcrush.
    - destruct r1.
      fcrush.
      assert (Hwfρ1 : An.wf_cenv θ ρ1) by eauto using G_wf_cenv_l.
      assert (Hwfρ2 : wf_cenv ρ2) by eauto using G_wf_cenv_r.
      inv H2.
      rename c0 into v1.
      edestruct (Hk _  bdr Rs _ _ eq_refl Hescθ Hbdr Hω eq_refl Hex (i - 1) (M.set f (An.CTag (θ c) c l (An.CVfun f ρ1 xs e)) ρ1) (M.set f (CTag l (ω c) (CVfun f ρ2 xs e)) ρ2)) with (j1 := i0) (r1 := (An.CRes v1)) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + eapply G_subset.
        eapply G_set; eauto.
        eapply G_mono with i; eauto; lia.
        * eapply Vfun_V; eauto.
          apply G_mono with i; eauto; lia.
        * eauto using cescaped_defining.
        * unfold cbinding; simpl.
          split; intros; fcrush.
        * apply Included_refl.
      + edestruct R_res_inv_l as [w2 [Heqw2 HV]]; eauto; subst.
        exists (S j2), (CRes w2); split; eauto.
        * econstructor; eauto.
          destruct ex; auto.
          constructor; auto.
          eapply V_exposed; fcrush.
        * eapply R_mono; eauto; lia.
  Qed.

  Lemma app_compat A Γ W w xs f l c :
    W ! l = Some w ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    well_annotated A c W Γ (Eapp f l xs).
  Proof.
    unfold well_annotated, E, E'.
    intross Hw Hf Hxs θ bdr Rs ω ex Heqθ Hescθ Hbdr Hω HW Hex; simpl.

    pose proof (G_wf_cenv_l _ _ H) as Hwfρ1.
    pose proof (G_wf_cenv_r _ _ H) as Hwfρ2.
    pose proof (G_cescaped_env _ _ H) as Hescρ.
    pose proof (G_cbinding_env _ _ H) as Hbindρ.

    inv H1.
    - fcrush.
    - destruct r1.
      fcrush.
      inv H2.
      + (* escape => exposed *)
        edestruct (G_get _ _ H f) as [fv2 [Heqfv2 HV]]; eauto.
        destruct i.
        inv H0.
        rename c0 into v.
        destruct fv2; destruct c0; simpl in HV; invc.
        2 : { fcrush. }
        rename w0 into W0.
        destruct HV as [Hwf1 [Hwf2 [Heql [HW [w2 [Hw2 [Heqf [Heqxs [Heqe [Hsub [Hsite [Hesc_t [Hloc_t HV]]]]]]]]]]]]]; subst; invc.
        edestruct (G_get_list _ _ H xs vs) as [vs2 [Heqvs2 Vvs]]; eauto; invc.

        rename v0 into f0.
        destruct (set_lists_length3 (M.set f0 (CTag l0 (ω c') (CVfun f0 t l1 e0)) t) l1 vs2) as [ρ4 Heqρ4].
        unfold clval in *.
        rewrite (set_lists_length_eq _ _ _ _ H15); auto.
        eapply Forall2_length; eauto.

        assert (HE : E θ ω A' c' true (An.ai_ret A' l0) (ω c') (exposedb w2) (i - (i - i)) ρ'' ρ4 e0).
        {
          eapply (HV _ i c vs vs2); eauto.
          - eapply V_mono_Forall; eauto; lia.
          - inv Hwf1; subst.
            eapply @An.cbinding_handover_list with (c := c); eauto.
            + eapply An.wf_cenv_get_list; eauto.
            + eapply An.cescaped_env_get_list; eauto.
            + unfold An.analysis_context_escape_ok, An.escapes_ok in *.
              destruct (Hescθ c') as [_ Hesc]; fcrush.
          - intros.
            eapply V_exposed_Forall_escaped; eauto.
            eapply An.cescaped_env_get_list; eauto.
        }

        rewrite_math (i - (i - i) = i).

        unfold E, E' in HE.
        destruct (HE i0 (An.CRes v) I) as [j2 [r2 [He0 Rr]]]; try lia; auto.
        edestruct R_res_inv_l as [v2 [Heqv2 HVv]]; eauto; subst.

        unfold valid_web_map_context in *.
        destruct (Hω c) as [_ Hexpo].
        destruct (Hω c') as [_ Hexpo'].
        unfold web_map_exposed in *.
        edestruct Hexpo as [_ Haexpo]; eauto.
        edestruct Hexpo' as [_ Haexpo']; eauto.

        assert (Hw2expo : w2 = w_ext).
        {

          assert (Hl0 : (An.label_of (An.AVfun l0 f0 l1 e0)) \in (aexposed (θ c'))).
          {
            inv Hwf1.
            eapply AExp_esc; eauto.
          }
          simpl in Hl0.
          specialize (Haexpo' Hl0); subst; eauto.
        }

        assert (Hwexpo : w = w_ext).
        {
          assert (Hint : (An.l_top_intro, l) \in An.ai_int (θ c)).
          {
            destruct (H4 c' l0 c l) as [_ [_ Hec]].
            - fcrush.
            - eauto.
          }

          assert (Hl : l \in aexposed (θ c)).
          { eapply AExp_int_l; [exact Hint | apply AExp_top_intro]. }

          eapply (Hexpo _ _ Hw); eauto.
        }

        subst.

        exists (S j2), (CRes v2); split; eauto.
        econstructor; eauto.
        eapply @Cbstep_app; eauto.

        intros; split.
        * eapply V_exposed_Forall_escaped; eauto.
          eapply An.cescaped_env_get_list; eauto.
        * destruct (exposed_reflect w_ext); try contradiction.
          eapply cbstep_fuel_to_exposed_cres; eauto.
        * destruct ex; auto.
          destruct (exposed_reflect w_ext).
          eapply cbstep_fuel_to_exposed_cres; eauto.
          exfalso.
          eapply n; eauto.
          eapply w_ext_exposed; eauto.

      + rename H11 into Hbind_params.
        edestruct (G_get _ _ H f) as [fv2 [Heqfv2 HV]]; eauto.
        destruct i.
        inv H0.
        rename c0 into v.
        destruct fv2; destruct c0; simpl in HV; invc.
        2 : { fcrush. }
        rename w0 into W0.
        destruct HV as [Hwf1 [Hwf2 [Heql [HW [w2 [Hw2 [Heqf [Heqxs [Heqe [Hsub [Hsite [Hesc_t [Hloc_t HV]]]]]]]]]]]]]; subst; invc.
        edestruct (G_get_list _ _ H xs vs) as [vs2 [Heqvs2 Vvs]]; eauto; invc.

        rename v0 into f0.
        destruct (set_lists_length3 (M.set f0 (CTag l0 (ω c) (CVfun f0 t l1 e0)) t) l1 vs2) as [ρ4 Heqρ4].
        unfold clval in *.
        match goal with
        | [Hs : set_lists _ _ _ = Some ρ'' |- _] => rewrite (set_lists_length_eq _ _ _ _ Hs); auto
        end.
        eapply Forall2_length; eauto.

        assert (Hexvs2 : Ensembles.In web Exposed w2 -> Forall to_exposed vs2).
        {
          (* the callee is exposed, hence so are its parameters *)
          intros Hw2x.
          destruct (Hω c) as [_ Hexp].
          eapply (V_exposed_Forall_cbinding θ ω Hω (xs := l1));
            [ eapply V_mono_Forall; eauto; lia
            | eapply (An.cescaped_env_get_list Hescρ xs); eauto
            | exact Hbind_params
              | ].
          intros x Hin av Hav.
          eapply AExp_param; [exact Hsite | | exact Hin | exact Hav].
          unfold web_map_exposed in Hexp.
          apply (Hexp _ _ Hw2), w_ext_exposed; exact Hw2x.
        }

        assert (HE : E θ ω (θ c) c false (An.ai_ret (θ c) l0) (ω c) (exposedb w2) (i - (i - i)) ρ'' ρ4 e0).
        {
          eapply (HV _ i c vs vs2); eauto.
          - eapply V_mono_Forall; eauto; lia.
          - eapply (An.cescaped_env_get_list Hescρ xs); eauto.
          - fcrush.
        }

        rewrite_math (i - (i - i) = i).

        unfold E, E' in HE.
        destruct (HE i0 (An.CRes v) I) as [j2 [r2 [He0 Rr]]]; try lia; auto.
        edestruct R_res_inv_l as [v2 [Heqv2 HVv]]; eauto; subst.

        assert (Heqw : w = w2).
        {
          destruct (H4 c l0 c l) as [Hcc _];
            [apply Union_introl; constructor |].
          destruct (Hω c) as [Hassign Hexp].
          symmetry.
          exact (web_map_interact_eq Hassign Hexp (Hcc eq_refl eq_refl) Hw2 Hw).
        }
        subst.

        exists (S j2), (CRes v2); split; eauto.
        econstructor; eauto.
        eapply @Cbstep_app; eauto.
        * intros; split; eauto.
          destruct (exposed_reflect w2); try contradiction.
          eapply cbstep_fuel_to_exposed_cres; eauto.
        * destruct ex; auto.
          destruct (exposed_reflect w2).
          -- eapply cbstep_fuel_to_exposed_cres; eauto.
          -- (* the result flows into `Rs`, whose labels are all exposed *)
             constructor.
             destruct H5 as [Hesc_v Hfl_v].
             exact (V_exposed θ ω Hω HVv Hesc_v Hfl_v Hex).
  Qed.

  Lemma fundamental_property {A c W Γ e}:
    web_map_well_scoped W Γ e ->
    well_annotated A c W Γ e.
  Proof.
    intros H.
    induction H; intros.
    - eapply ret_compat; eauto.
    - eapply fun_compat; eauto;
        destruct (proj1 (web_map_well_scoped_inv _ _ _) H0) as [Hlab Hscope].
      + eapply well_scoped_inv; eauto.
      + exact Hlab.
    - (* eapply app_compat; eauto. *)
      admit.
    - admit.
    - admit.
    - admit.
    - (* eapply case_nil_compat; eauto. *)
      admit.
    - admit.
  Admitted.

End Compat.

(* Top Level *)

(* Top-level Compilation Unit & Linking *)
(* This is what an analysis should annotate the compilation unit with *)
Inductive cexp : Type :=
| CEunit : web_map -> exp -> cexp
| CElink : var -> cexp -> cexp -> cexp.

Hint Constructors cexp : core.

(* Linking *)
Definition clink x e1 e2 : cexp := CElink x e1 e2.

(* TODO: renaming *)
(* `A` is the analysis result of one of the units of `ce`. *)
Inductive has_cunit : cexp -> web_map -> Prop :=
| Has_cunit_unit :
  forall W e,
    has_cunit (CEunit W e) W

| Has_cunit_link1 :
  forall x ce1 ce2 W,
    has_cunit ce1 W ->
    has_cunit (CElink x ce1 ce2) W

| Has_cunit_link2 :
  forall x ce1 ce2 W,
    has_cunit ce2 W ->
    has_cunit (CElink x ce1 ce2) W.

Hint Constructors has_cunit : core.

Inductive occurs_free_top : cexp -> vars :=
| Free_cexp :
  forall e W x,
    occurs_free e x ->
    occurs_free_top (CEunit W e) x

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
  (occurs_free_top (CEunit W e)) <--> (occurs_free e).
Proof. split; unfold Ensembles.Included, Ensembles.In; fcrush. Qed.

(* Top-level Checking Semantics for the *Colored* Top-level Expression *)
(* The colors are already in the tree, so the top-level semantics does not
   mention `Θ` at all: it just runs each unit at the color preprocessing gave
   it, and unions the interactions the units record.
   `Θ` reappears only in the theorems, through `analysis_context_of`. *)
Inductive cbstep_top (ρ : cenv) : cexp -> fuel -> cres -> Prop :=
| CbstepT_link_Res :
  forall {x ce1 ce2 i1 i2 W l v r},
    cbstep_top_fuel ρ ce1 i1 (CRes (CTag l W v)) ->
    cbstep_top_fuel (M.set x (CTag l W v) ρ) ce2 i2 r ->
    cbstep_top ρ (CElink x ce1 ce2) (S (i1 + i2)) r

| CbstepT_link_OOT :
  forall {x ce1 ce2 i},
    cbstep_top_fuel ρ ce1 i COOT ->
    cbstep_top ρ (CElink x ce1 ce2) (S i) COOT

with cbstep_top_fuel (ρ : cenv) : cexp -> fuel -> cres -> Prop :=
| CbstepTF_unit :
  forall {W e i r},
    cbstep_fuel W true ρ e i r ->
    cbstep_top_fuel ρ (CEunit W e) i r

| CbstepTF_link_OOT :
  forall {x ce1 ce2},
    cbstep_top_fuel ρ (CElink x ce1 ce2) 0 COOT

| CbstepTF_link_Step :
  forall {x ce1 ce2 i r},
    cbstep_top ρ (CElink x ce1 ce2) i r ->
    cbstep_top_fuel ρ (CElink x ce1 ce2) (S i) r.

Hint Constructors cbstep_top : core.
Hint Constructors cbstep_top_fuel : core.

Scheme cbstep_top_ind' := Minimality for cbstep_top Sort Prop
with cbstep_top_fuel_ind' := Minimality for cbstep_top_fuel Sort Prop.

(* The step-index is aligned between the two semantics. *)
Lemma cbstep_fuel_cbstep_top_fuel W ρ e j r:
  cbstep_fuel W true ρ e j r ->
  cbstep_top_fuel ρ (CEunit W e) j r.
Proof. intros; eauto. Qed.

Lemma cbstep_top_fuel_cbstep_fuel W ρ e j r:
  cbstep_top_fuel ρ (CEunit W e) j r ->
  cbstep_fuel W true ρ e j r.
Proof. intros H. fcrush. Qed.

(* Every compilation unit is run exposed, so the result of any (possibly
   linked) top-level expression is always exposed. *)
Lemma cbstep_top_fuel_to_exposed_cres ρ ce j r :
  cbstep_top_fuel ρ ce j r ->
  to_exposed_cres r.
Proof.
  intros H.
  induction H using cbstep_top_fuel_ind' with
    (P := fun ρ ce i r => to_exposed_cres r)
    (P0 := fun ρ ce i r => to_exposed_cres r);
    eauto using cbstep_fuel_to_exposed_cres.
Qed.

(* A value returned by a (possibly linked) top-level expression is well-formed. *)
Lemma cbstep_top_wf_cres :
  forall ρ ce i r,
    cbstep_top ρ ce i r ->
    wf_cenv ρ ->
    wf_cres r.
Proof.
  intros ρ ce i r Hstep.
  induction Hstep as
    [ ρ x ce1 ce2 i1 i2 W l v r Hfuel1 IH1 Hfuel2 IH2
    | ρ x ce1 ce2 i Hfuel1 IH1
    | ρ W e i r Hfuel
    | ρ x ce1 ce2
    | ρ x ce1 ce2 i r Htop IHtop ]
    using cbstep_top_ind'
    with (P := fun ρ ce i r => wf_cenv ρ -> wf_cres r)
         (P0 := fun ρ ce i r => wf_cenv ρ -> wf_cres r).

  - (* CbstepT_link_Res: the linked value is well-formed, so the second unit
       still runs in a well-formed environment *)
    intros Hρ.
    assert (Hv : wf_cval (CTag l W v)) by (specialize (IH1 Hρ); inv IH1; assumption).
    exact (IH2 (wf_cenv_set ρ x (CTag l W v) Hρ Hv)).

  - (* CbstepT_link_OOT: no value is returned *)
    intros _; apply WF_COOT.

  - (* CbstepTF_unit *)
    intros Hρ.
    eapply cbstep_fuel_wf_res; eauto.

  - (* CbstepTF_link_OOT: no value is returned *)
    intros _; apply WF_COOT.

  - (* CbstepTF_link_Step *)
    intros Hρ.
    exact (IHtop Hρ).
Qed.

Lemma cbstep_top_fuel_wf_cres ρ ce i r :
  wf_cenv ρ ->
  cbstep_top_fuel ρ ce i r ->
  wf_cres r.
Proof.
  intros Hρ Hstep.
  inv Hstep.
  - eapply cbstep_fuel_wf_res; eauto.
  - apply WF_COOT.
  - match goal with
    | [Hs : cbstep_top _ _ _ _ |- _] =>
        exact (cbstep_top_wf_cres _ _ _ _ Hs Hρ)
    end.
Qed.

(* The top-level semantics returns at most one value. *)
Lemma cbstep_top_fuel_deterministic_aux :
  forall ρ ce i r,
    cbstep_top_fuel ρ ce i r ->
    forall i' r' v v',
      cbstep_top_fuel ρ ce i' r' ->
      r = CRes v ->
      r' = CRes v' ->
      (v = v' /\ i = i').
Proof.
  intros ρ ce i r Hstep.
  induction Hstep as
    [ ρ x ce1 ce2 i1 i2 W l v r Hs1 IH1 Hs2 IH2
    | ρ x ce1 ce2 i Hs1 IH1
    | ρ W e i r Hs
    | ρ x ce1 ce2
    | ρ x ce1 ce2 i r Htop IHtop ]
    using cbstep_top_fuel_ind'
    with (P := fun ρ ce i r =>
                 forall i' r' v v',
                   cbstep_top ρ ce i' r' ->
                   r = CRes v -> r' = CRes v' ->
                   (v = v' /\ i = i'))
         (P0 := fun ρ ce i r =>
                  forall i' r' v v',
                    cbstep_top_fuel ρ ce i' r' ->
                    r = CRes v -> r' = CRes v' ->
                    (v = v' /\ i = i'));
    intros i' r' v1 v1' Hs' Hr Hr'; subst.

  - (* CbstepT_link_Res: both runs bind the same value, then run the second
       component in the same environment *)
    inversion Hs' as [ x' a b j1 j2 W' l' v' r'' Hs1' Hs2'
                     | x' a b j Hf ]; subst.
    destruct (IH1 _ _ _ _ Hs1' eq_refl eq_refl) as [Heq1 Hi1].
    unfold CTag in Heq1; inversion Heq1; subst.
    destruct (IH2 _ _ _ _ Hs2' eq_refl eq_refl) as [Hv Hi2].
    split; [exact Hv | subst; reflexivity].

  - (* CbstepT_link_OOT: no value is returned *)
    discriminate.

  - (* CbstepTF_unit *)
    inversion Hs' as [ W' e' j' r'' Hx | x' a b | x' a b j' r'' Hnew ]; subst.
    exact (cbstep_fuel_deterministic v1 v1' Hs Hx).

  - (* CbstepTF_link_OOT: no value is returned *)
    discriminate.

  - (* CbstepTF_link_Step *)
    inversion Hs' as [ W' e' j' r'' Hx | x' a b | x' a b j' r'' Hnew ]; subst.
    destruct (IHtop _ _ _ _ Hnew eq_refl eq_refl) as [Hv Hi].
    split; [exact Hv | f_equal; exact Hi].
Qed.

Theorem cbstep_top_fuel_deterministic v v' {ρ ce i i'} :
  cbstep_top_fuel ρ ce i (CRes v) ->
  cbstep_top_fuel ρ ce i' (CRes v') ->
  (v = v' /\ i = i').
Proof.
  intros H H'.
  exact (cbstep_top_fuel_deterministic_aux ρ ce i (CRes v) H i' (CRes v') v v' H' eq_refl eq_refl).
Qed.

(* `ω` agrees with the coloring of `cce`: `we` has the same shape as `cce`,
   and the unit wearing color `c` is annotated with the web map `ω c`. *)
Inductive web_map_context_of (ω : web_map_context) : An.ccexp -> cexp -> Prop :=
| Web_map_context_of_unit :
  forall c A Rs e,
    web_map_context_of ω (An.CCunit c A Rs e) (CEunit (ω c) e)

| Web_map_context_of_link :
  forall x cce1 cce2 we1 we2,
    web_map_context_of ω cce1 we1 ->
    web_map_context_of ω cce2 we2 ->
    web_map_context_of ω (An.CClink x cce1 cce2) (CElink x we1 we2).

Hint Constructors web_map_context_of : core.

Lemma web_map_context_of_unit_inv {ω c A Rs e we} :
  web_map_context_of ω (An.CCunit c A Rs e) we ->
  we = CEunit (ω c) e.
Proof. intros H; inv H; reflexivity. Qed.

Lemma web_map_context_of_link_inv {ω x cce1 cce2 we} :
  web_map_context_of ω (An.CClink x cce1 cce2) we ->
  exists we1 we2,
    we = CElink x we1 we2 /\
    web_map_context_of ω cce1 we1 /\
    web_map_context_of ω cce2 we2.
Proof. intros H; inv H; eauto. Qed.

(* The units of the analysis-level program `ce` and of its web-annotated
   counterpart `we` are paired up, and each web map is valid for the analysis
   result of its unit. *)
Inductive web_map_valid_of : An.cexp -> cexp -> Prop :=
| Web_map_valid_of_unit :
  forall A Rs e W,
    web_map_assign W ->
    web_map_exposed W A ->
    web_map_valid_of (An.CEunit A Rs e) (CEunit W e)

| Web_map_valid_of_link :
  forall x ce1 ce2 we1 we2,
    web_map_valid_of ce1 we1 ->
    web_map_valid_of ce2 we2 ->
    web_map_valid_of (An.CElink x ce1 ce2) (CElink x we1 we2).

Hint Constructors web_map_valid_of : core.

(* `web_map_context_of` only depends on `ω` at the colors of the units. *)
Lemma web_map_context_of_ext {ω ω' cce we} :
  web_map_context_of ω cce we ->
  (forall c A, An.has_unit cce c A -> ω c = ω' c) ->
  web_map_context_of ω' cce we.
Proof.
  intros H.
  induction H as [c A Rs e | x cce1 cce2 we1 we2 H1 IH1 H2 IH2]; intros Hag.
  - rewrite (Hag c A (An.Has_unit_unit A Rs c e)).
    constructor.
  - constructor.
    + apply IH1; intros c A Hu; eapply Hag; eapply An.Has_unit_link1; exact Hu.
    + apply IH2; intros c A Hu; eapply Hag; apply An.Has_unit_link2; exact Hu.
Qed.

(* A web map context agreeing with the coloring, falling back to the empty map
   on colors that name no unit. *)
Lemma web_map_context_exists {θ c1 ce c2 cce} :
  An.coloring c1 ce c2 cce ->
  An.analysis_context_of θ cce ->
  forall we,
    web_map_valid_of ce we ->
    exists ω,
      web_map_context_of ω cce we /\
      valid_web_map_context ω θ.
Proof.
  intros Hcol.
  induction Hcol as [c A Rs e | c1 c2 c3 x e1 e2 cce1 cce2 Hc1 IH1 Hc2 IH2];
    intros Hθ we Hv.
  - inversion Hv as [A' Rs' e' W Hassign Hexp | ]; subst.
    pose (ω := fun c' => if Nat.eqb c' c then W else (M.empty web)).
    assert (Hωc : ω c = W) by (unfold ω; rewrite Nat.eqb_refl; reflexivity).
    exists ω; split.
    + rewrite <- Hωc; constructor.
    + intros c'; unfold ω.
      destruct (Nat.eqb c' c) eqn:Hc.
      * apply Nat.eqb_eq in Hc; subst c'.
        split; [exact Hassign |].
        rewrite <- (Hθ c A (An.Has_unit_unit A Rs c e)); exact Hexp.
      * split; intros l w Hget; rewrite M.gempty in Hget; discriminate.
  - inversion Hv as [ | x' e1' e2' we1 we2 Hv1 Hv2 ]; subst.
    destruct (IH1 (An.analysis_context_of_link1 Hθ) we1 Hv1) as [ω1 [Hof1 Hvalid1]].
    destruct (IH2 (An.analysis_context_of_link2 Hθ) we2 Hv2) as [ω2 [Hof2 Hvalid2]].
    pose (ω := fun c' => if Nat.ltb c' c2 then ω1 c' else ω2 c').
    exists ω; split.
    + constructor.
      * eapply web_map_context_of_ext; [exact Hof1 |].
        intros c A Hu.
        destruct (An.coloring_range Hc1 c A Hu) as [Hlo Hhi].
        assert (Hlt : Nat.ltb c c2 = true) by (apply Nat.ltb_lt; lia).
        unfold ω; rewrite Hlt; reflexivity.
      * eapply web_map_context_of_ext; [exact Hof2 |].
        intros c A Hu.
        destruct (An.coloring_range Hc2 c A Hu) as [Hlo Hhi].
        assert (Hge : Nat.ltb c c2 = false) by (apply Nat.ltb_ge; lia).
        unfold ω; rewrite Hge; reflexivity.
    + intros c'; unfold ω.
      destruct (Nat.ltb c' c2); [exact (Hvalid1 c') | exact (Hvalid2 c')].
Qed.

Section LRTop.

  (* Cross-language Logical Relations *)

  Variable θ : analysis_context.
  Hypothesis θ_escape_ok : analysis_context_escape_ok θ.

  Variable ω : web_map_context.
  Hypothesis ω_valid : valid_web_map_context ω θ.

  Definition E_top' (P : nat -> An.clval -> clval -> Prop) (i : nat) (ρ1 : An.cenv) (e1 : An.ccexp) (ρ2 : cenv) (e2 : cexp) : Prop :=
    forall j1 r1 I1,
      j1 <= i ->
      An.cbstep_top_fuel ρ1 e1 j1 r1 I1 ->
      exists j2 r2,
        cbstep_top_fuel ρ2 e2 j2 r2 /\
        R' P (i - j1) r1 r2.

  (* Related values that cross the program boundary: the source value has
     escaped, and the target value is exposed. *)
  Definition V_top i v1 v2 := V θ ω i v1 v2 /\ An.cboundary v1 /\ to_exposed v2.

  Definition R_top := R' V_top.
  Definition E_top := E_top' V_top.

  Lemma V_V_top i v1 v2 :
    An.cboundary v1 ->
    to_exposed v2 ->
    (V θ ω i v1 v2 <-> V_top i v1 v2).
  Proof. unfold V_top; tauto. Qed.

  Lemma R_R_top :
    forall i r1 r2,
      An.cboundary_res r1 ->
      to_exposed_cres r2 ->
      (R θ ω i r1 r2 <-> R_top i r1 r2).
  Proof.
    unfold R, R_top, R'.
    intros i r1 r2 Hb Hx.
    destruct r1 as [| v1], r2 as [| v2]; try tauto.
    cbn in Hb.
    inv Hx.
    unfold V_top; tauto.
  Qed.

  Lemma E_E_top A c Rs W i ρ1 ρ2 e :
    E θ ω A c true Rs W true i ρ1 ρ2 e ->
    E_top i ρ1 (An.CCunit c A Rs e) ρ2 (CEunit W e).
  Proof.
    unfold E, E_top, E', E_top'.
    intros.
    inv H1.
    edestruct H as [j2 [r2 [Hcbstep HR]]]; eauto.
    exists j2, r2; split; eauto.
    assert (Hb1 : An.cboundary_res r1) by (eapply An.cbstep_fuel_cboundary_res; eauto).
    assert (Hb2 : to_exposed_cres r2) by (eapply cbstep_fuel_to_exposed_cres; eauto).
    eapply R_R_top; eauto.
  Qed.

  Lemma E_top_E A c Rs W i ρ1 ρ2 e :
    E_top i ρ1 (An.CCunit c A Rs e) ρ2 (CEunit W e) ->
    E θ ω A c true Rs W true i ρ1 ρ2 e.
  Proof.
    unfold E, E_top, E', E_top'.
    intros.
    edestruct H as [j2 [r2 [Hcbstep HR]]]; eauto.
    exists j2, r2; split; eauto.
    eapply cbstep_top_fuel_cbstep_fuel; eauto.
    assert (Hb1 : An.cboundary_res r1) by (eapply An.cbstep_fuel_cboundary_res; eauto).
    assert (Hb2 : to_exposed_cres r2) by (eapply cbstep_top_fuel_to_exposed_cres; eauto).
    eapply R_R_top; eauto.
  Qed.

  (* Every value bound at the top level crosses the program boundary, so the
     environment invariants of a unit are recovered in `G_top_G` from the unit
     treating its imports as unknown. *)
  Definition G_top i Γ1 ρ1 ρ2 :=
    An.wf_cenv θ ρ1 /\
      wf_cenv ρ2 /\
      forall x,
        (x \in Γ1) ->
        exists v1 v2,
          M.get x ρ1 = Some v1 /\
            M.get x ρ2 = Some v2 /\
            V_top i v1 v2.

  Lemma G_top_G {i Γ1 ρ1 ρ2} :
    G_top i Γ1 ρ1 ρ2 ->
    forall c,
      (forall x, (x \in Γ1) -> AVtop \in An.ai_env (θ c) x) ->
      G θ ω c i Γ1 ρ1 ρ2.
  Proof.
    unfold G_top, G.
    intros [Hwf1 [Hwf2 HG]] c Htop.
    split; [exact Hwf1 | split; [exact Hwf2 | split; [| split]]].
    - intros x v Hx Hget.
      destruct (HG x Hx) as [v1 [v2 [Hg1 [Hg2 [_ [HB _]]]]]].
      rewrite Hg1 in Hget; inv Hget.
      apply An.cboundary_cescaped; exact HB.
    - intros x v Hx Hget.
      destruct (HG x Hx) as [v1 [v2 [Hg1 [Hg2 [HV [HB _]]]]]].
      rewrite Hg1 in Hget; inv Hget.
      apply An.cboundary_cbinding;
        [eapply V_wf_cval_l; eauto | exact HB | apply Htop; exact Hx].
    - intros x Hx.
      destruct (HG x Hx) as [v1 [v2 [Hg1 [Hg2 [HV _]]]]].
      exists v1, v2; auto.
  Qed.

  Lemma G_top_wf_env_l i Γ1 ρ1 ρ2 :
    G_top i Γ1 ρ1 ρ2 ->
    An.wf_cenv θ ρ1.
  Proof. unfold G_top. intros; tauto. Qed.

  Lemma G_top_wf_cenv_r i Γ1 ρ1 ρ2 :
    G_top i Γ1 ρ1 ρ2 ->
    wf_cenv ρ2.
  Proof. unfold G_top. intros; tauto. Qed.

  Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 :
    G_top i Γ1 ρ1 ρ2 ->
    Γ2 \subset Γ1 ->
    G_top i Γ2 ρ1 ρ2.
  Proof.
    unfold G_top.
    intros [Hwf1 [Hwf2 HG]] Hsub.
    split; [exact Hwf1 | split; [exact Hwf2 |]].
    intros x Hx; apply HG; apply Hsub; exact Hx.
  Qed.

  (* Top-level Monotonicity Lemmas *)
  Lemma V_top_mono i :
    forall {j v1 v2},
      V_top i v1 v2 ->
      j <= i ->
      V_top j v1 v2.
  Proof.
    intros j v1 v2 [HV [HB Hx]] Hj.
    split; [eapply V_mono; eauto | split; assumption].
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
    destruct (H j1 r1 I1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
    exists j2, r2; split; eauto.
    apply R_top_mono with (i - j1); try lia; auto.
  Qed.

  Lemma G_top_mono {Γ1 ρ1 ρ2} i j:
    G_top i Γ1 ρ1 ρ2 ->
    j <= i ->
    G_top j Γ1 ρ1 ρ2.
  Proof.
    unfold G_top.
    intros [Hwf1 [Hwf2 HG]] Hj.
    split; [exact Hwf1 | split; [exact Hwf2 |]].
    intros x Hx.
    destruct (HG x Hx) as [v1 [v2 [Hg1 [Hg2 HV]]]].
    exists v1, v2.
    split; [exact Hg1 | split; [exact Hg2 | eapply V_top_mono; eauto]].
  Qed.

End LRTop.

Section Top.
  (* Top Level Relation and Theorem *)

  Definition trans_correct_top ce we :=
    (occurs_free_top we) \subset (An.occurs_free_top ce) /\
      forall θ ω cce c1 c2,
        coloring c1 ce c2 cce ->
        analysis_context_of θ cce ->
        analysis_context_escape_ok θ ->
        web_map_context_of ω cce we ->
        valid_web_map_context ω θ ->
        forall i ρ1 ρ2,
          G_top θ ω i (An.occurs_free_top ce) ρ1 ρ2 ->
          E_top θ ω i ρ1 cce ρ2 we.

  Lemma trans_correct_top_subset ce we :
    trans_correct_top ce we ->
    (occurs_free_top we) \subset (An.occurs_free_top ce).
  Proof. unfold trans_correct_top. fcrush. Qed.

  Theorem top A e Rs W:
    web_map_exposed W A ->
    has_label e \subset Dom_map W ->
    Rs \subset An.ai_esc A ->
    imports_unknown A (occurs_free e) ->
    trans_correct_top (An.CEunit A Rs e) (CEunit W e).
  Proof.
    unfold trans_correct_top, imports_unknown.
    intros Hexp Hsub Hesc Himp; intros.
    split; intros.

    eapply Included_trans.
    eapply occurs_free_top_cexp; eauto.
    eapply An.occurs_free_top_cexp; eauto.

    inv H.
    assert (Hwa : well_annotated A c1 W (occurs_free e) e).
    {
      eapply fundamental_property; eauto.
      unfold analysis_context_escape_ok.
      eapply web_map_well_scoped_intro; [exact Hsub | apply Included_refl].
    }

    eapply E_E_top; eauto.
    unfold well_annotated in Hwa.
    eapply Hwa; eauto.

    - unfold analysis_context_of in *.
      symmetry.
      eapply H0; eauto.
    - pose proof (web_map_context_of_unit_inv H2) as Hinv.
      fcrush.
    - unfold aexposed_avals.
      intros.
      eapply AExp_esc; eauto.
    - eapply (G_top_G θ ω).
      + eapply G_top_subset; eauto.
        eapply An.occurs_free_top_cexp; eauto.
      + intros y Hy.
        rewrite <- (H0 c1 A (An.Has_unit_unit A Rs c1 e)).
        apply Himp; exact Hy.
  Qed.

End Top.

Section Adequacy.

  (* Note that adequacy applies for the colored semantics and objects. *)

  Theorem adequacy ce we :
    trans_correct_top ce we ->
    forall θ ω cce c1 c2,
      coloring c1 ce c2 cce ->
      analysis_context_of θ cce ->
      analysis_context_escape_ok θ ->
      web_map_context_of ω cce we ->
      valid_web_map_context ω θ ->
      forall ρ1 ρ2,
        (forall k, G_top θ ω k (An.occurs_free_top ce) ρ1 ρ2) ->
        forall j1 r1 I1,
          An.cbstep_top_fuel ρ1 cce j1 r1 I1 ->
          exists j2 r2,
            cbstep_top_fuel ρ2 we j2 r2 /\
              (forall k, R_top θ ω k r1 r2).
  Proof.
    intros [HS HT] θ ω cce c1 c2 Hcol Hθ Hesc Hωof Hω ρ1 ρ2 HG j1 r1 I1 Hstep.

    (* the run of the target, from the relation at index `j1` *)
    assert (HE : E_top θ ω j1 ρ1 cce ρ2 we) by (eapply HT; eauto).
    destruct (HE j1 r1 I1 ltac:(lia) Hstep) as [j2 [r2 [Hstep2 HR]]].
    exists j2, r2; split; [exact Hstep2 |].

    (* the results are related at every index `k`, from the relation at
       index `j1 + k` and the determinism of the target *)
    intros k.
    assert (HE' : E_top θ ω (j1 + k) ρ1 cce ρ2 we) by (eapply HT; eauto).
    destruct (HE' j1 r1 I1 ltac:(lia) Hstep) as [j2' [r2' [Hstep2' HR']]].
    unfold R_top.
    destruct r1 as [| v1], r2 as [| v2], r2' as [| v2'];
      cbn in HR, HR' |- *; try contradiction; auto.
    replace (j1 + k - j1) with k in HR' by lia.
    rewrite (proj1 (cbstep_top_fuel_deterministic v2 v2' Hstep2 Hstep2')).
    exact HR'.
  Qed.

  Theorem adequacy_closed ce we :
    trans_correct_top ce we ->
    An.occurs_free_top ce \subset (Empty_set _) ->
    forall θ ω cce c1 c2,
      coloring c1 ce c2 cce ->
      analysis_context_of θ cce ->
      analysis_context_escape_ok θ ->
      web_map_context_of ω cce we ->
      valid_web_map_context ω θ ->
      forall j1 r1 I1,
        An.cbstep_top_fuel (M.empty _) cce j1 r1 I1 ->
        exists j2 r2,
          cbstep_top_fuel (M.empty _) we j2 r2 /\
            (forall k, R_top θ ω k r1 r2).
  Proof.
    intros Htc Hclosed θ ω cce c1 c2 Hcol Hθ Hesc Hωof Hω j1 r1 I1 Hstep.
    eapply adequacy; eauto.

    (* the empty environments are related at every index *)
    intros k.
    split; [| split].
    - constructor.
      intros x v Hget; rewrite M.gempty in Hget; discriminate.
    - constructor.
      intros x v Hget; rewrite M.gempty in Hget; discriminate.
    - intros x Hx; apply Hclosed in Hx; inv Hx.
  Qed.

  (* Adequacy from the colorless relations: the coloring, `θ` and `ω` are
     produced rather than assumed. *)
  Theorem adequacy2 ce we :
    trans_correct_top ce we ->
    web_map_valid_of ce we ->
    (forall A, An.has_cunit ce A -> An.escapes_ok A) ->

    exists θ ω cce c1 c2,
      An.coloring c1 ce c2 cce /\
      An.analysis_context_of θ cce /\
      An.analysis_context_escape_ok θ /\
      web_map_context_of ω cce we /\
      valid_web_map_context ω θ /\
      forall ρ1 ρ2,
        (forall k, G_top θ ω k (An.occurs_free_top ce) ρ1 ρ2) ->
        forall j1 r1 I1,
          An.cbstep_top_fuel ρ1 cce j1 r1 I1 ->
          exists j2 r2,
            cbstep_top_fuel ρ2 we j2 r2 /\
              (forall k, R_top θ ω k r1 r2).
  Proof.
    intros Htc Hvalid Hunits.

    (* color `ce`, and pick contexts agreeing with the coloring *)
    destruct (An.coloring_exists 0 ce) as [c2 [cce Hcol]].
    destruct (An.cexp_has_cunit ce) as [d Hd].
    destruct (An.coloring_context Hcol d (Hunits d Hd) Hunits) as [θ [Hθ Hesc]].
    destruct (web_map_context_exists Hcol Hθ we Hvalid) as [ω [Hωof Hω]].
    exists θ, ω, cce, 0, c2.
    split; [exact Hcol |].
    split; [exact Hθ |].
    split; [exact Hesc |].
    split; [exact Hωof |].
    split; [exact Hω |].

    intros ρ1 ρ2 HG j1 r1 I1 Hstep.
    exact (adequacy ce we Htc θ ω cce 0 c2 Hcol Hθ Hesc Hωof Hω ρ1 ρ2 HG j1 r1 I1 Hstep).
  Qed.

  Theorem adequacy_closed2 ce we :
    trans_correct_top ce we ->
    An.occurs_free_top ce \subset (Empty_set _) ->
    web_map_valid_of ce we ->
    (forall A, An.has_cunit ce A -> An.escapes_ok A) ->

    exists θ ω cce c1 c2,
      An.coloring c1 ce c2 cce /\
      An.analysis_context_of θ cce /\
      An.analysis_context_escape_ok θ /\
      web_map_context_of ω cce we /\
      valid_web_map_context ω θ /\
      forall j1 r1 I1,
        An.cbstep_top_fuel (M.empty _) cce j1 r1 I1 ->
        exists j2 r2,
          cbstep_top_fuel (M.empty _) we j2 r2 /\
            (forall k, R_top θ ω k r1 r2).
  Proof.
    intros Htc Hclosed Hvalid Hunits.
    destruct (adequacy2 ce we Htc Hvalid Hunits)
      as [θ [ω [cce [c1 [c2 [Hcol [Hθ [Hesc [Hωof [Hω Hrun]]]]]]]]]].
    exists θ, ω, cce, c1, c2.
    split; [exact Hcol |].
    split; [exact Hθ |].
    split; [exact Hesc |].
    split; [exact Hωof |].
    split; [exact Hω |].

    intros j1 r1 I1 Hstep.
    eapply Hrun; [| exact Hstep].

    (* the empty environments are related at every index *)
    intros k.
    split; [| split].
    - constructor.
      intros x v Hget; rewrite M.gempty in Hget; discriminate.
    - constructor.
      intros x v Hget; rewrite M.gempty in Hget; discriminate.
    - intros x Hx; apply Hclosed in Hx; inv Hx.
  Qed.

End Adequacy.

Section Linking.

  (* Inversion of the source top-level semantics of a link *)
  Lemma An_cbstep_top_fuel_link_inv {ρ x cce1 cce2 j r I} :
    An.cbstep_top_fuel ρ (An.CClink x cce1 cce2) j r I ->
    (r = An.COOT /\ j = 0) \/
      (exists i1 I1,
          j = S (S i1) /\ r = An.COOT /\ An.cbstep_top_fuel ρ cce1 i1 An.COOT I1) \/
      (exists i1 i2 v I1 I2,
          j = S (S (i1 + i2)) /\
            An.cbstep_top_fuel ρ cce1 i1 (An.CRes v) I1 /\
            An.cbstep_top_fuel (M.set x v ρ) cce2 i2 r I2).
  Proof.
    intros H.
    inv H; [left; auto | right].
    match goal with [Hl : An.cbstep_top _ _ _ _ _ |- _] => inv Hl end.
    - right; do 5 eexists; split; [reflexivity | split; eassumption].
    - left; do 2 eexists; split; [reflexivity | split; [reflexivity | eassumption]].
  Qed.

  (* The environment relation for the second component: the result of the
     first component, which crosses the boundary, is bound to `x`. *)
  Lemma G_top_link θ ω i j x e1 e2 ρ1 ρ2 v1 v2 :
    valid_web_map_context ω θ ->
    j <= i ->
    G_top θ ω i (An.occurs_free_top (An.clink x e1 e2)) ρ1 ρ2 ->
    V_top θ ω j v1 v2 ->
    G_top θ ω j (An.occurs_free_top e2) (M.set x v1 ρ1) (M.set x v2 ρ2).
  Proof.
    intros Hω Hj [Hwf1 [Hwf2 HG]] HV.
    assert (Hwfv1 : An.wf_cval θ v1)
      by (destruct HV as [HV _]; eapply V_wf_cval_l; eauto).
    assert (Hwfv2 : wf_cval v2)
      by (destruct HV as [HV _]; eapply V_wf_cval_r; eauto).
    refine (conj _ (conj _ _)).
    - apply An.wf_cenv_set; [exact Hwf1 | exact Hwfv1].
    - apply wf_cenv_set; [exact Hwf2 | exact Hwfv2].
    - intros y Hy.
      destruct (M.elt_eq x y) as [Hxy | Hxy].
      + subst y.
        exists v1, v2.
        rewrite !M.gss.
        exact (conj eq_refl (conj eq_refl HV)).
      + destruct (HG y (An.Free_clink2 x y e1 e2 Hxy Hy)) as [w1 [w2 [Hget1 [Hget2 HVw]]]].
        exists w1, w2.
        rewrite !M.gso by (intros Heq; subst y; contradiction).
        split; [exact Hget1 | split; [exact Hget2 | eapply V_top_mono; eauto]].
  Qed.

  Theorem preserves_linking x e1 e1' e2 e2' :
    trans_correct_top e1 e1' ->
    trans_correct_top e2 e2' ->
    trans_correct_top (An.clink x e1 e2) (clink x e1' e2').
  Proof.
    intros [Hfree1 He1] [Hfree2 He2].
    split.
    - intros y Hy.
      unfold Ensembles.In, clink in Hy.
      inv Hy.
      + apply An.Free_clink1; apply Hfree1; assumption.
      + apply An.Free_clink2; [assumption | apply Hfree2; assumption].
    - intros θ ω cce c1 c3 Hcol Hθ Hesc_ok Hωof Hω i ρ1 ρ2 HG.
      destruct (An.coloring_link_inv Hcol) as [c2 [cce1 [cce2 [Heq [Hcol1 Hcol2]]]]].
      subst cce.
      destruct (web_map_context_of_link_inv Hωof) as [we1 [we2 [Heqwe [Hω1 Hω2]]]].
      unfold clink in Heqwe; inv Heqwe.
      pose proof (An.analysis_context_of_link1 Hθ) as Hθ1.
      pose proof (An.analysis_context_of_link2 Hθ) as Hθ2.
      (* the first component runs in the same environment *)
      assert (HG1 : G_top θ ω i (An.occurs_free_top e1) ρ1 ρ2).
      { eapply G_top_subset; [exact HG |].
        intros y Hy; apply An.Free_clink1; exact Hy. }
      pose proof (He1 θ ω cce1 c1 c2 Hcol1 Hθ1 Hesc_ok Hω1 Hω i ρ1 ρ2 HG1) as HE1.
      unfold E_top, E_top'.
      intros j1 r1 I1 Hj1 Hstep.
      destruct (An_cbstep_top_fuel_link_inv Hstep)
        as [[-> ->] | [[k1 [J1 [-> [-> Hs1]]]] | [k1 [k2 [u [J1 [J2 [-> [Hs1 Hs2]]]]]]]]].
      + (* out of time: so is the linked program, right away *)
        exists 0, COOT.
        split; [apply CbstepTF_link_OOT | exact I].
      + (* the first component runs out of time *)
        destruct (HE1 k1 An.COOT J1 ltac:(lia) Hs1) as [j2 [r2 [Hc1 HR1]]].
        destruct r2 as [| v2]; [| destruct HR1].
        exists (S (S j2)), COOT.
        split; [| exact I].
        apply CbstepTF_link_Step; apply CbstepT_link_OOT; exact Hc1.
      + (* run the first component *)
        destruct (HE1 k1 (An.CRes u) J1 ltac:(lia) Hs1) as [j2 [r2 [Hc1 HR1]]].
        destruct r2 as [| v2]; [destruct HR1 |].
        (* run the second component with its result bound to `x` *)
        pose proof (G_top_link θ ω i (i - k1) x e1 e2 ρ1 ρ2 u v2 Hω ltac:(lia) HG HR1) as HG2.
        pose proof (He2 θ ω cce2 c2 c3 Hcol2 Hθ2 Hesc_ok Hω2 Hω (i - k1) _ _ HG2) as HE2.
        destruct (HE2 k2 r1 J2 ltac:(lia) Hs2) as [j3 [r3 [Hc2 HR2]]].
        destruct v2 as [l' W' w'].
        exists (S (S (j2 + j3))), r3.
        split.
        * apply CbstepTF_link_Step.
          eapply CbstepT_link_Res; [exact Hc1 | exact Hc2].
        * eapply R_top_mono; eauto; lia.
  Qed.

End Linking.

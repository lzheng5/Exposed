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

Parameter w_ext : web.
Parameter w_ext_exposed : forall w, w \in Exposed <-> w = w_ext.
Parameter w_int : web. (* not exposed *)

Definition web_map_assign (W : web_map) :=
  forall l w,
    M.get l W = Some w ->
    w = w_int \/ w = w_ext.

(* Internal webs are consistent with `ainteractions` *)
Definition web_map_internals (W : web_map) (AInt : An.internals) : Prop :=
  forall l w,
    M.get l W = Some w ->
    (w = w_int <-> l \in AInt).

(* *Static* Web Map Invariants *)
Definition valid_web_map (W : web_map) (A : An.analysis_result) e : Prop :=
  web_map_assign W /\
  (Dom_map W \subset has_label e) /\
  web_map_internals W (An.ainternals_of (An.ai_int A)).

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

(* Cross-semantics Logical Relations *)
Section LRBase.

  Variable θ : analysis_context.
  Hypothesis θ_escape_ok : analysis_context_escape_ok θ.

  Definition R' (P : nat -> An.clval -> clval -> Prop) (i : nat) (r1 : An.cres) (r2 : cres) :=
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
        exists w2, W2 ! l2 = Some w2 /\
        (w2 \in Exposed -> to_exposed cv2) /\
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
              match i with
              | 0 => True
              | S i0 =>
                  forall (bdr : bool) j vs1 vs2 ρ3 ρ4,
                    j <= i0 ->
                    (w2 \in Exposed -> Forall to_exposed vs2) ->
                    Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                    set_lists xs1 vs1 (M.set f1 (An.CTag A1 c1 l1 (An.CVfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                    set_lists xs2 vs2 (M.set f2 (CTag l2 W2 (CVfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                    (if bdr then w2 \in Exposed else True) ->
                    E' V A1 c1 bdr (An.ai_ret A1 l1) W2 (exposedb w2) (i0 - (i0 - j)) ρ3 ρ4 e1
              end

        | _, _ => False
        end
    end.

Definition R := (R' V).

Definition E := (E' V).

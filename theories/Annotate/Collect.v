From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From Annotate Require Import LabeledANF.

(* Colored Collecting Semantics *)

Inductive color : Type :=
| Blue : color (* current program context *)
| Red : color. (* external program context *)

Hint Constructors color : core.

Definition clabel : Type := (color * label).

(* Label Sets *)
Definition clabel_set := Ensemble (clabel * clabel).

(* Tagged Value *)
Inductive ctag A : Type :=
| CTAG : clabel -> A -> ctag A.

Hint Constructors ctag : core.

(* Value *)
Inductive cval : Type :=
| CVfun : var -> M.t (ctag cval) -> list var -> exp -> cval
| CVconstr : ctor_tag -> list (ctag cval) -> cval.

Hint Constructors cval : core.

Definition clval := ctag cval.

Definition CTag c l cv := CTAG cval (c, l) cv.

(* Environment *)
Definition cenv := M.t clval.

(* Result *)
Inductive cres : Type :=
| COOT
| CRes : clval -> cres.

Hint Constructors cres : core.

(* Collecting Semantics *)
(* `L` is the collected output label set by stepping the collecting big-step semantics. *)
(* We color the term depending on the current context we are in. *)
Inductive cbstep (L : clabel_set) (c : color) (ρ : cenv) : exp -> fuel -> cres -> Prop :=
| Cbstep_ret :
  forall {x v},
    M.get x ρ = Some v ->
    cbstep L c ρ (Eret x) 0 (CRes v)

| Cbstep_fun :
  forall {f l xs e k i r},
    cbstep_fuel L c (M.set f (CTag c l (CVfun f ρ xs e)) ρ) k i r ->
    cbstep L c ρ (Efun f l xs e k) i r

| Cbstep_app :
  forall {f f' c' l l' xs ρ' xs' e vs ρ'' i r},
    M.get f ρ = Some (CTag c' l' (CVfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (CTag c' l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    (((c', l'), (c, l)) \in L) ->
    cbstep_fuel L c' ρ'' e i r ->
    cbstep L c ρ (Eapp f l xs) i r

| Cbstep_letapp_Res :
  forall {x f f' l l' xs k ρ' xs' e vs ρ'' c' i i' v r},
    M.get f ρ = Some (CTag c' l' (CVfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (CTag c' l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    (((c', l'), (c, l)) \in L) ->
    cbstep_fuel L c' ρ'' e i (CRes v) ->
    cbstep_fuel L c (M.set x v ρ) k i' r ->
    cbstep L c ρ (Eletapp x f l xs k) (i + i') r

| Cbstep_letapp_OOT :
  forall {x f f' l c' l' xs k ρ' xs' e vs ρ'' i},
    M.get f ρ = Some (CTag c' l' (CVfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (CTag c' l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    (((c', l'), (c, l)) \in L) ->
    cbstep_fuel L c' ρ'' e i COOT ->
    cbstep L c ρ (Eletapp x f l xs k) i COOT

| Cbstep_constr :
  forall {x l t xs e r vs i},
    get_list xs ρ = Some vs ->
    cbstep_fuel L c (M.set x (CTag c l (CVconstr t vs)) ρ) e i r ->
    cbstep L c ρ (Econstr x l t xs e) i r

| Cbstep_proj :
  forall {x l c' l' t i y e j r v vs},
    M.get y ρ = Some (CTag c' l' (CVconstr t vs)) ->
    nth_error vs i = Some v ->
    (((c', l'), (c, l)) \in L) ->
    cbstep_fuel L c (M.set x v ρ) e j r ->
    cbstep L c ρ (Eproj x l i y e) j r

| Cbstep_case :
  forall {x l c' l' cl t e r i vs},
    M.get x ρ = Some (CTag c' l' (CVconstr t vs)) ->
    find_tag cl t e ->
    (((c', l'), (c, l)) \in L) ->
    cbstep_fuel L c ρ e i r ->
    cbstep L c ρ (Ecase x l cl) i r

with cbstep_fuel (L : clabel_set) (c : color) (ρ : cenv) : exp -> fuel -> cres -> Prop :=
| CbstepF_OOT :
  forall {e},
    cbstep_fuel L c ρ e 0 COOT

| CbstepF_Step :
  forall {e i r},
    cbstep L c ρ e i r ->
    cbstep_fuel L c ρ e (S i) r.

Hint Constructors cbstep : core.
Hint Constructors cbstep_fuel : core.

Scheme cbstep_ind' := Minimality for cbstep Sort Prop
with cbstep_fuel_ind' := Minimality for cbstep_fuel Sort Prop.

Lemma cbstep_deterministic_aux v v' {L c ρ e i i' r r'}:
  cbstep L c ρ e i r ->
  cbstep L c ρ e i' r' ->
  r = CRes v ->
  r' = CRes v' ->
  (v = v' /\ i = i').
Proof.
  intros H.
  generalize dependent v'.
  generalize dependent r'.
  generalize dependent i'.
  generalize dependent v.
  induction H using cbstep_ind' with (P := fun c ρ e i r =>
                                             forall v i' r' v',
                                               cbstep L c ρ e i' r' ->
                                               r = CRes v -> r' = CRes v' ->
                                               v = v' /\ i = i')
                                     (P0 := fun c ρ e i r =>
                                              forall v i' r' v',
                                                cbstep_fuel L c ρ e i' r' ->
                                                r = CRes v -> r' = CRes v' ->
                                                v = v' /\ i = i');
    intros; subst.
  - inv H0; inv H1; invc; auto.
  - inv H0.
    edestruct IHcbstep; eauto; subst.
  - inv H4; invc.
    edestruct IHcbstep; eauto.
  - inv H5; invc.
    edestruct IHcbstep; eauto.
    subst.
    edestruct IHcbstep0; eauto.
  - inv H5.
  - inv H1; invc.
    edestruct IHcbstep; eauto.
  - inv H3; invc.
    edestruct IHcbstep; eauto.
  - inv H3; invc.
    destruct (find_tag_deterministic H0 H8); subst.
    edestruct IHcbstep; eauto.
  - inv H0.
  - inv H0;
      edestruct IHcbstep; eauto.
Qed.

Lemma cbstep_fuel_deterministic_aux v v' {L c ρ e i i' r r'}:
  cbstep_fuel L c ρ e i r ->
  cbstep_fuel L c ρ e i' r' ->
  r = CRes v ->
  r' = CRes v' ->
  (v = v' /\ i = i').
Proof.
  intros.
  inv H; inv H0; try discriminate.
  edestruct (cbstep_deterministic_aux v v' H3 H); eauto.
Qed.

Theorem cbstep_deterministic v v' {L c ρ e i i'}:
  cbstep L c ρ e i (CRes v) ->
  cbstep L c ρ e i' (CRes v') ->
  (v = v' /\ i = i').
Proof. srun eauto using cbstep_deterministic_aux. Qed.

Theorem cbstep_fuel_deterministic v v' {L c ρ e i i'}:
  cbstep_fuel L c ρ e i (CRes v) ->
  cbstep_fuel L c ρ e i' (CRes v') ->
  (v = v' /\ i = i').
Proof. srun eauto using cbstep_fuel_deterministic_aux. Qed.

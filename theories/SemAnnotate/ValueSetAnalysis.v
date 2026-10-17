From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From SemAnnotate Require Import LabeledANF.

(* A Simple Value Set Analysis *)
(* Please note that everything is *static*. *)

(* --------------------------------------------------------------- *)
(* The unknown/foreign side                                          *)
(* --------------------------------------------------------------- *)

(* Everything the analysis does not see is summarised by two dedicated labels:
     - [l_top_intro]: *every* value that originates outside the analysed unit
     - [l_top_elim]: *every* elimination performed outside the analysed unit *)
Parameter l_top_intro l_top_elim : label.

(* Interaction Set *)
(* Each pair has the format (l_intro, l_elim). *)
Definition ainteraction : Type := (label * label).
Definition ainteractions := Ensemble ainteraction.

(* Internal Label Set *)
Definition internals : Type := labels.

(* Reachable labels for the (uncolored) statically predicted interactions *)
(* `areachable I l` is the set of labels connected to `l` by a chain of
   interactions in I, in either direction. *)
Inductive areachable (I : ainteractions) (l : label) : labels :=
| AReachable_refl :
  areachable I l l

| AReachable_interact_l :
  forall l',
    (l, l') \in I ->
    areachable I l l'

| AReachable_interact_r :
  forall l',
    (l', l) \in I ->
    areachable I l l'

| AReachable_step :
  forall l' l'',
    areachable I l l' ->
    areachable I l' l'' ->
    areachable I l l''.

Hint Constructors areachable : core.

(* `l` is internal if it never interacts with the unknown side, i.e. neither
   `l_top_intro` nor `l_top_elim` is reachable from it. *)
Definition ainternal (I : ainteractions) (l : label) : Prop :=
  ~ (l_top_intro \in areachable I l) /\ ~ (l_top_elim \in areachable I l).

(* All the internal labels in `I` *)
Definition ainternals_of (I : ainteractions) : internals :=
  fun l => ainternal I l.

(* Closure Property *)
(* `U` is closed under reachable interactions `I` *)
Definition ainternals_closed (U : internals) (I : ainteractions) : Prop :=
  forall l l',
    (l \in U) ->
    (l' \in (areachable I l)) ->
    (l' \in U).

Lemma ainternals_of_closed I :
  ainternals_closed (ainternals_of I) I.
Proof.
  unfold ainternals_closed, ainternals_of, ainternal, Ensembles.In.
  intros l l' [Hintro Helim] Hreach.
  (* anything reachable from `l'` is also reachable from `l` *)
  split.
  - intros Hintro'.
    apply Hintro.
    eapply AReachable_step; [exact Hreach | exact Hintro'].
  - intros Helim'.
    apply Helim.
    eapply AReachable_step; [exact Hreach | exact Helim'].
Qed.

(* --------------------------------------------------------------- *)
(* Abstract values                                                   *)
(* --------------------------------------------------------------- *)

(* An abstract value is an allocation site, summarised:
     - a closure is its introduction label together with its (syntactic) code;
     - a constructor is its introduction label, its tag, and the *variables*
       holding its fields -- the fields themselves are read back through the
       abstract environment, which is what makes the domain finite;
     - [AVtop] is the single abstract value standing for everything unknown:
       any foreign value, and any of our values that has escaped to the
       context.  Its introduction clabel is [l_top_intro]. *)
Inductive aval : Type :=
| AVtop : aval
| AVfun : label -> var -> list var -> exp -> aval.

Definition avals := Ensemble aval.

Definition label_of (av : aval) : label :=
  match av with
  | AVtop => l_top_intro
  | AVfun l _ _ _ => l
  end.

(* Abstract environment: one value set per variable (monovariant). *)
Definition aenv := var -> avals.

(* Abstract return sets, keyed by the closure's introduction label: a
     function body is analysed once, at its definition site, and everything it
     may return is collected in [aret] at that site. *)
Definition aret := label -> avals.

(* --------------------------------------------------------------- *)
(* The analysis result                                             *)
(* --------------------------------------------------------------- *)
Record analysis_info : Type :=
  mk_analysis_info {
      ai_env : aenv;           (* value sets                                 *)
      ai_ret : aret;           (* return sets                                *)
      ai_esc : avals;          (* values that may escape to the context      *)
      ai_int : ainteractions   (* statically predicted interactions          *)
    }.

(* What the context may do with a value we handed it.  [ai_esc] has to be closed
     under this: the context can eliminate an escaped value, call an escaped
     closure with arbitrary (hence unknown) arguments and keep whatever it
     returns, and project out of an escaped constructor. *)
Definition escapes_ok (ai : analysis_info) : Prop :=
  (forall av,
      (av \in ai_esc ai) ->
      ((label_of av, l_top_elim) \in ai_int ai)) /\
    (forall l f xs e,
        (AVfun l f xs e \in ai_esc ai) ->
        (forall x, List.In x xs -> (AVtop \in ai_env ai x)) /\
          (ai_ret ai l \subset ai_esc ai)).
(* /\
    (forall l t ys,
        (AVconstr l t ys \in Esc) ->
        forall y, List.In y ys -> (A y \subset Esc)).*)

(* --------------------------------------------------------------- *)
(* The abstract semantics                                            *)
(* --------------------------------------------------------------- *)

(* [acheck ai e R] reads: the analysis result [ai] is acceptable
     for [e] and [R] over-approximates the values [e] may return.
     This is the "abstract semantics": a declarative
     constraint system rather than a fixpoint computation, so any solver that
     produces an [analysis_info] may be plugged in and checked against it. *)
Inductive acheck (ai : analysis_info) : exp -> avals -> Prop :=
| Acheck_ret :
  forall {x R},
    (ai_env ai x \subset R) ->
    acheck ai (Eret x) R

| Acheck_fun :
  forall {f l xs e k R},
    (* the closure introduced here flows into [f] *)
    (AVfun l f xs e \in ai_env ai f) ->
    (* its body is analysed once, here, and returns into [ai_ret ai l] *)
    acheck ai e (ai_ret ai l) ->
    acheck ai k R ->
    acheck ai (Efun f l xs e k) R

| Acheck_app :
  forall {f l xs R},
    (* the call site (c, l) eliminates everything that reaches [f] *)
    (forall av, (av \in ai_env ai f) -> ((label_of av, l) \in ai_int ai)) ->
    (* known callee: arguments flow to parameters, results flow out *)
    (forall l' f' xs' e',
        (AVfun l' f' xs' e' \in ai_env ai f) ->
        length xs = length xs' /\
          (AVfun l' f' xs' e' \in ai_env ai f') /\
          Forall2 (fun x x' => ai_env ai x \subset ai_env ai x') xs xs' /\
          (ai_ret ai l' \subset R)) ->
    (* unknown callee: the arguments escape and the result is unknown *)
    ((AVtop \in ai_env ai f) ->
     Forall (fun x => ai_env ai x \subset ai_esc ai) xs /\
       (AVtop \in R)) ->
    acheck ai (Eapp f l xs) R.

Hint Constructors acheck : core.

(* Checking Semantics With Respect to Colored Label Pair Set *)

(* Color *)
Definition color := nat.
Definition colors := Ensemble nat.

(* Colored Label *)
Definition clabel : Type := (color * label).
Definition clabels : Type := Ensemble clabel.

(* Interaction Set *)
(* Each pair has the format (l_intro, l_elim). *)
Definition interaction : Type := (clabel * clabel).
Definition interactions := Ensemble interaction.

(* Reachable label pairs *)
(* `reachable I cl` is the set of colored labels connected to `cl` by a chain of
   interactions in I, in either direction (transitive closure of `cinteract`). *)
Inductive reachable (I : interactions) (cl : clabel) : clabels :=
| Reachable_refl :
  reachable I cl cl

| Reachable_interact_l :
  forall cl',
    (cl, cl') \in I ->
    reachable I cl cl'

| Reachable_interact_r :
  forall cl',
    (cl', cl) \in I ->
    reachable I cl cl'

| Reachable_step :
  forall cl' cl'',
    reachable I cl cl' ->
    reachable I cl' cl'' ->
    reachable I cl cl''.

Hint Constructors reachable : core.

Definition colors_of (L : clabels) : colors :=
  fun c => exists l, (c, l) \in L.

(* `cl` has only internal interaction if the set of reachable colors is exactly the empty set or the singleton set {c}. *)
Definition internal (I : interactions) (cl : clabel) : Prop :=
  match cl with
  | (c, _) => (colors_of (reachable I cl)) \subset [ set c ]
  end.

(* `cl` has external interaction if it is not internal or it interacts with some other color. *)
Definition external (I : interactions) (cl : clabel) : Prop :=
  ~ internal I cl.

(* All the internal labels in `I` with respect color `c` *)
Definition internals_of (c : color) (I : interactions) : internals :=
  fun l => internal I (c, l).

(* Internal with respect to `U` paired with its corresponding color `c` *)
Definition cinternal (U : internals) (c : color) (cl : clabel) : Prop :=
  fst cl = c /\ (snd cl \in U).

(* Closure Property *)
(* `U` paired with `c` is closed under reachable interactions `I`.
    Note that `U` is not necessarily the most precise internal events in `I`. *)
Definition internals_closed (U : internals) (c : color) (I : interactions) : Prop :=
  forall l cl',
    (l \in U) ->
    (cl' \in (reachable I (c, l))) ->
    cinternal U c cl'.

Lemma internals_of_closed c I :
  internals_closed (internals_of c I) c I.
Proof.
  unfold internals_closed, cinternal, internals_of, internal, colors_of,
    Ensembles.Included, Ensembles.In.
  intros l [c' l'] Hint Hreach.
  cbn in *.
  (* `(c', l')` is reachable from `(c, l)`, so its color is `c` *)
  pose proof (Hint c' (ex_intro _ l' Hreach)) as Hc'.
  inv Hc'.
  split; [reflexivity |].
  (* anything reachable from `(c, l')` is also reachable from `(c, l)` *)
  intros c'' [l'' Hreach'].
  apply Hint.
  exists l''.
  eapply Reachable_step; [exact Hreach | exact Hreach'].
Qed.

(* Edge-wise characterization of Closure *)
(* `U` respects `I` when every *single* interaction of `I` joins two colored
   labels that are either both internal to the unit wearing `c` or both not:
   reachability can then never leave the unit.  This is the form that the
   checking semantics produces one interaction at a time. *)
Definition interactions_respect (U : internals) (c : color) (I : interactions) : Prop :=
  forall cl_i cl_e,
    ((cl_i, cl_e) \in I) ->
    (cinternal U c cl_i <-> cinternal U c cl_e).

Lemma interactions_respect_union U c I1 I2 :
  interactions_respect U c I1 ->
  interactions_respect U c I2 ->
  interactions_respect U c (I1 :|: I2).
Proof.
  unfold interactions_respect.
  intros H1 H2 cl_i cl_e Hin.
  inv Hin.
  - match goal with [HI : _ \in I1 |- _] => exact (H1 cl_i cl_e HI) end.
  - match goal with [HI : _ \in I2 |- _] => exact (H2 cl_i cl_e HI) end.
Qed.

(* Reachability starting from an internal label never leaves the unit --- in particular it never changes color. *)
Lemma interactions_respect_reachable {U c I} :
  interactions_respect U c I ->
  forall cl cl',
    (cl' \in reachable I cl) ->
    cinternal U c cl ->
    cinternal U c cl'.
Proof.
  unfold interactions_respect.
  intros Hres cl cl' Hreach.
  induction Hreach as [x | x y Hin | x y Hin | x y z Hxy IHxy Hyz IHyz].
  - intros Hx; exact Hx.
  - intros Hx; exact (proj1 (Hres x y Hin) Hx).
  - intros Hx; exact (proj2 (Hres y x Hin) Hx).
  - intros Hx; apply IHyz, IHxy, Hx.
Qed.

Lemma interactions_respect_closed U c I :
  interactions_respect U c I ->
  internals_closed U c I.
Proof.
  unfold internals_closed, cinternal.
  intros Hres l cl' HlU Hreach.
  pose proof (interactions_respect_reachable Hres (c, l) cl' Hreach
                (conj eq_refl HlU)) as [Hc Hl].
  fcrush.
Qed.

Lemma internals_closed_respect U c I :
  internals_closed U c I ->
  interactions_respect U c I.
Proof.
  unfold internals_closed, interactions_respect, cinternal.
  intros Hclosed cl_i cl_e Hin.
  split; intros [Heq Hc].
  - hauto lq: on use: surjective_pairing, Reachable_interact_l unfold: Ensembles.In, snd, clabel.
  - qauto use: surjective_pairing, Reachable_interact_r unfold: Ensembles.In, snd, clabel.
Qed.

Theorem internals_closed_iff_respect U c I :
  internals_closed U c I <-> interactions_respect U c I.
Proof.
  split; [exact (internals_closed_respect U c I)
         | exact (interactions_respect_closed U c I)].
Qed.

Lemma internals_of_respect c I :
  interactions_respect (internals_of c I) c I.
Proof. eauto using internals_closed_respect, internals_of_closed. Qed.


Lemma interactions_respect_internal {U c I} :
  interactions_respect U c I ->
  forall cl,
    cinternal U c cl ->
    internal I cl.
Proof.
  intros Hres cl Hcint.
  destruct cl as [c0 l0].
  destruct Hcint as [Hc Hl]; simpl in Hc, Hl; subst c0.
  unfold internal, colors_of, Ensembles.Included, Ensembles.In.
  intros x [l1 Hreach].
  pose proof (interactions_respect_reachable Hres (c, l0) (x, l1) Hreach
                (conj eq_refl Hl)) as [Hx Hl1].
  simpl in Hx; subst x.
  constructor.
Qed.

(* Soundness transfers along a single interaction, in either direction. *)
Lemma internals_repsect_sound_l {U c I} :
  interactions_respect U c I ->
  forall cl cl',
    ((cl, cl') \in I) ->
    cinternal U c cl ->
    internal I cl'.
Proof.
  intros Hres cl cl' Hin Hcint.
  exact (interactions_respect_internal Hres cl' (proj1 (Hres cl cl' Hin) Hcint)).
Qed.

Lemma internals_repsect_sound_r {U c I} :
  interactions_respect U c I ->
  forall cl cl',
    ((cl, cl') \in I) ->
    cinternal U c cl' ->
    internal I cl.
Proof.
  intros Hres cl cl' Hin Hcint.
  exact (interactions_respect_internal Hres cl (proj2 (Hres cl cl' Hin) Hcint)).
Qed.

Lemma interactions_respect_empty U c :
  interactions_respect U c (Empty_set interaction).
Proof.
  unfold interactions_respect, Ensembles.In.
  intros cl_i cl_e Hin; destruct Hin.
Qed.

Lemma interactions_respect_add U c cl_i cl_e I :
  (cinternal U c cl_i <-> cinternal U c cl_e) ->
  interactions_respect U c I ->
  interactions_respect U c ((cl_i, cl_e) |: I).
Proof.
  unfold interactions_respect.
  intros Hiff Hres cl_i' cl_e' Hin.
  inv Hin.
  - match goal with [Hsing : _ \in [set _] |- _] => inv Hsing end.
    assumption.
  - match goal with [HI : _ \in I |- _] => exact (Hres cl_i' cl_e' HI) end.
Qed.

Lemma interactions_respect_Same_set U U' c I :
  U <--> U' ->
  interactions_respect U' c I ->
  interactions_respect U c I.
Proof.
  unfold interactions_respect, cinternal, Ensembles.In.
  intros [Hsub Hsub'] Hres cl_i cl_e Hin.
  split; intros [Hc Hmem].
  - destruct (proj1 (Hres cl_i cl_e Hin) (conj Hc (Hsub _ Hmem))) as [Hc' Hmem'].
    exact (conj Hc' (Hsub' _ Hmem')).
  - destruct (proj2 (Hres cl_i cl_e Hin) (conj Hc (Hsub _ Hmem))) as [Hc' Hmem'].
    exact (conj Hc' (Hsub' _ Hmem')).
Qed.

(* Tagged Value *)
Inductive ctag A : Type :=
| CTAG : analysis_info -> clabel -> A -> ctag A.

Hint Constructors ctag : core.

(* Value *)
Inductive cval : Type :=
| CVfun : var -> M.t (ctag cval) -> list var -> exp -> cval
| CVconstr : ctor_tag -> list (ctag cval) -> cval.

Hint Constructors cval : core.

Definition clval := ctag cval.

Definition CTag A c l cv := CTAG cval A (c, l) cv.

(* Environment *)
Definition cenv := M.t clval.

(* Result *)
Inductive cres : Type :=
| COOT
| CRes : clval -> cres.

Hint Constructors cres : core.

(* Approximation *)
(* `approx_val av v`: the abstract value `av` over-approximates the concrete
   value `v`, with respect to the analysis result carried by the tag of `v`.
   - [AVtop] stands for everything unknown, so it approximates any value;
   - otherwise `av` must share the introduction label of `v` and approximate
     the untagged value under the tag's analysis result. *)
Inductive approx_val : aval -> clval -> Prop :=
| Approx_top :
  forall v,
    approx_val AVtop v

| Approx_TAG :
  forall A c l av v,
    label_of av = l ->
    approx_val' A av v ->
    approx_val av (CTag A c l v)

(* A closure is approximated by its own allocation site, provided that its
   captured environment is approximated by the abstract environment of `A`. *)
with approx_val' : analysis_info -> aval -> cval -> Prop :=
| Approx_CVfun :
  forall A l f ρ xs e,
    approx_env (ai_env A) ρ ->
    approx_val' A (AVfun l f xs e) (CVfun f ρ xs e)

(* Every value bound in `ρ` is approximated by some abstract value in the value
   set of its variable. *)
with approx_env : aenv -> cenv -> Prop :=
| Approx_env :
  forall aenv ρ,
    (forall x v,
        ρ ! x = Some v ->
        exists av, (av \in aenv x) /\ approx_val av v) ->
    approx_env aenv ρ.

Hint Constructors approx_val : core.
Hint Constructors approx_val' : core.
Hint Constructors approx_env : core.

Scheme approx_val_mut := Induction for approx_val Sort Prop
with approx_val'_mut := Induction for approx_val' Sort Prop
with approx_env_mut := Induction for approx_env Sort Prop.

Definition approx_vals (avs : avals) (v : clval) : Prop :=
  forall av, av \in avs -> approx_val av v.

(* A result is approximated by `R` if it is out of time, or returns a value
   approximated by some abstract value in `R`. *)
Inductive approx_res : avals -> cres -> Prop :=
| Approx_OOT :
  forall R,
    approx_res R COOT

| Approx_res :
  forall R av v,
    (av \in R) ->
    approx_val av v ->
    approx_res R (CRes v).

Hint Constructors approx_res : core.

(* Checking Semantics based on the Collecting Semantics *)
(* This semantics specifies the validity of the analysis result, `A`. *)
Inductive cbstep (A : analysis_info) (c : color) (ρ : cenv) : exp -> fuel -> avals -> cres -> Prop :=
| Cbstep_ret :
  forall {x v Rs},
    M.get x ρ = Some v ->
    (forall av, av \in Rs -> approx_val av v) ->
    cbstep A c ρ (Eret x) 0 Rs (CRes v)

| Cbstep_fun :
  forall {f l xs e k i Rs r},
    cbstep_fuel A c (M.set f (CTag A c l (CVfun f ρ xs e)) ρ) k i Rs r ->
    approx_vals (ai_env A f) (CTag A c l (CVfun f ρ xs e)) ->
    cbstep A c ρ (Efun f l xs e k) i Rs r

| Cbstep_app_External :
  forall {A' f f' c' l l' xs ρ' xs' e vs ρ'' i Rs r},
    M.get f ρ = Some (CTag A' c' l' (CVfun f' ρ' xs' e)) ->
    c <> c' -> (* foreign call *)
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (CTag A' c' l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    cbstep_fuel A' c' ρ'' e i Rs r ->
    cbstep A c ρ (Eapp f l xs) i Rs r

| Cbstep_app_Internal :
  forall {A' f f' l l' xs ρ' xs' e vs ρ'' i Rs r},
    M.get f ρ = Some (CTag A' c l' (CVfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (CTag A' c l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    cbstep_fuel A' c ρ'' e i Rs r ->
    cbstep A c ρ (Eapp f l xs) i Rs r

with cbstep_fuel (A : analysis_info) (c : color) (ρ : cenv) : exp -> fuel -> avals -> cres -> Prop :=
| CbstepF_OOT :
  forall {e Rs},
    cbstep_fuel A c ρ e 0 Rs COOT

| CbstepF_Step :
  forall {e i Rs r},
    cbstep A c ρ e i Rs r ->
    approx_res Rs r ->
    cbstep_fuel A c ρ e (S i) Rs r.

Hint Constructors cbstep : core.
Hint Constructors cbstep_fuel : core.

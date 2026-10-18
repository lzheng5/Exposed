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
(* Please note that everything related to the analysis is *static*. *)

(* --------------------------------------------------------------- *)
(* The Unknown/Foreign Side                                          *)
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
Record analysis_result : Type :=
  mk_analysis_result {
      ai_env : aenv;           (* value sets                                 *)
      ai_ret : aret;           (* return sets                                *)
      ai_esc : avals;          (* values that may escape to the context      *)
      ai_int : ainteractions   (* statically predicted interactions          *)
    }.

(* What the context may do with a value we handed it.  [ai_esc] has to be closed
     under this: the context can eliminate an escaped value, call an escaped
     closure with arbitrary (hence unknown) arguments and keep whatever it
     returns, and project out of an escaped constructor. *)
Definition escapes_ok (A : analysis_result) : Prop :=
  (forall av,
      (av \in ai_esc A) ->
      ((label_of av, l_top_elim) \in ai_int A)) /\
    (forall l f xs e,
        (AVfun l f xs e \in ai_esc A) ->
        (forall x, List.In x xs -> (AVtop \in ai_env A x)) /\
          (ai_ret A l \subset ai_esc A)).
(* /\
    (forall l t ys,
        (AVconstr l t ys \in Esc) ->
        forall y, List.In y ys -> (A y \subset Esc)).*)

(* --------------------------------------------------------------- *)
(* The Abstract Semantics                                            *)
(* --------------------------------------------------------------- *)

(* [acheck A e R] reads: the analysis result [A] is acceptable
     for [e] and [R] over-approximates the values [e] may return.
     This is the "abstract semantics": a declarative
     constraint system rather than a fixpoint computation, so any solver that
     produces an [analysis_result] may be plugged in and checked against it. *)
Inductive acheck (A : analysis_result) : exp -> avals -> Prop :=
| Acheck_ret :
  forall {x R},
    (ai_env A x \subset R) ->
    acheck A (Eret x) R

| Acheck_fun :
  forall {f l xs e k R},
    (* the closure introduced here flows into [f] *)
    (AVfun l f xs e \in ai_env A f) ->
    (* its body is analysed once, here, and returns into [ai_ret A l] *)
    acheck A e (ai_ret A l) ->
    acheck A k R ->
    acheck A (Efun f l xs e k) R

| Acheck_app :
  forall {f l xs R},
    (* the call site (c, l) eliminates everything that reaches [f] *)
    (forall av, (av \in ai_env A f) -> ((label_of av, l) \in ai_int A)) ->
    (* internal call: arguments flow to parameters, results flow out *)
    (forall l' f' xs' e',
        (AVfun l' f' xs' e' \in ai_env A f) ->
        length xs = length xs' /\
          (AVfun l' f' xs' e' \in ai_env A f') /\
          Forall2 (fun x x' => ai_env A x \subset ai_env A x') xs xs' /\
          (ai_ret A l' \subset R)) ->
    (* foreign call: the arguments escape and the result is unknown *)
    ((AVtop \in ai_env A f) ->
     Forall (fun x => ai_env A x \subset ai_esc A) xs /\
       (AVtop \in R)) ->
    acheck A (Eapp f l xs) R.

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

Lemma empty_internals_closed c I :
  internals_closed (Empty_set _) c I.
Proof. unfold internals_closed. sfirstorder. Qed.

Lemma internals_closed_empty U c :
  internals_closed U c (Empty_set interaction).
Proof.
  unfold internals_closed, cinternal, Ensembles.In.
  intros l cl' HclU Hreach.
  assert (Heq : cl' = (c, l)).
  { clear HclU.
    induction Hreach as [| ? Hin | ? Hin | ? ? ? IH1 ? IH2]; sfirstorder. }
  fcrush.
Qed.

Lemma internals_closed_equivalent U c I I' :
  I <--> I' ->
  (internals_closed U c I <-> internals_closed U c I').
Proof.
  intros [Hsub Hsub'].
  assert (Hreach : forall (J J' : interactions),
             (forall p, p \in J -> p \in J') ->
             forall cl cl', cl' \in reachable J cl -> cl' \in reachable J' cl).
  { intros J J' HJ cl cl' Hr.
    induction Hr as [x | x y Hin | x y Hin | x y z H1 IH1 H2 IH2];
      [ apply Reachable_refl
      | apply Reachable_interact_l; apply HJ; exact Hin
      | apply Reachable_interact_r; apply HJ; exact Hin
      | eapply Reachable_step; eauto ]. }
  unfold internals_closed, cinternal.
  split; intros Hclosed l cl' HlU Hr.
  - eapply Hclosed; [exact HlU |].
    eapply (Hreach I' I); eauto.
  - eapply Hclosed; [exact HlU |].
    eapply (Hreach I I'); eauto.
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
| CTAG : analysis_result -> clabel -> A -> ctag A.

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
with approx_val' : analysis_result -> aval -> cval -> Prop :=
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

(* `v` is approximated by some abstract value in `avs`. *)
Definition approx_vals (avs : avals) (v : clval) : Prop :=
  exists av, (av \in avs) /\ approx_val av v.

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

(* `approx_int c AI I`: the static interactions `AI` of the unit wearing color
   `c` over-approximate the collected interactions `I`, as seen from that unit.
   `l_top_intro` and `l_top_elim` approximate all foreign interactions:
   - an internal interaction is predicted as it is;
   - one of our values eliminated by the context is predicted as eliminated
     at `l_top_elim`;
   - a foreign value eliminated by us is predicted as introduced at
     `l_top_intro`;
   - interactions between other units are not constrained. *)
Definition approx_int (c : color) (AI : ainteractions) (I : interactions) : Prop :=
  forall c1 l1 c2 l2,
    (((c1, l1), (c2, l2)) \in I) ->
    (c1 = c -> c2 = c -> (l1, l2) \in AI) /\
    (c1 = c -> c2 <> c -> (l1, l_top_elim) \in AI) /\
    (c1 <> c -> c2 = c -> (l_top_intro, l2) \in AI).

Lemma approx_int_respect c AI I :
  approx_int c AI I ->
  interactions_respect (ainternals_of AI) c I.
Proof.
  unfold approx_int, interactions_respect, cinternal.
  intros Happrox [c1 l1] [c2 l2] Hin.
  pose proof (Happrox c1 l1 c2 l2 Hin) as [Hcc [Hce Hec]].
  pose proof (ainternals_of_closed AI) as Hclosed.
  unfold ainternals_closed in Hclosed.
  split; intros [Hc HU].
  - (* the introduction site is internal *)
    destruct (Nat.eq_dec c2 c) as [Hc2 | Hc2].
    + (* internal interaction: `l2` is reachable from `l1` *)
      split; [exact Hc2 |].
      eapply Hclosed; [exact HU |].
      unfold Ensembles.In.
      apply AReachable_interact_l.
      exact (Hcc Hc Hc2).
    + (* eliminated by the context: `l1` would reach `l_top_elim` *)
      exfalso.
      unfold ainternals_of, ainternal, Ensembles.In in HU.
      destruct HU as [_ Helim].
      apply Helim.
      apply AReachable_interact_l.
      exact (Hce Hc Hc2).
  - (* the elimination site is internal *)
    destruct (Nat.eq_dec c1 c) as [Hc1 | Hc1].
    + (* internal interaction: `l1` is reachable from `l2` *)
      split; [exact Hc1 |].
      eapply Hclosed; [exact HU |].
      unfold Ensembles.In.
      apply AReachable_interact_r.
      exact (Hcc Hc1 Hc).
    + (* foreign value eliminated by us: `l2` would reach `l_top_intro` *)
      exfalso.
      unfold ainternals_of, ainternal, Ensembles.In in HU.
      destruct HU as [Hintro _].
      apply Hintro.
      apply AReachable_interact_r.
      exact (Hec Hc1 Hc).
Qed.

Corollary approx_int_closed c AI I :
  approx_int c AI I ->
  internals_closed (ainternals_of AI) c I.
Proof. eauto using approx_int_respect, interactions_respect_closed. Qed.

(* Checking Semantics based on the Collecting Semantics *)
(* This semantics dynamically validates the analysis result, `A`.
   The collected interactions are validated against `ai_int A` once, in
   `CbstepF_Step`, which covers every interaction produced underneath it,
   including the call edge added by `Cbstep_app_*`. *)
Inductive cbstep (A : analysis_result) (c : color) (ρ : cenv) : exp -> fuel -> avals -> cres -> interactions -> Prop :=
| Cbstep_ret :
  forall {x v Rs},
    M.get x ρ = Some v ->
    cbstep A c ρ (Eret x) 0 Rs (CRes v) (Empty_set _)

| Cbstep_fun :
  forall {f l xs e k i Rs r I},
    cbstep_fuel A c (M.set f (CTag A c l (CVfun f ρ xs e)) ρ) k i Rs r I ->
    approx_vals (ai_env A f) (CTag A c l (CVfun f ρ xs e)) ->
    cbstep A c ρ (Efun f l xs e k) i Rs r I

(* Foreign call: dynamic counterpart of the unknown-callee branch of `Acheck_app`,
   validated from both sides.  The caller (`A`) sees an unknown value being
   eliminated and its arguments escaping; the callee (`A'`) sees one of its
   escaped closures being eliminated by the context. *)
| Cbstep_app_External :
  forall {A' f f' c' l l' xs ρ' xs' e vs ρ'' i Rs r I},
    M.get f ρ = Some (CTag A' c' l' (CVfun f' ρ' xs' e)) ->
    c <> c' ->

    (* callee side: the closure has escaped and is eliminated by the context
       (the caller side, `(l_top_intro, l)`, is checked by `CbstepF_Step`) *)
    approx_vals (ai_esc A') (CTag A' c' l' (CVfun f' ρ' xs' e)) ->
    ((l', l_top_elim) \in ai_int A') ->

    (* caller side: the arguments escape to the context *)
    get_list xs ρ = Some vs ->
    Forall (approx_vals (ai_esc A)) vs ->

    (* callee side: the (unknown) arguments flow to the parameters *)
    set_lists xs' vs (M.set f' (CTag A' c' l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    approx_env (ai_env A') ρ'' ->

    (* the body is validated against the callee's own analysis result and
       returns into `ai_ret A' l'` *)
    cbstep_fuel A' c' ρ'' e i (ai_ret A' l') r I ->

    cbstep A c ρ (Eapp f l xs) i Rs r (((c', l'), (c, l)) |: I)

(* Internal call: dynamic counterpart of the known-callee branch of
   `Acheck_app`.  The callee wears the caller's color, so it belongs to the
   same unit and is validated against the same analysis result `A`. *)
| Cbstep_app_Internal :
  forall {f f' l l' xs ρ' xs' e vs ρ'' i Rs r I},
    M.get f ρ = Some (CTag A c l' (CVfun f' ρ' xs' e)) ->

    (* the arguments flow to the parameters *)
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (CTag A c l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    approx_env (ai_env A) ρ'' ->

    (* the body returns into `ai_ret A l'` *)
    cbstep_fuel A c ρ'' e i (ai_ret A l') r I ->

    cbstep A c ρ (Eapp f l xs) i Rs r (((c, l'), (c, l)) |: I)

with cbstep_fuel (A : analysis_result) (c : color) (ρ : cenv) : exp -> fuel -> avals -> cres -> interactions -> Prop :=
| CbstepF_OOT :
  forall {e Rs},
    cbstep_fuel A c ρ e 0 Rs COOT (Empty_set _)

| CbstepF_Step :
  forall {e i Rs r I},
    cbstep A c ρ e i Rs r I ->
    approx_res Rs r ->
    approx_int c (ai_int A) I ->
    cbstep_fuel A c ρ e (S i) Rs r I.

Hint Constructors cbstep : core.
Hint Constructors cbstep_fuel : core.

Scheme cbstep_ind' := Minimality for cbstep Sort Prop
with cbstep_fuel_ind' := Minimality for cbstep_fuel Sort Prop.

Lemma cbstep_deterministic_aux v v' {A I I' c ρ e i i' Rs r r'}:
  cbstep A c ρ e i Rs r I ->
  cbstep A c ρ e i' Rs r' I' ->
  r = CRes v ->
  r' = CRes v' ->
  (v = v' /\ i = i' /\ I <--> I').
Proof.
  intros H.
  generalize dependent v'.
  generalize dependent r'.
  generalize dependent i'.
  generalize dependent v.
  generalize dependent I'.
  induction H using cbstep_ind' with (P := fun A c ρ e i Rs r I =>
                                             forall I' v i' r' v',
                                               cbstep A c ρ e i' Rs r' I' ->
                                               r = CRes v -> r' = CRes v' ->
                                               v = v' /\ i = i' /\ I <--> I')
                                     (P0 := fun A c ρ e i Rs r I =>
                                              forall I' v i' r' v',
                                                cbstep_fuel A c ρ e i' Rs r' I' ->
                                                r = CRes v -> r' = CRes v' ->
                                                v = v' /\ i = i' /\ I <--> I');
    intros; subst.
  - inv H0; inv H1; invc; fcrush.
  - inv H1.
    edestruct IHcbstep; eauto; subst.
  - inv H8; invc.
    edestruct IHcbstep as [Heqv [Heqi HeqI]]; eauto; subst;
      hauto lq: on use: Extensionality_Ensembles unfold: Same_set, Included, interactions.
    fcrush.
  - inv H4; invc.
    fcrush.
    edestruct IHcbstep as [Heqv [Heqi HeqI]]; eauto; subst;
      hauto lq: on use: Extensionality_Ensembles unfold: Same_set, Included, interactions.
  - fcrush.
  - inv H2;
      edestruct IHcbstep as [Heqv [Heqi HeqI]]; eauto.
Qed.

Lemma cbstep_fuel_deterministic_aux v v' {A I I' c ρ e i i' Rs r r'}:
  cbstep_fuel A c ρ e i Rs r I ->
  cbstep_fuel A c ρ e i' Rs r' I' ->
  r = CRes v ->
  r' = CRes v' ->
  (v = v' /\ i = i' /\ I <--> I').
Proof.
  intros Hstep Hstep' Heqr Heqr'; subst.
  inv Hstep; inv Hstep'.
  edestruct (cbstep_deterministic_aux v v' H H2) as [Heqv [Heqi HeqI]];
    subst; eauto.
Qed.

Theorem cbstep_deterministic v v' {A I I' c ρ e Rs i i'}:
  cbstep A c ρ e i Rs (CRes v) I ->
  cbstep A c ρ e i' Rs (CRes v') I' ->
  (v = v' /\ i = i' /\ I <--> I').
Proof. srun eauto using cbstep_deterministic_aux. Qed.

Theorem cbstep_fuel_deterministic v v' {A I I' c ρ e Rs i i'}:
  cbstep_fuel A c ρ e i Rs (CRes v) I ->
  cbstep_fuel A c ρ e i' Rs (CRes v') I' ->
  (v = v' /\ i = i' /\ I <--> I').
Proof. srun eauto using cbstep_fuel_deterministic_aux. Qed.

(* Analysis Context *)
Definition analysis_context := color -> analysis_result.

(* Every unit's analysis result must be closed under what the context may do
   with the values it hands out. *)
Definition analysis_context_escape_ok (Θ : analysis_context) : Prop :=
  forall c, escapes_ok (Θ c).

(* Well-formed Value and Environment w.r.t. an Analysis Context *)
(* Every tag occurring in a value, or in an environment, assigns to its color
   the analysis result that `Θ` prescribes for it. *)
Inductive wf_cval (Θ : analysis_context) : clval -> Prop :=
| WF_TAG :
  forall A c l v,
    Θ c = A ->
    wf_cval' Θ v ->
    wf_cval Θ (CTag A c l v)

with wf_cval' (Θ : analysis_context) : cval -> Prop :=
| WF_CVfun :
  forall f ρ xs e,
    wf_cenv Θ ρ ->
    wf_cval' Θ (CVfun f ρ xs e)

| WF_CVconstr_nil :
  forall t,
    wf_cval' Θ (CVconstr t [])

| WF_CVconstr :
  forall t v vs,
    wf_cval Θ v ->
    wf_cval' Θ (CVconstr t vs) ->
    wf_cval' Θ (CVconstr t (v :: vs))

with wf_cenv (Θ : analysis_context) : cenv -> Prop :=
| WF_cenv :
  forall ρ,
    (forall x v, ρ ! x = Some v -> wf_cval Θ v) ->
    wf_cenv Θ ρ.

Hint Constructors wf_cval : core.
Hint Constructors wf_cval' : core.
Hint Constructors wf_cenv : core.

Scheme wf_cval_mut := Induction for wf_cval Sort Prop
with wf_cval'_mut := Induction for wf_cval' Sort Prop
with wf_cenv_mut := Induction for wf_cenv Sort Prop.

(* A result is well-formed if it is out of time, or returns a well-formed value. *)
Inductive wf_cres (Θ : analysis_context) : cres -> Prop :=
| WF_COOT :
  wf_cres Θ COOT

| WF_CRes :
  forall v,
    wf_cval Θ v ->
    wf_cres Θ (CRes v).

Hint Constructors wf_cres : core.

(* Inversion *)
Lemma wf_cval_CTag_inv {Θ A c l v} :
  wf_cval Θ (CTag A c l v) ->
  (Θ c = A) /\ wf_cval' Θ v.
Proof. intros Hwf; inv Hwf; split; eauto. Qed.

Lemma wf_cval_CVfun_inv {Θ f ρ xs e} :
  wf_cval' Θ (CVfun f ρ xs e) ->
  wf_cenv Θ ρ.
Proof. intros Hwf; inv Hwf; assumption. Qed.

Lemma wf_cres_CRes_inv {Θ v} :
  wf_cres Θ (CRes v) ->
  wf_cval Θ v.
Proof. intros Hwf; inv Hwf; assumption. Qed.

(* `wf_cenv` is preserved by the environment operations of the semantics *)
Lemma wf_cenv_get {Θ ρ} :
  wf_cenv Θ ρ ->
  forall x v,
    ρ ! x = Some v ->
    wf_cval Θ v.
Proof. fcrush. Qed.

Lemma wf_cenv_get_list {Θ ρ} :
  wf_cenv Θ ρ ->
  forall xs vs,
    get_list xs ρ = Some vs ->
    Forall (wf_cval Θ) vs.
Proof.
  intros Henv xs.
  induction xs as [| x xs IHxs]; simpl; intros vs Hget; fcrush.
Qed.

Lemma wf_cenv_set {Θ ρ} x v :
  wf_cenv Θ ρ ->
  wf_cval Θ v ->
  wf_cenv Θ (M.set x v ρ).
Proof.
  intros Henv Hv.
  inv Henv.
  constructor; intros y w Hget.
  destruct (M.elt_eq x y); subst.
  - rewrite M.gss in *; fcrush.
  - rewrite M.gso in *; fcrush.
Qed.

Lemma wf_cenv_set_lists {Θ} :
  forall ρ,
    wf_cenv Θ ρ ->
    forall vs xs ρ',
      Forall (wf_cval Θ) vs ->
      set_lists xs vs ρ = Some ρ' ->
      wf_cenv Θ ρ'.
Proof.
  intros ρ Henv vs.
  induction vs as [| v vs IHvs]; intros xs ρ' Hvs Hset.
  - destruct xs as [| x xs]; simpl in Hset; [| discriminate Hset].
    inv Hset; assumption.
  - destruct xs as [| x xs]; simpl in Hset; [discriminate Hset |].
    destruct (set_lists xs vs ρ) as [ρ'' |] eqn:Heqρ''; [| discriminate Hset].
    inv Hset.
    inv Hvs.
    match goal with
    | [Hv : wf_cval Θ v, Hvs' : Forall (wf_cval Θ) vs |- _] =>
        exact (wf_cenv_set x v (IHvs xs ρ'' Hvs' Heqρ'') Hv)
    end.
Qed.

Lemma cbstep_fuel_closed A c ρ e i Rs r I :
  cbstep_fuel A c ρ e i Rs r I ->
  internals_closed (ainternals_of (ai_int A)) c I.
Proof.
  intros.
  inv H.
  - eapply internals_closed_empty; eauto.
  - eapply approx_int_closed; eauto.
Qed.

(* Well-formedness does not depend on `acheck`: a foreign callee runs under its
   own analysis result, for which no `acheck` is available, so the induction
   is carried out without it. *)
Lemma cbstep_wf_cres_aux Θ :
  forall A c ρ e i Rs r I,
    cbstep A c ρ e i Rs r I ->
    Θ c = A ->
    wf_cenv Θ ρ ->
    wf_cres Θ r.
Proof.
  intros A c ρ e i Rs r I Hstep.
  induction Hstep using cbstep_ind' with
    (P := fun A c ρ e i Rs r I => Θ c = A -> wf_cenv Θ ρ -> wf_cres Θ r)
    (P0 := fun A c ρ e i Rs r I => Θ c = A -> wf_cenv Θ ρ -> wf_cres Θ r);
    intros HΘ Henv.
  - (* Cbstep_ret *)
    constructor.
    eapply wf_cenv_get; eauto.
  - (* Cbstep_fun: the new closure is tagged with `A = Θ c` *)
    apply IHHstep; [exact HΘ |].
    apply wf_cenv_set; [exact Henv |].
    constructor; [exact HΘ |].
    constructor; exact Henv.
  - (* Cbstep_app_External: the callee runs under its own tag `A' = Θ c'` *)
    match goal with
    | [Hget : M.get ?f ρ = Some ?vf |- _] =>
        pose proof (wf_cenv_get Henv f vf Hget) as Hvf
    end.
    destruct (wf_cval_CTag_inv Hvf) as [HΘ' Hvf'].
    pose proof (wf_cval_CVfun_inv Hvf') as Henv'.
    apply IHHstep; [exact HΘ' |].
    match goal with
    | [Hgetl : get_list _ ρ = Some _, Hset : set_lists _ _ _ = Some _ |- _] =>
        refine (wf_cenv_set_lists _ _ _ _ _ _ Hset);
        [ apply wf_cenv_set; [exact Henv' | exact Hvf]
        | exact (wf_cenv_get_list Henv _ _ Hgetl) ]
    end.
  - (* Cbstep_app_Internal: the callee runs under `A = Θ c` *)
    match goal with
    | [Hget : M.get ?f ρ = Some ?vf |- _] =>
        pose proof (wf_cenv_get Henv f vf Hget) as Hvf
    end.
    destruct (wf_cval_CTag_inv Hvf) as [HΘ' Hvf'].
    pose proof (wf_cval_CVfun_inv Hvf') as Henv'.
    apply IHHstep; [exact HΘ' |].
    match goal with
    | [Hgetl : get_list _ ρ = Some _, Hset : set_lists _ _ _ = Some _ |- _] =>
        refine (wf_cenv_set_lists _ _ _ _ _ _ Hset);
        [ apply wf_cenv_set; [exact Henv' | exact Hvf]
        | exact (wf_cenv_get_list Henv _ _ Hgetl) ]
    end.
  - (* CbstepF_OOT *)
    constructor.
  - (* CbstepF_Step *)
    apply IHHstep; [exact HΘ | exact Henv].
Qed.

(* A returned value agrees with Θ as well. *)
Lemma cbstep_wf_cres Θ :
  forall A c ρ e i Rs r I,
    cbstep A c ρ e i Rs r I ->
    Θ c = A ->
    wf_cenv Θ ρ ->
    wf_cres Θ r.
Proof.
  intros A c ρ e i Rs r I Hstep.
  exact (cbstep_wf_cres_aux Θ A c ρ e i Rs r I Hstep).
Qed.

Lemma cbstep_fuel_wf_cres Θ A c ρ e i Rs r I :
  Θ c = A ->
  wf_cenv Θ ρ ->
  cbstep_fuel A c ρ e i Rs r I ->
  wf_cres Θ r.
Proof.
  intros HΘ Henv Hstep.
  inv Hstep.
  - constructor.
  - eapply cbstep_wf_cres_aux; eauto.
Qed.

(* Cross-semantics Logical Relations *)
Section LR.

  Variable θ : analysis_context.
  Hypothesis θ_escape_ok : analysis_context_escape_ok θ.

  Definition R' (P : nat -> wval -> clval -> Prop) (i : nat) (r1 : res) (r2 : cres) :=
    match r1, r2 with
    | OOT, COOT => True
    | Res v1, CRes v2 => P i v1 v2
    | _, _ => False
    end.

  Definition E' (P : nat -> wval -> clval -> Prop) (A : analysis_result) (c : color) (i : nat) (ρ1 : env) (ρ2 : cenv) (e : exp) (Rs : avals) : Prop :=
    forall j1 r1,
      j1 <= i ->
      bstep_fuel ρ1 e j1 r1 ->
      exists j2 r2 I2,
        cbstep_fuel A c ρ2 e j2 Rs r2 I2 /\
          R' P (i - j1) r1 r2.

  Fixpoint V (i : nat) (wv : wval) (cv : clval) {struct i} : Prop :=
    wf_val wv /\
      wf_cval θ cv /\
      match wv, cv with
      | TAG _ l1 v1, CTAG _ A2 (c2, l2) v2 =>
          l1 = l2 /\
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

            | Vfun f1 ρ1 xs1 e1, CVfun f2 ρ2 xs2 e2 =>
                f1 = f2 /\ xs1 = xs2 /\ e1 = e2 /\
                  approx_vals (ai_env A2 f2) cv /\
                  approx_env (ai_env A2) ρ2 /\
                  match i with
                  | 0 => True
                  | S i0 =>
                      forall j c vs1 vs2 ρ3 ρ4,
                        j <= i0 ->
                        Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                        set_lists xs1 vs1 (M.set f1 (Tag l1 (Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                        set_lists xs2 vs2 (M.set f2 (CTag A2 c2 l2 (CVfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                        (* internal call: the arguments flow to the parameters *)
                        (c = c2 -> Forall2 (fun x v => approx_vals (ai_env A2 x) v) xs2 vs2) ->
                        (* foreign call: the closure must have escaped its unit *)
                        (c <> c2 -> approx_vals (ai_esc A2) cv) ->
                        E' V A2 c2 (i0 - (i0 - j)) ρ3 ρ4 e1 (ai_ret A2 l2)
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
    wf_cval θ v2.
  Proof. intros; destruct i; simpl in *; fcrush. Qed.

  Lemma V_wf_cval_Forall_r {i vs1 vs2} :
    Forall2 (V i) vs1 vs2 ->
    Forall (wf_cval θ) vs2.
  Proof. intros H. induction H; eauto using V_wf_cval_r. Qed.

  Lemma V_wf_cres_r {i v1 v2}:
    V i v1 v2 ->
    wf_cres θ (CRes v2).
  Proof. intros; eauto using V_wf_cval_r; eauto. Qed.

  Lemma R_wf_cres_r {i r1 r2} :
    R i r1 r2 ->
    wf_cres θ r2.
  Proof.
    unfold R.
    intros.
    destruct r1; destruct r2; try contradiction;
      eauto using V_wf_cval_r.
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
    wf_env Γ1 ρ1 /\
      wf_cenv θ ρ2 /\
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
    wf_env Γ1 ρ1.
  Proof. unfold G. fcrush. Qed.

  Lemma G_wf_cenv_r {i Γ1 ρ1 ρ2}:
    G i Γ1 ρ1 ρ2 ->
    wf_cenv θ ρ2.
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

    intros.
    destruct (M.elt_eq x0 x); subst.
    - repeat rewrite M.gss in *.
      fcrush.
    - repeat (rewrite M.gso in *; auto).
      fcrush.
  Qed.

  (* Binding a variable that is not in [Γ1] on the source side only
   preserves the environment relation. *)
  Lemma G_set_unused {i Γ1 ρ1 ρ2} y v :
    G i Γ1 ρ1 ρ2 ->
    ~ (y \in Γ1) ->
    wf_val v ->
    G i Γ1 (M.set y v ρ1) ρ2.
  Proof.
    unfold G.
    intros HG Hy Hv.
    destruct HG as [Hwf1 [Hwf2 HGv]].
    split; [| split ].
    - eapply wf_env_subset.
      + eapply wf_env_set; eassumption.
      + unfold Ensembles.Included, Ensembles.In.
        intros z Hz. right. assumption.
    - exact Hwf2.
    - intros z Hz.
      destruct (HGv z Hz) as [v1 [v2 [Hg1 [Hg2 HV]]]].
      exists v1, v2.
      rewrite M.gso by (intros Heq; subst; contradiction).
      split; [ exact Hg1 | split; [ exact Hg2 | exact HV ] ].
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
      destruct H0 as [Hwf1 [Hwf2 HV]];
      destruct c; destruct HV as [Heql HV]; subst.
    - destruct v; destruct c; fcrush.
    - fcrush.
(*    - repeat (split; auto).
      destruct v; destruct c0; try contradiction.
      + fcrush.
      + fcrush. *)
    - repeat (split; auto).
      destruct v; destruct c0; try contradiction.
      + destruct HV as [Heqv [Heql [Heqe [Havs [Haenv HV]]]]]; subst.
        repeat (split; eauto); intros.
    - repeat (split; auto).
      destruct v; destruct c0; try contradiction.
      destruct HV as [Heqv [Heql [Heqe [Havs [Haenv HV]]]]]; subst.
      repeat (split; eauto); intros.
      specialize (HV j0 c0 vs1 vs2 ρ3 ρ4).
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

  Lemma E_mono {A Rs c ρ1 ρ2 e} i j:
    E A c i ρ1 ρ2 e Rs ->
    j <= i ->
    E A c j ρ1 ρ2 e Rs.
  Proof.
    unfold E, R, E', R'.
    intros.
    destruct (H j1 r1) as [j2 [r2 [I2 [Hr2 HR]]]]; auto; try lia.
    exists j2, r2, I2; split; eauto.
    apply R_mono with (i - j1); try lia; auto.
  Qed.

  Lemma G_mono {Γ1 ρ1 ρ2} i j:
    G i Γ1 ρ1 ρ2 ->
    j <= i ->
    G j Γ1 ρ1 ρ2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hwf1 [Hwf2 HG]].
    repeat (split; auto); intros.
    edestruct HG as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto; invc.
    eexists; repeat (split; eauto).
    eauto using V_mono.
  Qed.


  (* Compatibility Lemmas *)
  (* Well Scoped *)
  (* This essentially says `occurs_free e` ⊆ Γ *)
  Inductive well_scoped (Γ : vars) : exp -> Prop :=
  | Well_Scoped_ret :
    forall x,
      (x \in Γ) ->
      well_scoped Γ (Eret x)

  | Well_Scoped_fun :
    forall {f l xs e k},
      well_scoped (FromList xs :|: (f |: Γ)) e ->
      well_scoped (f |: Γ) k ->
      well_scoped Γ (Efun f l xs e k)

  | Well_Scoped_app :
    forall {f l xs},
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      well_scoped Γ (Eapp f l xs)

  | Well_Scoped_letapp :
    forall {x f l xs k},
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      well_scoped (x |: Γ) k ->
      well_scoped Γ (Eletapp x f l xs k)

  | Well_Scoped_constr :
    forall {x l t xs k},
      (FromList xs \subset Γ) ->
      well_scoped (x |: Γ) k ->
      well_scoped Γ (Econstr x l t xs k)

  | Well_Scoped_proj :
    forall {l x y k n},
      (y \in Γ) ->
      well_scoped (x |: Γ) k ->
      well_scoped Γ (Eproj x l n y k)

  | Well_Scoped_case_nil :
    forall {l x},
      (x \in Γ) ->
      well_scoped Γ (Ecase x l [])

  | Well_Scoped_case_cons :
    forall {x l e t cl},
      (x \in Γ) ->
      well_scoped Γ e ->
      well_scoped Γ (Ecase x l cl) ->
      well_scoped Γ (Ecase x l ((t, e) :: cl)).

  Hint Constructors well_scoped : core.

  Lemma well_scoped_inv e Γ :
    well_scoped Γ e ->
    occurs_free e \subset Γ.
  Proof.
    intros.
    induction H; unfold Ensembles.Included, Ensembles.In in *; intros; fcrush.
  Qed.

  Lemma well_scoped_intro e Γ :
    occurs_free e \subset Γ ->
    well_scoped Γ e.
  Proof.
    revert Γ.
    induction e
      as [ x
         | x w xs
         | f w xs e k IHe IHk
         | x f w xs e IHe
         | x w c xs e IHe
         | x w
         | x w cl c e IHe IHcl
         | x w n v0 e IHe ]
           using exp_ind';
      intros Γ Hfree; unfold Ensembles.Included, Ensembles.In in *.
    - constructor.
      apply Hfree; constructor.
    - constructor.
      + apply Hfree; constructor.
      + eapply free_app_xs_inv; eauto.
    - constructor.
      + apply IHe; eapply free_fun_e_inv; eauto.
      + apply IHk; eapply free_fun_k_inv; eauto.
    - constructor.
      + apply Hfree; eapply Free_letapp2.
      + eapply free_letapp_xs_inv; eauto.
      + apply IHe; eapply free_letapp_k_inv; eauto.
    - constructor.
      + eapply free_constr_xs_inv; eauto.
      + apply IHe; eapply free_constr_k_inv; eauto.
    - constructor.
      apply Hfree; constructor.
    - constructor.
      + apply Hfree; constructor.
      + apply IHe; eapply free_case_hd_inv; eauto.
      + apply IHcl; eapply free_case_tl_inv; eauto.
    - constructor.
      + apply Hfree; constructor.
      + apply IHe; eapply free_proj_k_inv; eauto.
  Qed.

  Definition well_annotated A c Γ e Rs :=
    θ c = A /\
    forall i ρ1 ρ2,
      acheck A e Rs ->
      G i Γ ρ1 ρ2 ->
      E A c i ρ1 ρ2 e Rs.

  Lemma ret_compat A c Γ x Rs :
    θ c = A ->
    (x \in Γ) ->
    well_annotated A c Γ (Eret x) Rs.
  Proof.
    unfold well_annotated, E, E', R, R', Ensembles.Included, Ensembles.In.
    intros; simpl.
    split; auto; intros.

    inv H4.
    - fcrush.
    - destruct r1.
      fcrush.
      inv H1; inv H5.
      edestruct (G_get H2) as [v2 [Heqv2 HV]]; eauto.
      exists 1, (CRes v2), (Empty_set _); split; eauto; simpl.
      econstructor; eauto.
      admit.
      (* no interaction is collected *)
      unfold approx_int, Ensembles.In.
      intros c1 l1 c2 l2 Hin; destruct Hin.
      eapply V_mono; eauto; lia.
  Admitted.

  Lemma fundamental_property {A c Γ e Rs}:
    θ c = A ->
    well_scoped Γ e ->
    well_annotated A c Γ e Rs.
  Proof.
    intros HU H.
    induction H; intros.
    - eapply ret_compat; eauto.
    - (* eapply fun_compat; eauto.
      eapply well_scoped_inv; eauto. *)
      admit.
    - (* eapply app_compat; eauto. *)
      admit.
    - admit.
    - admit.
    - admit.
    - (* eapply case_nil_compat; eauto. *)
      admit.
    - admit.
  Admitted.

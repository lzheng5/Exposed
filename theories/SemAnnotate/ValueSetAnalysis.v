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

    (* unknown callee: the arguments escape and the result is unknown; since
       `AVtop` also stands for our own escaped closures, the callee may be any
       of them, which is then called as a known callee *)
    ((AVtop \in ai_env A f) ->
       Forall (fun x => ai_env A x \subset ai_esc A) xs /\ (* each argument can escape *)
       (AVtop \in R) /\ (* result is unknown *)
       (forall l' f' xs' e',
           (AVfun l' f' xs' e' \in ai_esc A) ->
             ((l', l) \in ai_int A) /\ (* each escaping function can be called at this callsite *)
             length xs = length xs' /\
             (AVfun l' f' xs' e' \in ai_env A f') /\
             Forall2 (fun x x' => ai_env A x \subset ai_env A x') xs xs' /\ (* call the escaping function with the current arguments *)
             (ai_ret A l' \subset R))) -> (* what each escaping function may return can also be returned from this callsite *)

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

Lemma approx_vals_subset {AE x' v} {x : var}:
  approx_vals (AE x) v ->
  (AE x) \subset (AE x') ->
  approx_vals (AE x') v.
Proof. unfold approx_vals. fcrush. Qed.

Lemma approx_vals_subset_list {AE xs vs2} :
  Forall2 (fun (x : var) (v : clval) => approx_vals (AE x) v) xs vs2 ->
  forall xs',
    Forall2 (fun x x' : var => AE x \subset AE x') xs xs' ->
    Forall2 (fun (x : var) (v1 : clval) => approx_vals (AE x) v1) xs' vs2.
Proof.
  intro H.
  induction H; intros; simpl.
  - inv H; auto.
  - inv H1.
    constructor; auto.
    eapply approx_vals_subset; eauto.
Qed.

Lemma set_lists_approx_top {AE xs vs ρ ρ'} :
  (forall x, List.In x xs -> AVtop \in AE x) ->
  set_lists xs vs ρ = Some ρ' ->
  Forall2 (fun x v => approx_vals (AE x) v) xs vs.
Proof.
  intros Htop.
  revert vs ρ ρ' Htop.
  induction xs as [| x xs IHxs]; intros vs ρ ρ' Htop Hset.
  - destruct vs as [| v vs]; [constructor | discriminate Hset].
  - destruct vs as [| v vs]; [discriminate Hset |].
    simpl in Hset.
    destruct (set_lists xs vs ρ) as [ρ'' |] eqn:Heq; [| discriminate Hset].
    constructor.
    + (* `AVtop` approximates every value *)
      exists AVtop; split; [apply Htop; left; reflexivity | constructor].
    + eapply IHxs; [| exact Heq].
      intros y Hy; apply Htop; right; exact Hy.
Qed.

Lemma approx_env_get {AE ρ x v} :
  approx_env AE ρ ->
  ρ ! x = Some v ->
  approx_vals (AE x) v.
Proof. intros Henv Hget; inv Henv; unfold approx_vals; eauto. Qed.

Lemma approx_env_set {AE ρ} x v :
  approx_env AE ρ ->
  approx_vals (AE x) v ->
  approx_env AE (M.set x v ρ).
Proof.
  intros Henv Hv.
  inv Henv.
  constructor; intros y w Hget.
  destruct (M.elt_eq x y); subst.
  - rewrite M.gss in Hget; inv Hget; exact Hv.
  - rewrite M.gso in Hget by auto; eauto.
Qed.

Lemma approx_env_get_list {AE ρ} :
  approx_env AE ρ ->
  forall xs vs,
    get_list xs ρ = Some vs ->
    Forall2 (fun x v => approx_vals (AE x) v) xs vs.
Proof.
  intros Henv xs.
  induction xs as [| x xs IHxs]; simpl; intros vs Hget.
  - inv Hget; constructor.
  - destruct (M.get x ρ) as [v |] eqn:Hx; [| discriminate Hget].
    destruct (get_list xs ρ) as [vs' |] eqn:Hxs; [| discriminate Hget].
    inv Hget.
    constructor.
    + eapply approx_env_get; eauto.
    + eapply IHxs; eauto.
Qed.

Lemma approx_env_set_lists {AE ρ} :
  approx_env AE ρ ->
  forall xs vs ρ',
    Forall2 (fun x v => approx_vals (AE x) v) xs vs ->
    set_lists xs vs ρ = Some ρ' ->
    approx_env AE ρ'.
Proof.
  intros Henv xs.
  induction xs as [| x xs IHxs]; intros vs ρ' Hall Hset; simpl in Hset.
  - destruct vs as [| v vs]; [| discriminate Hset].
    inv Hset; exact Henv.
  - destruct vs as [| v vs]; [discriminate Hset |].
    destruct (set_lists xs vs ρ) as [ρ'' |] eqn:Heq; [| discriminate Hset].
    inv Hset.
    inv Hall.
    apply approx_env_set; [eapply IHxs; eauto | assumption].
Qed.

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

Lemma approx_res_subset Rs Rs' r :
  approx_res Rs r ->
  Rs \subset Rs' ->
  approx_res Rs' r.
Proof. intros. inv H; fcrush. Qed.

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

Lemma approx_int_empty c AI :
  approx_int c AI (Empty_set _).
Proof. unfold approx_int, Ensembles.In. fcrush. Qed.

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

(* Adding an internal interaction of the unit `c` that its analysis predicts. *)
Lemma approx_int_add_internal {c AI l1 l2 I} :
  (l1, l2) \in AI ->
  approx_int c AI I ->
  approx_int c AI (((c, l1), (c, l2)) |: I).
Proof.
  unfold approx_int.
  intros Hl HI c1 l1' c2 l2' Hin.
  inv Hin.
  - match goal with [Hs : _ \in [set _] |- _] => inv Hs end.
    repeat split.
    + intros _ _; exact Hl.
    + intros _ Hneq; exfalso; apply Hneq; reflexivity.
    + intros Hneq _; exfalso; apply Hneq; reflexivity.
  - match goal with [HI' : _ \in I |- _] => exact (HI _ _ _ _ HI') end.
Qed.

Lemma approx_int_add {c AI cl I} :
  approx_int c AI [set cl] ->
  approx_int c AI I ->
  approx_int c AI (cl |: I).
Proof.
  unfold approx_int.
  intros H1 H2 c1 l1 c2 l2 Hin.
  inv Hin; eauto.
Qed.

Lemma approx_int_singleton {c AI c1 l1 c2 l2} :
  (c1 = c -> c2 = c -> (l1, l2) \in AI) ->
  (c1 = c -> c2 <> c -> (l1, l_top_elim) \in AI) ->
  (c1 <> c -> c2 = c -> (l_top_intro, l2) \in AI) ->
  approx_int c AI [set ((c1, l1), (c2, l2))].
Proof.
  unfold approx_int.
  intros H1 H2 H3 c1' l1' c2' l2' Hin.
  inv Hin.
  auto.
Qed.

Lemma approx_int_union {c AI I1 I2} :
  approx_int c AI I1 ->
  approx_int c AI I2 ->
  approx_int c AI (I1 :|: I2).
Proof.
  unfold approx_int.
  intros H1 H2 c1 l1 c2 l2 Hin.
  inv Hin; eauto.
Qed.

(* Invariants for Escaped Values *)
(* A value held by the unit wearing `c` that belongs to another unit must have
   escaped from that unit.  A closure must have escaped with its own allocation
   site: an `AVtop` in `ai_esc` would not constrain anything. *)
Definition cescaped (c : color) (v : clval) : Prop :=
  match v with
  | CTAG _ A' (c', l) (CVfun f _ xs e) => c' <> c -> AVfun l f xs e \in ai_esc A'
  | CTAG _ A' (c', _) _ => c' <> c -> approx_vals (ai_esc A') v
  end.

Lemma cescaped_defining A c l v :
  cescaped c (CTag A c l v).
Proof. unfold cescaped; fcrush. Qed.

Definition cescaped_env (c : color) (ρ : cenv) : Prop :=
  forall x v, ρ ! x = Some v -> cescaped c v.

Lemma cescaped_env_set {c ρ} x v :
  cescaped_env c ρ ->
  cescaped c v ->
  cescaped_env c (M.set x v ρ).
Proof.
  unfold cescaped_env.
  intros Hesc Hv y w Hget.
  destruct (M.elt_eq x y); subst.
  - rewrite M.gss in Hget; inv Hget; exact Hv.
  - rewrite M.gso in Hget by auto; eauto.
Qed.

Lemma cescaped_env_get {c ρ} x v :
  cescaped_env c ρ ->
  ρ ! x = Some v ->
  cescaped c v.
Proof. unfold cescaped_env; eauto. Qed.

Lemma cescaped_env_get_list {c ρ} :
  cescaped_env c ρ ->
  forall xs vs,
    get_list xs ρ = Some vs ->
    Forall (cescaped c) vs.
Proof.
  intros Hesc xs.
  induction xs as [| x xs IHxs]; simpl; intros vs Hget.
  - inv Hget; constructor.
  - destruct (M.get x ρ) as [v |] eqn:Hx; [| discriminate Hget].
    destruct (get_list xs ρ) as [vs' |] eqn:Hxs; [| discriminate Hget].
    inv Hget.
    constructor.
    + eapply cescaped_env_get; eauto.
    + eapply IHxs; eauto.
Qed.

Lemma cescaped_env_set_lists {c ρ} :
  cescaped_env c ρ ->
  forall xs vs ρ',
    Forall (cescaped c) vs ->
    set_lists xs vs ρ = Some ρ' ->
    cescaped_env c ρ'.
Proof.
  intros Hesc xs.
  induction xs as [| x xs IHxs]; intros vs ρ' Hall Hset; simpl in Hset.
  - destruct vs as [| v vs]; [| discriminate Hset].
    inv Hset; exact Hesc.
  - destruct vs as [| v vs]; [discriminate Hset |].
    destruct (set_lists xs vs ρ) as [ρ'' |] eqn:Heq; [| discriminate Hset].
    inv Hset.
    inv Hall.
    apply cescaped_env_set; [eapply IHxs; eauto | assumption].
Qed.

(* Invariants for Variable Binding *)
(* How a value held by the unit wearing `c` (with analysis result `A`) is
   approximated at variable `x`:
   - a closure of the unit itself is approximated by its own allocation site,
     not merely by `AVtop` -- unless it has already *escaped*, in which case
     `AVtop` stands for it.  This is what lets its exact site reach `ai_esc A`
     when it escapes, and what makes calling it a (statically) known call;
   - a foreign value is approximated by `AVtop`, so that eliminating it is
     treated as an unknown call. *)
Definition cbinding (c : color) (A : analysis_result) (x : var) (v : clval) : Prop :=
  match v with
  | CTAG _ _ (c', l) (CVfun f _ xs e) =>
      (c' = c -> (* c is the defining unit *)
       (AVfun l f xs e \in ai_env A x) \/ (* internal closure *)
         ((AVfun l f xs e \in ai_esc A) /\ (AVtop \in ai_env A x))) /\ (* unknown closure *)
        (c' <> c -> AVtop \in ai_env A x) (* c is not the defining unit *)
  | CTAG _ _ (c', _) _ => c' <> c -> AVtop \in ai_env A x
  end.

Definition cbinding_env (c : color) (A : analysis_result) (ρ : cenv) : Prop :=
  forall x v, ρ ! x = Some v -> cbinding c A x v.

Lemma cbinding_env_set {c A ρ} x v :
  cbinding_env c A ρ ->
  cbinding c A x v ->
  cbinding_env c A (M.set x v ρ).
Proof.
  unfold cbinding_env.
  intros Hex Hv y w Hget.
  destruct (M.elt_eq x y); subst.
  - rewrite M.gss in Hget; inv Hget; exact Hv.
  - rewrite M.gso in Hget by auto; eauto.
Qed.

Lemma cbinding_env_get {c A ρ} x v :
  cbinding_env c A ρ ->
  ρ ! x = Some v ->
  cbinding c A x v.
Proof. unfold cbinding_env; eauto. Qed.

Lemma cbinding_env_get_list {c A ρ} :
  cbinding_env c A ρ ->
  forall xs vs,
    get_list xs ρ = Some vs ->
    Forall2 (cbinding c A) xs vs.
Proof.
  intros Hloc xs.
  induction xs as [| x xs IHxs]; simpl; intros vs Hget.
  - inv Hget; constructor.
  - destruct (M.get x ρ) as [v |] eqn:Hx; [| discriminate Hget].
    destruct (get_list xs ρ) as [vs' |] eqn:Hxs; [| discriminate Hget].
    inv Hget.
    constructor.
    + eapply cbinding_env_get; eauto.
    + eapply IHxs; eauto.
Qed.

Lemma cbinding_env_set_lists {c A ρ} :
  cbinding_env c A ρ ->
  forall xs vs ρ',
    Forall2 (cbinding c A) xs vs ->
    set_lists xs vs ρ = Some ρ' ->
    cbinding_env c A ρ'.
Proof.
  intros Hloc xs.
  induction xs as [| x xs IHxs]; intros vs ρ' Hall Hset; simpl in Hset.
  - destruct vs as [| v vs]; [| discriminate Hset].
    inv Hset; exact Hloc.
  - destruct vs as [| v vs]; [discriminate Hset |].
    destruct (set_lists xs vs ρ) as [ρ'' |] eqn:Heq; [| discriminate Hset].
    inv Hset.
    inv Hall.
    apply cbinding_env_set; [eapply IHxs; eauto | assumption].
Qed.

(* `cbinding` is preserved when the value flows into a variable whose value
   set includes that of the original one. *)
Lemma cbinding_subset {c A x x' v} :
  cbinding c A x v ->
  ai_env A x \subset ai_env A x' ->
  cbinding c A x' v.
Proof.
  intros Hb Hsub.
  destruct v as [A' [c' l'] w].
  destruct w as [f ρ xs e | t vs]; unfold cbinding in *.
  - destruct Hb as [Hown Hforeign].
    split.
    + intros Heq.
      destruct (Hown Heq) as [Hin | [Hesc Htop]].
      * left; apply Hsub; exact Hin.
      * right; split; [exact Hesc | apply Hsub; exact Htop].
    + intros Hneq; apply Hsub; exact (Hforeign Hneq).
  - intros Hneq; apply Hsub; exact (Hb Hneq).
Qed.

Lemma cbinding_subset_list {c A xs xs' vs} :
  Forall2 (cbinding c A) xs vs ->
  Forall2 (fun x x' => ai_env A x \subset ai_env A x') xs xs' ->
  Forall2 (cbinding c A) xs' vs.
Proof.
  intros Hb.
  revert xs'.
  induction Hb as [| x v xs vs Hx Hb IH]; intros xs' Hsub; inv Hsub.
  - constructor.
  - constructor; [eapply cbinding_subset; eauto | eapply IH; eauto].
Qed.

(* Invariants for Value Flow *)
(* `cbinding` generalised from the value set of a variable to an arbitrary
   value set `avs`, e.g. the return set of an expression: how a value held by
   the unit wearing `c` is approximated in `avs`. *)
Definition cflows (c : color) (A : analysis_result) (avs : avals) (v : clval) : Prop :=
  match v with
  | CTAG _ _ (c', l) (CVfun f _ xs e) =>
      (c' = c -> (* c is the defining unit *)
       (AVfun l f xs e \in avs) \/ (* internal closure *)
         ((AVfun l f xs e \in ai_esc A) /\ (AVtop \in avs))) /\ (* unknown closure *)
        (c' <> c -> AVtop \in avs) (* c is not the defining unit *)
  | CTAG _ _ (c', _) _ => c' <> c -> AVtop \in avs
  end.

Lemma cbinding_cflows {c A x v} :
  cbinding c A x v ->
  cflows c A (ai_env A x) v.
Proof. intros H; exact H. Qed.

Lemma cflows_cbinding {c A x v} :
  cflows c A (ai_env A x) v ->
  cbinding c A x v.
Proof. intros H; exact H. Qed.

Lemma cflows_subset {c A avs avs' v} :
  cflows c A avs v ->
  avs \subset avs' ->
  cflows c A avs' v.
Proof.
  intros Hb Hsub.
  destruct v as [A' [c' l'] w].
  destruct w as [f ρ xs e | t vs]; unfold cflows in *.
  - destruct Hb as [Hown Hforeign].
    split.
    + intros Heq.
      destruct (Hown Heq) as [Hin | [Hesc Htop]].
      * left; apply Hsub; exact Hin.
      * right; split; [exact Hesc | apply Hsub; exact Htop].
    + intros Hneq; apply Hsub; exact (Hforeign Hneq).
  - intros Hneq; apply Hsub; exact (Hb Hneq).
Qed.

(* Invariants for Results *)
(* A result returned by the unit wearing `c` into the return set `Rs` keeps
   the invariants of a binding: a foreign value has escaped, and a closure of
   the unit itself is approximated in `Rs` by its own allocation site, unless
   it has escaped already.  Unlike `approx_res`, this survives `AVtop ∈ Rs`. *)
Definition cres_inv (c : color) (A : analysis_result) (Rs : avals) (r : cres) : Prop :=
  match r with
  | COOT => True
  | CRes v => cescaped c v /\ cflows c A Rs v
  end.

Lemma cres_inv_subset {c A Rs Rs' r} :
  cres_inv c A Rs r ->
  Rs \subset Rs' ->
  cres_inv c A Rs' r.
Proof.
  intros Hok Hsub.
  destruct r as [| v]; [exact I |].
  destruct Hok as [Hesc Hfl].
  split; [exact Hesc | eapply cflows_subset; eauto].
Qed.

(* The result is not a constructor.  Only closures cross the boundary for now
   (see `cboundary`), and the logical relation only relates closures. *)
Definition cres_is_fun (r : cres) : Prop :=
  match r with
  | CRes (CTAG _ _ _ (CVconstr _ _)) => False
  | _ => True
  end.

(* A value that crosses the program boundary: a closure that has escaped
   from its unit with its own allocation site. *)
Definition cboundary (cv : clval) : Prop :=
  match cv with
  | CTAG _ A (c, l) (CVfun f _ xs e) => AVfun l f xs e \in ai_esc A
  | _ => False
  end.

(* A result that crosses the program boundary. *)
Definition cboundary_res (r : cres) : Prop :=
  match r with
  | COOT => True
  | CRes v => cboundary v
  end.

(* Checking Semantics based on the Collecting Semantics *)
(* This semantics dynamically validates the analysis result, `A`.
   The collected interactions are validated against `ai_int A` once, in
   `CbstepF_Step`, which covers every interaction produced underneath it,
   including the call edge added by `Cbstep_app_*`. *)
Inductive cbstep (A : analysis_result) (c : color) (bdr : bool) (ρ : cenv) : exp -> fuel -> avals -> cres -> interactions -> Prop :=
| Cbstep_ret :
  forall {x v Rs},
    M.get x ρ = Some v ->
    cbstep A c bdr ρ (Eret x) 0 Rs (CRes v) (Empty_set _)

| Cbstep_fun :
  forall {f l xs e k i Rs r I},
    cbstep_fuel A c bdr (M.set f (CTag A c l (CVfun f ρ xs e)) ρ) k i Rs r I ->
    approx_vals (ai_env A f) (CTag A c l (CVfun f ρ xs e)) ->
    cbstep A c bdr ρ (Efun f l xs e k) i Rs r I

(* Foreign call: dynamic counterpart of the unknown-callee branch of `Acheck_app`,
   validated from both sides.  The caller (`A`) sees an unknown value being
   eliminated and its arguments escaping; the callee (`A'`) sees one of its
   escaped closures being eliminated by the context. *)
| Cbstep_app_External :
  forall Rs {A' f f' c' l l' xs ρ' xs' e vs ρ'' i r I},
    M.get f ρ = Some (CTag A' c' l' (CVfun f' ρ' xs' e)) ->
    c <> c' ->

    (* callee side: the closure has escaped and is eliminated by the context
       (the caller side, `(l_top_intro, l)`, is checked by `CbstepF_Step`) *)
    (AVfun l' f' xs' e \in ai_esc A') ->
    ((l', l_top_elim) \in ai_int A') ->

    (* caller side: the arguments escape to the callee's unit *)
    get_list xs ρ = Some vs ->
    Forall (cescaped c') vs ->

    (* callee side: the (unknown) arguments flow to the parameters *)
    set_lists xs' vs (M.set f' (CTag A' c' l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    approx_env (ai_env A') ρ'' ->

    (* the body is validated against the callee's own analysis result and
       returns into `ai_ret A' l'` *)
    cbstep_fuel A' c' true ρ'' e i (ai_ret A' l') r I ->

    cbstep A c bdr ρ (Eapp f l xs) i Rs r (((c', l'), (c, l)) |: I)

(* Internal call: dynamic counterpart of the known-callee branch of
   `Acheck_app`.  The callee wears the caller's color, so it belongs to the
   same unit and is validated against the same analysis result `A`. *)
| Cbstep_app_Internal :
  forall Rs { f f' l l' xs ρ' xs' e vs ρ'' i r I },
    M.get f ρ = Some (CTag A c l' (CVfun f' ρ' xs' e)) ->

    (* the arguments flow to the parameters *)
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (CTag A c l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    approx_env (ai_env A) ρ'' ->

    (* the body returns into `ai_ret A l'` *)
    cbstep_fuel A c false ρ'' e i (ai_ret A l') r I ->

    cbstep A c bdr ρ (Eapp f l xs) i Rs r (((c, l'), (c, l)) |: I)

with cbstep_fuel (A : analysis_result) (c : color) (bdr : bool) (ρ : cenv) : exp -> fuel -> avals -> cres -> interactions -> Prop :=
| CbstepF_OOT :
  forall {e Rs},
    cbstep_fuel A c bdr ρ e 0 Rs COOT (Empty_set _)

| CbstepF_Step :
  forall {e i Rs r I},
    cbstep A c bdr ρ e i Rs r I ->
    approx_res Rs r ->
    approx_int c (ai_int A) I ->
    (if bdr then cboundary_res r else True) ->
    cres_inv c A Rs r ->
    cbstep_fuel A c bdr ρ e (S i) Rs r I.

Hint Constructors cbstep : core.
Hint Constructors cbstep_fuel : core.

Scheme cbstep_ind' := Minimality for cbstep Sort Prop
with cbstep_fuel_ind' := Minimality for cbstep_fuel Sort Prop.

Lemma cbstep_deterministic_aux v v' {A I I' c bdr ρ e i i' Rs r r'}:
  cbstep A c bdr ρ e i Rs r I ->
  cbstep A c bdr ρ e i' Rs r' I' ->
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
  induction H using cbstep_ind' with (P := fun A c bdr ρ e i Rs r I =>
                                             forall I' v i' r' v',
                                               cbstep A c bdr ρ e i' Rs r' I' ->
                                               r = CRes v -> r' = CRes v' ->
                                               v = v' /\ i = i' /\ I <--> I')
                                     (P0 := fun A c bdr ρ e i Rs r I =>
                                              forall I' v i' r' v',
                                                cbstep_fuel A c bdr ρ e i' Rs r' I' ->
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
  - match goal with [Hf : cbstep_fuel _ _ _ _ _ _ _ _ _ |- _] => inv Hf end;
      edestruct IHcbstep as [Heqv [Heqi HeqI]]; eauto.
Qed.

Lemma cbstep_fuel_deterministic_aux v v' {A I I' c bdr ρ e i i' Rs r r'}:
  cbstep_fuel A c bdr ρ e i Rs r I ->
  cbstep_fuel A c bdr ρ e i' Rs r' I' ->
  r = CRes v ->
  r' = CRes v' ->
  (v = v' /\ i = i' /\ I <--> I').
Proof.
  intros Hstep Hstep' Heqr Heqr'; subst.
  inv Hstep; inv Hstep'.
  match goal with
  | [Hcb : cbstep _ _ _ _ _ _ _ (CRes v) _,
     Hcb' : cbstep _ _ _ _ _ _ _ (CRes v') _ |- _] =>
      edestruct (cbstep_deterministic_aux v v' Hcb Hcb') as [Heqv [Heqi HeqI]];
      subst; eauto
  end.
Qed.

Theorem cbstep_deterministic v v' {A I I' c bdr ρ e Rs i i'}:
  cbstep A c bdr ρ e i Rs (CRes v) I ->
  cbstep A c bdr ρ e i' Rs (CRes v') I' ->
  (v = v' /\ i = i' /\ I <--> I').
Proof. srun eauto using cbstep_deterministic_aux. Qed.

Theorem cbstep_fuel_deterministic v v' {A I I' c bdr ρ e Rs i i'}:
  cbstep_fuel A c bdr ρ e i Rs (CRes v) I ->
  cbstep_fuel A c bdr ρ e i' Rs (CRes v') I' ->
  (v = v' /\ i = i' /\ I <--> I').
Proof. srun eauto using cbstep_fuel_deterministic_aux. Qed.

Lemma cbstep_fuel_cboundary_res A c ρ e i Rs r I :
  cbstep_fuel A c true ρ e i Rs r I ->
  cboundary_res r.
Proof. intros. inv H; fcrush. Qed.

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

Lemma cbstep_fuel_approx_res A c bdr ρ e i Rs r I :
  cbstep_fuel A c bdr ρ e i Rs r I ->
  approx_res Rs r.
Proof. intros H. inv H; eauto. Qed.

Lemma cbstep_fuel_cres_inv A c bdr ρ e i Rs r I :
  cbstep_fuel A c bdr ρ e i Rs r I ->
  cres_inv c A Rs r.
Proof. intros Hstep. inv Hstep; [exact I | assumption]. Qed.

(* A result returned into a return set that escapes crosses the boundary:
   - a closure of the unit itself is either approximated in `Rs` by its own
     allocation site, hence in `ai_esc`, or has escaped already;
   - a foreign closure has escaped from its own unit. *)
Lemma cres_inv_cboundary Θ c Rs r :
  wf_cres Θ r ->
  cres_is_fun r ->
  cres_inv c (Θ c) Rs r ->
  Rs \subset ai_esc (Θ c) ->
  cboundary_res r.
Proof.
  intros Hwf Hfun Hok Hsub.
  destruct r as [| v]; [exact I |].
  destruct v as [A' [c' l'] w].
  pose proof (wf_cval_CTag_inv (wf_cres_CRes_inv Hwf)) as [HA' _].
  subst A'.
  destruct w as [f ρ xs e | t vs]; [| destruct Hfun].
  destruct Hok as [Hesc [Hown _]].
  destruct (Nat.eq_dec c' c) as [Heq | Hneq].
  - subst c'.
    destruct (Hown eq_refl) as [Hin | [Hin _]].
    + exact (Hsub _ Hin).
    + exact Hin.
  - exact (Hesc Hneq).
Qed.

Lemma cbstep_fuel_approx_int A c bdr ρ e i Rs r I :
  cbstep_fuel A c bdr ρ e i Rs r I ->
  approx_int c (ai_int A) I.
Proof.
  intros H. inv H; eauto.
  eapply approx_int_empty; eauto.
Qed.

Lemma cbstep_fuel_closed A c bdr ρ e i Rs r I :
  cbstep_fuel A c bdr ρ e i Rs r I ->
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
  forall A c bdr ρ e i Rs r I,
    cbstep A c bdr ρ e i Rs r I ->
    Θ c = A ->
    wf_cenv Θ ρ ->
    wf_cres Θ r.
Proof.
  intros A c bdr ρ e i Rs r I Hstep.
  induction Hstep using cbstep_ind' with
    (P := fun A c bdr ρ e i Rs r I => Θ c = A -> wf_cenv Θ ρ -> wf_cres Θ r)
    (P0 := fun A c bdr ρ e i Rs r I => Θ c = A -> wf_cenv Θ ρ -> wf_cres Θ r);
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
  forall A c bdr ρ e i Rs r I,
    cbstep A c bdr ρ e i Rs r I ->
    Θ c = A ->
    wf_cenv Θ ρ ->
    wf_cres Θ r.
Proof.
  intros A c bdr ρ e i Rs r I Hstep.
  exact (cbstep_wf_cres_aux Θ A c bdr ρ e i Rs r I Hstep).
Qed.

Lemma cbstep_fuel_wf_cres Θ A c bdr ρ e i Rs r I :
  Θ c = A ->
  wf_cenv Θ ρ ->
  cbstep_fuel A c bdr ρ e i Rs r I ->
  wf_cres Θ r.
Proof.
  intros HΘ Henv Hstep.
  inv Hstep.
  - constructor.
  - eapply cbstep_wf_cres_aux; eauto.
Qed.

(* The callee's entry environment is well-formed, and the callee runs under
   the analysis result that `Θ` prescribes for its color. *)
Lemma wf_cenv_callee {Θ ρ f A' c' l' f' ρ' xs' e xs vs ρ''} :
  wf_cenv Θ ρ ->
  M.get f ρ = Some (CTag A' c' l' (CVfun f' ρ' xs' e)) ->
  get_list xs ρ = Some vs ->
  set_lists xs' vs (M.set f' (CTag A' c' l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
  Θ c' = A' /\ wf_cenv Θ ρ''.
Proof.
  intros Henv Hget Hgetl Hset.
  pose proof (wf_cenv_get Henv _ _ Hget) as Hvf.
  destruct (wf_cval_CTag_inv Hvf) as [HΘ' Hvf'].
  pose proof (wf_cval_CVfun_inv Hvf') as Henv'.
  split; [exact HΘ' |].
  refine (wf_cenv_set_lists _ _ _ _ _ _ Hset);
    [ apply wf_cenv_set; [exact Henv' | exact Hvf]
    | exact (wf_cenv_get_list Henv _ _ Hgetl) ].
Qed.

(* Interactions collected under a unit are approximated from the point of view
   of every *other* unit: an interaction in which another unit `c'` takes part
   is either produced by a foreign call into one of its closures, whose callee
   side is checked by `Cbstep_app_External`, or by code of `c'` itself, which
   is checked by the `CbstepF_Step` of the nested run under `c'`. *)
Lemma cbstep_approx_int_handover_aux Θ :
  forall A c bdr ρ e i Rs r I,
    cbstep A c bdr ρ e i Rs r I ->
    Θ c = A ->
    wf_cenv Θ ρ ->
    forall c', c' <> c -> approx_int c' (ai_int (Θ c')) I.
Proof.
  intros A c bdr ρ e i Rs r I Hstep.
  induction Hstep using cbstep_ind' with
    (P := fun A c bdr ρ e i Rs r I =>
            Θ c = A -> wf_cenv Θ ρ ->
            forall c', c' <> c -> approx_int c' (ai_int (Θ c')) I)
    (P0 := fun A c bdr ρ e i Rs r I =>
             Θ c = A -> wf_cenv Θ ρ ->
             forall c', approx_int c' (ai_int (Θ c')) I);
    intros HΘ Henv.
  - (* Cbstep_ret *)
    intros c' _; apply approx_int_empty.
  - (* Cbstep_fun *)
    intros c' _.
    apply IHHstep; [exact HΘ |].
    apply wf_cenv_set; [exact Henv |].
    constructor; [exact HΘ |].
    constructor; exact Henv.
  - (* Cbstep_app_External: the edge is checked on the callee's side *)
    intros c'' Hc''.
    match goal with
    | [Hget : M.get _ ρ = Some _, Hgetl : get_list _ ρ = Some _,
       Hset : set_lists _ _ _ = Some _ |- _] =>
        destruct (wf_cenv_callee Henv Hget Hgetl Hset) as [HΘ' Henv']
    end.
    subst.
    apply approx_int_add; [apply approx_int_singleton | eapply IHHstep; eauto].
    + intros _ Heq; exfalso; apply Hc''; symmetry; exact Heq.
    + intros Heq _; subst c''; auto.
    + intros _ Heq; exfalso; apply Hc''; symmetry; exact Heq.
  - (* Cbstep_app_Internal: the edge does not involve other units *)
    intros c'' Hc''.
    match goal with
    | [Hget : M.get _ ρ = Some _, Hgetl : get_list _ ρ = Some _,
       Hset : set_lists _ _ _ = Some _ |- _] =>
        destruct (wf_cenv_callee Henv Hget Hgetl Hset) as [HΘ' Henv']
    end.
    apply approx_int_add; [apply approx_int_singleton | eapply IHHstep; eauto].
    + intros Heq _; exfalso; apply Hc''; symmetry; exact Heq.
    + intros Heq _; exfalso; apply Hc''; symmetry; exact Heq.
    + intros _ Heq; exfalso; apply Hc''; symmetry; exact Heq.
  - (* CbstepF_OOT *)
    intros c'; apply approx_int_empty.
  - (* CbstepF_Step: the unit itself checks its own view *)
    intros c'.
    destruct (Nat.eq_dec c' c) as [Heq | Hneq].
    + subst c'; rewrite HΘ; assumption.
    + eapply IHHstep; eauto.
Qed.

Lemma cbstep_fuel_approx_int_handover Θ A c bdr ρ e i Rs r I :
  Θ c = A ->
  wf_cenv Θ ρ ->
  cbstep_fuel A c bdr ρ e i Rs r I ->
  forall c', approx_int c' (ai_int (Θ c')) I.
Proof.
  intros HΘ Henv Hstep c'.
  destruct Hstep as [e' Rs' | e' i' Rs' r' I' Hcb Hres Hint].
  - apply approx_int_empty.
  - destruct (Nat.eq_dec c' c) as [Heq | Hneq].
    + fcrush.
    + eapply cbstep_approx_int_handover_aux; eauto.
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

  Definition E' (P : nat -> wval -> clval -> Prop) (A : analysis_result) (c : color) (bdr : bool) (i : nat) (ρ1 : env) (ρ2 : cenv) (e : exp) (Rs : avals) : Prop :=
    forall j1 r1,
      j1 <= i ->
      bstep_fuel ρ1 e j1 r1 ->
      exists j2 r2 I2,
        cbstep_fuel A c bdr ρ2 e j2 Rs r2 I2 /\
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

                  (* the closure is recorded at its defining unit *)
                  (AVfun l2 f2 xs2 e2 \in ai_env A2 f2) /\
                  approx_env (ai_env A2) ρ2 /\

                  (* the closure environment invariants *)
                  cescaped_env c2 ρ2 /\
                  cbinding_env c2 A2 ρ2 /\

                  match i with
                  | 0 => True
                  | S i0 =>
                      forall (bdr : bool) j c vs1 vs2 ρ3 ρ4,
                        j <= i0 ->
                        Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                        set_lists xs1 vs1 (M.set f1 (Tag l1 (Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                        set_lists xs2 vs2 (M.set f2 (CTag A2 c2 l2 (CVfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->

                        (* invariants for escaped values and variable bindings *)
                        Forall (cescaped c2) vs2 ->
                        Forall2 (cbinding c2 A2) xs2 vs2 ->

                        (* invariants for coloring *)
                        (* internal call: the arguments flow to the parameters should be internal *)
                        (c2 = c -> Forall2 (fun x v => approx_vals (ai_env A2 x) v) xs2 vs2) ->
                        (* foreign call: the closure has escaped its unit *)
                        (c2 <> c -> AVfun l2 f2 xs2 e2 \in ai_esc A2) ->

                        (* invariants for closures that may cross the program boundary *)
                        (if bdr then AVfun l2 f2 xs2 e2 \in ai_esc A2 else True) ->

                        E' V A2 c2 bdr (i0 - (i0 - j)) ρ3 ρ4 e1 (ai_ret A2 l2)
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

  (* Only closures are related. *)
  Lemma V_cres_is_fun {i v1 v2} :
    V i v1 v2 ->
    cres_is_fun (CRes v2).
  Proof.
    intros HV.
    destruct v2 as [A2 [c2 l2] w2].
    destruct w2 as [f2 ρ2 xs2 e2 | t2 vs2]; simpl; [exact I |].
    destruct v1 as [l1 w1].
    destruct w1 as [f1 ρ1 xs1 e1 | t1 vs1]; destruct i as [| i']; simpl in HV; fcrush.
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
  (* Relates the environments of the unit wearing `c`: besides the pointwise
     value relation, the target environment is approximated by the abstract
     environment of `θ c`, every foreign value in it has escaped, and every
     closure of the unit itself is approximated by its own allocation site. *)
  Definition G c i Γ1 ρ1 ρ2 :=
    wf_env Γ1 ρ1 /\
      wf_cenv θ ρ2 /\
      approx_env (ai_env (θ c)) ρ2 /\
      cescaped_env c ρ2 /\
      cbinding_env c (θ c) ρ2 /\
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
  Proof. unfold G. fcrush. Qed.

  Lemma G_wf_env_l {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    wf_env Γ1 ρ1.
  Proof. unfold G. fcrush. Qed.

  Lemma G_wf_cenv_r {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    wf_cenv θ ρ2.
  Proof. unfold G. fcrush. Qed.

  Lemma G_approx_env {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    approx_env (ai_env (θ c)) ρ2.
  Proof. unfold G. intros [_ [_ [Haenv _]]]. exact Haenv. Qed.

  Lemma G_cescaped_env {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    cescaped_env c ρ2.
  Proof. unfold G. intros [_ [_ [_ [Hesc _]]]]. exact Hesc. Qed.

  Lemma G_cbinding_env {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    cbinding_env c (θ c) ρ2.
  Proof. unfold G. intros [_ [_ [_ [_ [Hex _]]]]]. exact Hex. Qed.

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
    destruct H as [Hwf [Href [Haenv [Hesc [Hex HG]]]]].
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
      approx_vals (ai_env (θ c) x) v2 ->
      cescaped c v2 ->
      cbinding c (θ c) x v2 ->
      G c i (x |: Γ1) (M.set x v1 ρ1) (M.set x v2 ρ2).
  Proof.
    unfold G.
    intro HG.
    pose proof HG as HG'.
    intros.

    destruct HG as [Hwf [Href [Haenv [Hesc [Hex HG]]]]].
    split.
    eapply wf_env_set; eauto.
    eapply V_wf_val_l; eauto.

    split.
    eapply wf_cenv_set; eauto.
    eapply V_wf_cval_r; eauto.

    split.
    eapply approx_env_set; eauto.

    split.
    eapply cescaped_env_set; eauto.

    split.
    eapply cbinding_env_set; eauto.

    intros.
    destruct (M.elt_eq x0 x); subst.
    - repeat rewrite M.gss in *.
      fcrush.
    - repeat (rewrite M.gso in *; auto).
      fcrush.
  Qed.

  (* Binding a variable that is not in [Γ1] on the source side only
   preserves the environment relation. *)
  Lemma G_set_unused {c i Γ1 ρ1 ρ2} y v :
    G c i Γ1 ρ1 ρ2 ->
    ~ (y \in Γ1) ->
    wf_val v ->
    G c i Γ1 (M.set y v ρ1) ρ2.
  Proof.
    unfold G.
    intros HG Hy Hv.
    destruct HG as [Hwf1 [Hwf2 [Haenv [Hesc [Hex HGv]]]]].
    split; [| split; [| split; [| split; [| split ]]]].
    - eapply wf_env_subset.
      + eapply wf_env_set; eassumption.
      + unfold Ensembles.Included, Ensembles.In.
        intros z Hz. right. assumption.
    - exact Hwf2.
    - exact Haenv.
    - exact Hesc.
    - exact Hex.
    - intros z Hz.
      destruct (HGv z Hz) as [v1 [v2 [Hg1 [Hg2 HV]]]].
      exists v1, v2.
      rewrite M.gso by (intros Heq; subst; contradiction).
      split; [ exact Hg1 | split; [ exact Hg2 | exact HV ] ].
  Qed.

  Lemma G_set_lists {c i Γ1 ρ1 ρ2}:
    G c i Γ1 ρ1 ρ2 ->
    forall {xs vs1 vs2 ρ3 ρ4},
      Forall2 (V i) vs1 vs2 ->
      Forall2 (fun x v => approx_vals (ai_env (θ c) x) v) xs vs2 ->
      Forall (cescaped c) vs2 ->
      Forall2 (cbinding c (θ c)) xs vs2 ->
      set_lists xs vs1 ρ1 = Some ρ3 ->
      set_lists xs vs2 ρ2 = Some ρ4 ->
      G c i (FromList xs :|: Γ1) ρ3 ρ4.
  Proof.
    intros HG xs.
    induction xs; simpl; intros.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      inv H3; inv H4.
      eapply G_subset; eauto; normalize_sets;
        rewrite Union_Empty_set_neut_l; eauto;
        apply Included_refl.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
      destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
      inv H; inv H0; inv H1; inv H2; inv H3; inv H4.
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
      + destruct HV as [Heqv [Heql [Heqe [Havs [Hsite [Haenv [Hesc [Hloc HV]]]]]]]]; subst.
        repeat (split; eauto); intros.
    - repeat (split; auto).
      destruct v; destruct c0; try contradiction.
      destruct HV as [Heqv [Heql [Heqe [Havs [Hsite [Haenv [Hesc [Hloc HV]]]]]]]]; subst.
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

  Lemma E_mono {A Rs c bdr ρ1 ρ2 e} i j:
    E A c bdr i ρ1 ρ2 e Rs ->
    j <= i ->
    E A c bdr j ρ1 ρ2 e Rs.
  Proof.
    unfold E, R, E', R'.
    intros.
    destruct (H j1 r1) as [j2 [r2 [I2 [Hr2 HR]]]]; auto; try lia.
    exists j2, r2, I2; split; eauto.
    apply R_mono with (i - j1); try lia; auto.
  Qed.

  Lemma G_mono {c Γ1 ρ1 ρ2} i j:
    G c i Γ1 ρ1 ρ2 ->
    j <= i ->
    G c j Γ1 ρ1 ρ2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hwf1 [Hwf2 [Haenv [Hesc [Hex HG]]]]].
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

  (* `Rs` is quantified inside as function bodies are checked against other return sets. *)
  Definition well_annotated A c Γ e : Prop :=
    θ c = A /\
    forall Rs (bdr : bool),
      acheck A e Rs ->
      (if bdr then (Rs \subset (ai_esc A)) else True) ->
      forall i ρ1 ρ2,
        G c i Γ ρ1 ρ2 ->
        E A c bdr i ρ1 ρ2 e Rs.

  Lemma ret_compat A c Γ x :
    θ c = A ->
    (x \in Γ) ->
    well_annotated A c Γ (Eret x).
  Proof.
    unfold well_annotated, E, E', R, R', Ensembles.Included, Ensembles.In.
    intros; simpl.
    split; auto; intros.

    inv H5.
    - fcrush.
    - destruct r1.
      fcrush.
      inv H1; inv H6.
      edestruct (G_get H3) as [v2 [Heqv2 HV]]; eauto.
      exists 1, (CRes v2), (Empty_set _); split; eauto; simpl.
      + econstructor; eauto.

        * destruct (approx_env_get (G_approx_env H3) Heqv2) as [av [Hav Happrox]]; eauto.
        * eapply approx_int_empty; eauto.

        * destruct bdr; simpl; auto.
          unfold cboundary.
          destruct v2; destruct c0; destruct c1; simpl; auto.

          -- assert (Hcbenv : cbinding_env c (θ c) ρ2) by eauto using G_cbinding_env.
             pose proof (cbinding_env_get _ _ Hcbenv Heqv2) as Hloc_x.
             unfold cbinding in Hloc_x.
             destruct (Nat.eq_dec c0 c); subst.
             ++ destruct Hloc_x as [Hown _].
                edestruct (Hown eq_refl);
                  unfold Ensembles.Included, Ensembles.In in *;
                  fcrush.
             ++ destruct Hloc_x as [_ Hext].
                specialize (Hext n).
                pose proof (cescaped_env_get x _ (G_cescaped_env H3) Heqv2) as Hesc.
                unfold cescaped in *.
                fcrush.
          -- destruct w; destruct i; simpl in HV; fcrush.

        * split.
          -- eapply cescaped_env_get; [eapply G_cescaped_env; eauto | exact Heqv2].
          -- eapply cflows_subset.
             ++ eapply cbinding_cflows; eauto.
                eapply cbinding_env_get; [eapply G_cbinding_env; eauto | exact Heqv2].
             ++ assumption.

      + eapply V_mono; eauto; lia.
  Qed.

  Lemma Vfun_V Γ f l A c xs e  :
    occurs_free e \subset FromList xs :|: (f |: Γ) ->
    well_annotated A c (FromList xs :|: (f |: Γ)) e ->
    acheck A e (ai_ret A l) ->
    forall {i ρ1 ρ2},
      wf_val (Tag l (Vfun f ρ1 xs e)) ->
      wf_cval θ (CTag A c l (CVfun f ρ2 xs e)) ->
      (AVfun l f xs e) \in (ai_env A f) ->
      approx_vals (ai_env A f) (CTag A c l (CVfun f ρ2 xs e)) ->
      G c i Γ ρ1 ρ2 ->
      V i (Tag l (Vfun f ρ1 xs e)) (CTag A c l (CVfun f ρ2 xs e)).
  Proof.
    unfold well_annotated.
    intros HS [HU He] Hack i.
    induction i; simpl; subst; intros; auto;
      assert (Haenv : approx_env (ai_env (θ c)) ρ2) by eauto using G_approx_env;
      assert (Hesc_env : cescaped_env c ρ2) by eauto using G_cescaped_env;
      assert (Hloc_env : cbinding_env c (θ c) ρ2) by eauto using G_cbinding_env;
      repeat (split; auto);
      intros; (repeat split; auto).

    eapply (He _ _ Hack) with (i := (i - (i - j))) (ρ1 :=  ρ3) (ρ2 := ρ4); eauto.
    - destruct bdr; auto.
      destruct (θ_escape_ok c) as [_ Hres].
      fcrush.
    - eapply G_subset; eauto.
      eapply G_set_lists; eauto.
      eapply G_set; eauto.
      + apply G_mono with (S i); eauto; lia.
      + apply V_mono with i; try lia.
        eapply IHi; eauto.
        apply G_mono with (S i); eauto; lia.
      + eauto using cescaped_defining.
      + unfold cbinding; simpl.
        split; intros; fcrush.
      + destruct (Nat.eq_dec c0 c); try auto.
        eapply set_lists_approx_top; eauto.
        edestruct θ_escape_ok as [_ Hesc_fun]; eauto.
        eapply Hesc_fun; eauto.
      + eapply Included_refl; eauto.
  Qed.

  Lemma fun_compat A c Γ e k f l xs :
    occurs_free e \subset FromList xs :|: (f |: Γ) ->
    well_annotated A c (FromList xs :|: (f |: Γ)) e ->
    well_annotated A c (f |: Γ) k ->
    well_annotated A c Γ (Efun f l xs e k).
  Proof.
    unfold well_annotated, E, E'.
    intros HS He [HU Hk].
    split; auto; intros.

    inv H3.
    - fcrush.
    - destruct r1.
      fcrush.
      assert (Hwfρ1 : wf_env Γ ρ1) by eauto using G_wf_env_l.
      assert (Hwfρ2 : wf_cenv θ ρ2) by eauto using G_wf_cenv_r.
      inv H; inv H4.
      assert (Happrox : approx_vals (ai_env (θ c) f) (CTag (θ c) c l (CVfun f ρ2 xs e))).
      {
        unfold approx_vals.
        eexists; split; sfirstorder.
      }

      edestruct (Hk Rs bdr H12 H0 (i - 1) (M.set f (Tag l (Vfun f ρ1 xs e)) ρ1) (M.set f (CTag (θ c) c l (CVfun f ρ2 xs e)) ρ2)) with (j1 := c0) (r1 := (Res w)) as [j2 [r2 [I2 [Hk2 Rr]]]]; eauto; try lia.
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
        exists (S j2), (CRes w2), I2; split; eauto.
        econstructor; eauto.
        eapply cbstep_fuel_approx_res; eauto.
        eapply cbstep_fuel_approx_int; eauto.
        destruct bdr; [eapply cbstep_fuel_cboundary_res; eauto | exact I].
        eapply cbstep_fuel_cres_inv; eauto.
        eapply R_mono; eauto; lia.
  Qed.

  (* A value that the unit `c` hands over to another unit `c1`, through a
     variable whose value set escapes, has escaped from its own unit:
     - if it belongs to `c1`, there is nothing to show;
     - if it belongs to `c`, its exact site (or, for a constructor, some
       approximating value) is in the value set of the variable, hence in
       `ai_esc (θ c)`;
     - if it belongs to a third unit, it had escaped already. *)
  Lemma cescaped_handover {c x v} :
    wf_cval θ v ->
    cescaped c v ->
    cbinding c (θ c) x v ->
    approx_vals (ai_env (θ c) x) v ->
    ai_env (θ c) x \subset ai_esc (θ c) ->
    forall c1, cescaped c1 v.
  Proof.
    intros Hwf Hesc Hloc Happrox Hsub c1.
    destruct v as [A' [c' l'] w].
    pose proof (wf_cval_CTag_inv Hwf) as [HA' _]; subst.
    destruct (Nat.eq_dec c' c1) as [Heq1 | Hneq1].
    - (* c1 is the defining unit *)
      subst c'.
      eauto using cescaped_defining.
    - (* c1 is not the defining unit *)
      destruct (Nat.eq_dec c' c) as [Heqc | Hneqc].
      + (* c is the defining unit -> v has escaped but bound by x in unit c -> only the defining unit, c', matters *)
        subst c'.
        unfold cescaped.
        destruct w as [f' ρ' xs' e' | t vs]; intros _.
        * unfold cbinding in Hloc.
          destruct Hloc as [Hown _].
          destruct (Hown eq_refl) as [Hin | [Hin _]].
          -- eauto using Hsub.
          -- auto.
        * unfold approx_vals in *.
          destruct Happrox as [av [Hav Hap]]; eauto.
      + (* c is not the defining unit *)
        (* the value belongs to a third unit: it had escaped already -> only the defining unit, c', matters *)
        unfold cescaped in *.
        destruct w; simpl in Hesc |- *; intros _.
        * auto.
        * apply Hesc; exact Hneqc.
  Qed.

  Lemma cescaped_handover_list {c c1 i Γ ρ1 ρ2 xs vs} :
    G c i Γ ρ1 ρ2 ->
    Forall (fun x => ai_env (θ c) x \subset ai_esc (θ c)) xs ->
    get_list xs ρ2 = Some vs ->
    Forall (cescaped c1) vs.
  Proof.
    intros HG Hsub.
    revert vs.
    induction Hsub as [| x xs Hxsub Hsub IH]; simpl; intros vs Hget.
    - inv Hget; constructor.
    - destruct (M.get x ρ2) as [v |] eqn:Hx; [| discriminate Hget].
      destruct (get_list xs ρ2) as [vs' |] eqn:Hxs; [| discriminate Hget].
      inv Hget.
      constructor.
      + apply (@cescaped_handover c x v).
        * eapply wf_cenv_get; [eapply G_wf_cenv_r; eauto | exact Hx].
        * eapply cescaped_env_get; [eapply G_cescaped_env; eauto | exact Hx].
        * eapply cbinding_env_get; [eapply G_cbinding_env; eauto | exact Hx].
        * eapply approx_env_get; [eapply G_approx_env; eauto | exact Hx].
        * exact Hxsub.
      + eapply IH; eauto.
  Qed.

  (* A value handed over by the unit `c` to another unit `c1`, at a parameter
     whose value set contains `AVtop`, is bound as `cbinding` requires:
     - a closure of `c1` itself comes back from the context, so it has escaped
       from `c1` and `AVtop` stands for it at the parameter;
     - any other value is foreign to `c1`, hence approximated by `AVtop`. *)
  Lemma cbinding_handover {c c1 x v} :
    c1 <> c ->
    wf_cval θ v ->
    cescaped c v ->
    AVtop \in ai_env (θ c1) x ->
    cbinding c1 (θ c1) x v.
  Proof.
    intros Hneq Hwf Hesc Htop.
    destruct v as [A' [c' l'] w].
    pose proof (wf_cval_CTag_inv Hwf) as [HA' _].
    subst A'.
    destruct w as [f ρ xs e | t vs]; unfold cbinding, cescaped in *.
    - split.
      + intros Heq; subst c'.
        right; split; [apply Hesc; exact Hneq | exact Htop].
      + intros _; exact Htop.
    - intros _; exact Htop.
  Qed.

  Lemma cbinding_handover_list {c c1 xs vs ρ ρ'} :
    c1 <> c ->
    Forall (wf_cval θ) vs ->
    Forall (cescaped c) vs ->
    (forall x, List.In x xs -> AVtop \in ai_env (θ c1) x) ->
    set_lists xs vs ρ = Some ρ' ->
    Forall2 (cbinding c1 (θ c1)) xs vs.
  Proof.
    intros Hneq Hwf Hesc Htop Hset.
    revert vs ρ' Hwf Hesc Htop Hset.
    induction xs as [| x xs IH]; intros vs ρ' Hwf Hesc Htop Hset; simpl in Hset.
    - destruct vs as [| v vs]; [constructor | discriminate Hset].
    - destruct vs as [| v vs]; [discriminate Hset |].
      destruct (set_lists xs vs ρ) as [ρ'' |] eqn:Heq; [| discriminate Hset].
      inv Hwf; inv Hesc.
      constructor.
      + eapply cbinding_handover;
          [exact Hneq | assumption | assumption | apply Htop; left; reflexivity].
      + eapply IH; [eassumption | eassumption | | exact Heq].
        intros y Hy; apply Htop; right; exact Hy.
  Qed.

  (* `cescaped_handover` over an arbitrary value set `avs` that escapes. *)
  Lemma cescaped_handover_avs {c avs v} :
    wf_cval θ v ->
    cescaped c v ->
    cflows c (θ c) avs v ->
    approx_vals avs v ->
    avs \subset ai_esc (θ c) ->
    forall c1, cescaped c1 v.
  Proof.
    intros Hwf Hesc Hfl Happrox Hsub c1.
    destruct v as [A' [c' l'] w].
    pose proof (wf_cval_CTag_inv Hwf) as [HA' _]; subst.
    destruct (Nat.eq_dec c' c1) as [Heq1 | Hneq1].
    - (* c1 is the defining unit *)
      subst c'.
      eauto using cescaped_defining.
    - destruct (Nat.eq_dec c' c) as [Heqc | Hneqc].
      + (* c is the defining unit: the value flows through `avs`, which escapes *)
        subst c'.
        unfold cescaped.
        destruct w as [f' ρ' xs' e' | t vs]; intros _.
        * unfold cflows in Hfl.
          destruct Hfl as [Hown _].
          destruct (Hown eq_refl) as [Hin | [Hin _]].
          -- exact (Hsub _ Hin).
          -- exact Hin.
        * destruct Happrox as [av [Hav Hap]].
          exists av; split; [exact (Hsub _ Hav) | exact Hap].
      + (* the value belongs to a third unit: it had escaped already *)
        unfold cescaped in *.
        destruct w; simpl in Hesc |- *; intros _.
        * auto.
        * apply Hesc; exact Hneqc.
  Qed.

  (* `cbinding_handover` over an arbitrary value set `avs` holding `AVtop`. *)
  Lemma cflows_handover {c c1 avs v} :
    c1 <> c ->
    wf_cval θ v ->
    cescaped c v ->
    AVtop \in avs ->
    cflows c1 (θ c1) avs v.
  Proof.
    intros Hneq Hwf Hesc Htop.
    destruct v as [A' [c' l'] w].
    pose proof (wf_cval_CTag_inv Hwf) as [HA' _].
    subst A'.
    destruct w as [f ρ xs e | t vs]; unfold cflows, cescaped in *.
    - split.
      + intros Heq; subst c'.
        right; split; [apply Hesc; exact Hneq | exact Htop].
      + intros _; exact Htop.
    - intros _; exact Htop.
  Qed.

  (* A result returned by the unit `c` into an escaping return set `Rs1` is
     handed over to the unit `c1`, which receives it into `Rs` as an unknown
     value (`AVtop ∈ Rs`). *)
  Lemma cres_inv_handover {c c1 Rs1 Rs r} :
    c1 <> c ->
    wf_cres θ r ->
    approx_res Rs1 r ->
    cres_inv c (θ c) Rs1 r ->
    Rs1 \subset ai_esc (θ c) ->
    AVtop \in Rs ->
    cres_inv c1 (θ c1) Rs r.
  Proof.
    intros Hneq Hwf Happrox Hok Hsub Htop.
    destruct r as [| v]; [exact I |].
    pose proof (wf_cres_CRes_inv Hwf) as Hwfv.
    destruct Hok as [Hesc Hfl].
    assert (Happrox_v : approx_vals Rs1 v)
      by (inv Happrox; eexists; split; eauto).
    split.
    - exact (cescaped_handover_avs Hwfv Hesc Hfl Happrox_v Hsub c1).
    - exact (cflows_handover Hneq Hwfv Hesc Htop).
  Qed.

  Lemma app_compat A Γ xs f l c :
    θ c = A ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    well_annotated A c Γ (Eapp f l xs).
  Proof.
    unfold well_annotated, E, E'.
    intross HU Hf Hxs; simpl.
    split; auto; intros.

    inv H3.
    - fcrush.
    - destruct r1.
      fcrush.
      inv H; inv H4.
      edestruct (G_get H1 f) as [fv2 [Heqfv2 HV]]; eauto.
      destruct i.
      inv H2.
      rename w into v.
      destruct fv2; destruct c1; destruct c2; simpl in HV; invc.
      2 : { fcrush. }
      destruct HV as [Hwf1 [Hwf2 [Heql [Heqf [Heqxs [Heqe [Havs [Hsite [Haenv [Hesc_t [Hloc_t HV]]]]]]]]]]]; subst; invc.
      rename a into A0.
      edestruct (G_get_list H1 xs vs) as [vs2 [Heqvs2 Vvs]]; eauto; invc.

      destruct (set_lists_length3 (M.set v0 (CTag A0 c1 l0 (CVfun v0 t l1 e0)) t) l1 vs2) as [ρ4 Heqρ4].
      unfold clval in *.
      rewrite (set_lists_length_eq _ _ _ _ H13); auto.
      eapply Forall2_length; eauto.

      assert (HE : E A0 c1 (negb (c1 =? c)) (i - (i - i)) ρ'' ρ4 e0 (ai_ret A0 l0)).
      {
        eapply (HV _ i c vs vs2); eauto.
        - apply V_mono_Forall with (S i); auto; lia.
        - destruct (Nat.eq_dec c1 c) as [Heqc | Hneqc].
          + (* internal call *)
            subst c1.
            eapply cescaped_env_get_list; [eapply G_cescaped_env; eauto | exact Heqvs2].
          + (* foreign call: the caller approximates the callee by `AVtop`, so its arguments escape *)
            assert (Htop : AVtop \in ai_env (θ c) f).
            { pose proof (cbinding_env_get f _ (G_cbinding_env H1) Heqfv2) as Hloc_f.
              unfold cbinding in Hloc_f.
              destruct Hloc_f as [_ Hforeign].
              exact (Hforeign Hneqc). }
            destruct (H10 Htop) as [Hargs _].
            eapply cescaped_handover_list; eauto.

        - destruct (Nat.eq_dec c1 c) as [Heqc | Hneqc]; subst.
          + inv Hwf2.
            assert (Hcbinding_xs : Forall2 (cbinding c (θ c)) xs vs2).
            { eapply cbinding_env_get_list; [eapply G_cbinding_env; eauto | exact Heqvs2]. }
            assert (Hcbinding_f : cbinding c (θ c) f (CTAG cval (θ c) (c, l0) (CVfun v0 t l1 e0))).
            {
              eapply cbinding_env_get; [eapply G_cbinding_env; eauto | eauto ].
            }
            unfold cbinding in Hcbinding_f.
            destruct Hcbinding_f as [Hfown _].

            destruct (Hfown eq_refl) as [Hin | [Hesc Htop]].
            * edestruct (H9 _ _ _ _ Hin) as [_ [_ [Hsub _]]]; eauto.
              eapply cbinding_subset_list; eauto.
            * destruct (H10 Htop) as [_ [_ Hesc_fun]].
              destruct (Hesc_fun _ _ _ _ Hesc) as [_ [_ [_ [Hsub _]]]].
              eapply cbinding_subset_list; eauto.

          + assert (Htop : AVtop \in ai_env (θ c) f).
            { pose proof (cbinding_env_get f _ (G_cbinding_env H1) Heqfv2) as Hloc_f.
              unfold cbinding in Hloc_f.
              destruct Hloc_f as [_ Hforeign].
              exact (Hforeign Hneqc). }
            destruct (H10 Htop) as [Hargs [HRs Hesc_fun]].
            (* the parameters belong to the callee's unit: its closure has
               escaped, so by `escapes_ok` every parameter holds `AVtop` *)
            pose proof (wf_cval_CTag_inv Hwf2) as [HA0 _].
            subst A0.

            assert (Hfesc : AVfun l0 v0 l1 e0 \in ai_esc (θ c1)).
            { pose proof (cescaped_env_get f _ (G_cescaped_env H1) Heqfv2) as Hf_esc.
              unfold cescaped in Hf_esc.
              exact (Hf_esc Hneqc). }
            destruct (θ_escape_ok c1) as [_ Hesc_ok].
            destruct (Hesc_ok _ _ _ _ Hfesc) as [Hparams _].
            eapply (cbinding_handover_list Hneqc);
              [ eapply wf_cenv_get_list; [eapply G_wf_cenv_r; eauto | exact Heqvs2]
              | eapply cescaped_env_get_list; [eapply G_cescaped_env; eauto | exact Heqvs2]
              | exact Hparams
              | exact Heqρ4 ].

        - intros; subst.
          inv Hwf2.
          pose proof (approx_env_get_list (G_approx_env H1) _ _ Heqvs2) as Happrox_xs.
          pose proof (cbinding_env_get f _ (G_cbinding_env H1) Heqfv2) as Hloc_f.
          unfold cbinding in Hloc_f.
          destruct Hloc_f as [Hint _].
          specialize (Hint eq_refl).
          inv Hint.
          * (* internal *)
            edestruct H9 as [_ [_ [Hsub _]]]; eauto.
            eapply approx_vals_subset_list; eauto.
          * (* foreign *)
            inv H; eauto.
            eapply set_lists_approx_top; eauto.
            destruct (θ_escape_ok c) as [_ Hesc_ok].
            eapply Hesc_ok; eauto.

        - intros Hneq.
          pose proof (cescaped_env_get f _ (G_cescaped_env H1) Heqfv2) as Hf_esc.
          unfold cescaped in Hf_esc.
          exact (Hf_esc Hneq).

        - (* only a foreign call runs the body at the boundary, and then the
             closure has escaped *)
          destruct (Nat.eqb_spec c1 c); simpl; auto.
          pose proof (cescaped_env_get f _ (G_cescaped_env H1) Heqfv2) as Hf_esc.
          unfold cescaped in Hf_esc; eauto.
      }

      apply (E_mono _ i) in HE; try lia.
      unfold E, E' in HE.
      destruct (HE c0 (Res v)) as [j2 [r2 [I2 [He0 Rr]]]]; try lia; auto.
      edestruct R_res_inv_l as [v2 [Heqv2 HVv]]; eauto; subst.
      inv Hwf2.
      destruct (Nat.eq_dec c1 c); subst.
      + assert (Hb : negb (c =? c) = false) by fcrush.
        rewrite Hb in He0.

        exists (S j2), (CRes v2), (((c, l0), (c, l)) |: I2); split; eauto.

        pose proof (approx_env_get_list (G_approx_env H1) _ _ Heqvs2) as Happrox_xs.

        assert (Hint : Ensembles.In aval (ai_env (θ c) f) (AVfun l0 v0 l1 e0) \/
                        (Ensembles.In aval (ai_esc (θ c)) (AVfun l0 v0 l1 e0) /\ Ensembles.In aval (ai_env (θ c) f) AVtop)).
        {
          pose proof (cbinding_env_get f _ (G_cbinding_env H1) Heqfv2) as Hloc_f.
          unfold cbinding in Hloc_f.
          destruct Hloc_f as [Hint _].
          apply (Hint eq_refl).
        }

        (* what the callee may return can be returned from this call site *)
        assert (Hret : ai_ret (θ c) l0 \subset Rs).
        { destruct Hint as [Hin | [Hesc Htop]].
          - destruct (H9 _ _ _ _ Hin) as [_ [_ [_ Hsub]]]; exact Hsub.
          - destruct (H10 Htop) as [_ [_ Hesc_fun]].
            destruct (Hesc_fun _ _ _ _ Hesc) as [_ [_ [_ [_ Hsub]]]]; exact Hsub. }

        assert (Hok : cres_inv c (θ c) Rs (CRes v2))
          by (eapply cres_inv_subset; [eapply cbstep_fuel_cres_inv; eauto | exact Hret]).

        econstructor; eauto.
        * eapply Cbstep_app_Internal; eauto.

          assert (Happrox : approx_env (ai_env (θ c)) (M.set v0 (CTag (θ c) c l0 (CVfun v0 t l1 e0)) t)) by eauto using approx_env_set.
          eapply (approx_env_set_lists Happrox l1 vs2); eauto.

          inv Hint.
          -- (* internal *)
            edestruct H9 as [_ [_ [Hsub _]]]; eauto.
            eapply approx_vals_subset_list; eauto.

          -- (* foreign *)
            inv H; eauto.
            eapply set_lists_approx_top; eauto.
            destruct (θ_escape_ok c) as [_ Hesc_ok].
            eapply Hesc_ok; eauto.

        * assert (approx_res (ai_ret (θ c) l0) (CRes v2)) by eauto using cbstep_fuel_approx_res.
          eapply approx_res_subset; eauto.

        * assert (HI2 : approx_int c (ai_int (θ c)) I2) by eauto using cbstep_fuel_approx_int.
          apply approx_int_add_internal; [| exact HI2].
          destruct Hint as [Hin | [Hesc Htop]].
          -- apply (H7 _ Hin).
          -- destruct (H10 Htop) as [_ [_ Hesc_fun]].
             eapply (Hesc_fun _ _ _ _ Hesc); eauto.

        * (* the result crosses the boundary if `Rs` escapes *)
          destruct bdr; [| exact I].
          eapply (cres_inv_cboundary θ c Rs);
            [ eapply V_wf_cres_r; eauto
            | eapply V_cres_is_fun; eauto
            | exact Hok
            | assumption ].

      + assert (Hb : negb (c1 =? c) = true) by fcrush.
        rewrite Hb in He0.

        exists (S j2), (CRes v2), (((c1, l0), (c, l)) |: I2); split; eauto.
        assert (Hafv : (AVfun l0 v0 l1 e0) \in (ai_esc (θ c1))).
        {
          pose proof (cescaped_env_get f _ (G_cescaped_env H1) Heqfv2) as Hf_esc.
          unfold cescaped in Hf_esc; eauto.
        }

        assert (Htop : AVtop \in ai_env (θ c) f).
        { pose proof (cbinding_env_get f _ (G_cbinding_env H1) Heqfv2) as Hloc_f.
          unfold cbinding in Hloc_f.
          destruct Hloc_f as [_ Hforeign].
          exact (Hforeign n). }

        (* the callee returns into `ai_ret (θ c1) l0`, which escapes from
           `c1`, and the caller receives the result as unknown *)
        assert (Hok : cres_inv c (θ c) Rs (CRes v2)).
        { destruct (θ_escape_ok c1) as [_ Hesc_ok].
          destruct (Hesc_ok _ _ _ _ Hafv) as [_ Hret_esc].
          destruct (H10 Htop) as [_ [HRs _]].
          eapply (cres_inv_handover (not_eq_sym n));
            [ eapply V_wf_cres_r; eauto
            | eapply cbstep_fuel_approx_res; eauto
            | eapply cbstep_fuel_cres_inv; eauto
            | exact Hret_esc
            | exact HRs ]. }

        econstructor; eauto.
        * eapply Cbstep_app_External; eauto.
          -- sfirstorder.

          -- destruct (H10 Htop) as [Hargs _].
             eapply cescaped_handover_list; eauto.

          -- assert (Happrox : approx_env (ai_env (θ c1)) (M.set v0 (CTag (θ c1) c1 l0 (CVfun v0 t l1 e0)) t)) by eauto using approx_env_set.
             eapply (approx_env_set_lists Happrox l1 vs2); eauto.
             pose proof (approx_env_get_list (G_approx_env H1) _ _ Heqvs2) as Happrox_xs.

             eapply set_lists_approx_top; eauto.
             destruct (θ_escape_ok c1) as [_ Hesc_ok].
             eapply Hesc_ok; eauto.

        * (* the result of a foreign call is unknown to the caller: `AVtop ∈ Rs` *)
          destruct (H10 Htop) as [_ [HRs _]].
          econstructor; [exact HRs | constructor].

        * assert (Hltop : (l_top_intro, l) \in (ai_int (θ c))) by fcrush.
          apply approx_int_add.
          -- apply approx_int_singleton.
             ++ intros Heq _; exfalso; exact (n Heq).
             ++ intros Heq _; exfalso; exact (n Heq).
             ++ intros _ _; exact Hltop.
          -- (* the interactions collected by the callee, as seen by our unit *)
            eapply cbstep_fuel_approx_int_handover; eauto.
            destruct (wf_cenv_callee (G_wf_cenv_r H1) Heqfv2 Heqvs2 Heqρ4) as [HΘ1 Henv4]; eauto.

        * (* the result crosses the boundary if `Rs` escapes *)
          destruct bdr; [| exact I].
          eapply (cres_inv_cboundary θ c Rs);
            [ eapply V_wf_cres_r; eauto
            | eapply V_cres_is_fun; eauto
            | exact Hok
            | assumption ].

  Qed.

  Lemma fundamental_property {A c Γ e}:
    θ c = A ->
    well_scoped Γ e ->
    well_annotated A c Γ e.
  Proof.
    intros HU H.
    induction H; intros.
    - eapply ret_compat; eauto.
    - eapply fun_compat; eauto.
      eapply well_scoped_inv; eauto.
    - eapply app_compat; eauto.
    - admit.
    - admit.
    - admit.
    - (* eapply case_nil_compat; eauto. *)
      admit.
    - admit.
  Admitted.

End LR.

(* Top Level *)
(* The top-level consists of two phases: coloring and running. *)

(* Top-level Compilation Unit & Linking *)
(* This is what an analysis should annotate the compilation unit with *)
Inductive cexp : Type :=
| CEunit : analysis_result -> avals -> exp -> cexp
| CElink : var -> cexp -> cexp -> cexp.

Hint Constructors cexp : core.

(* Linking *)
Definition clink x e1 e2 : cexp := CElink x e1 e2.

Inductive occurs_free_top : cexp -> vars :=
| Free_cexp :
  forall e A Rs x,
    occurs_free e x ->
    occurs_free_top (CEunit A Rs e) x

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

Lemma occurs_free_top_cexp A Rs e :
  (occurs_free_top (CEunit A Rs e)) <--> (occurs_free e).
Proof. split; unfold Ensembles.Included, Ensembles.In; fcrush. Qed.

(* Phase 1: Coloring *)
(* Colored Linking Tree *)
(* The result of the preprocessing step.  A `cexp` is colorless: a unit only
   declares the internal labels it claims.  Colors are artificial names handed
   out once, at link time, so that the *dynamic* semantics can tell two units
   apart; nothing in a unit's own source mentions them. *)
Inductive ccexp : Type :=
| CCunit : color -> analysis_result -> avals -> exp -> ccexp
| CClink : var -> ccexp -> ccexp -> ccexp.

Hint Constructors ccexp : core.

(* `coloring c1 ce c2 cce` hands the colors `c1, c1+1, ..., c2-1` to the units
   of `ce`, left to right.  The counter is the whole point: it makes the
   assignment *injective*, which is exactly what `interaction_sound` leans on
   when it concludes, from two labels sharing a color, that they are governed
   by one and the same internal set. *)
Inductive coloring : color -> cexp -> color -> ccexp -> Prop :=
| Coloring_unit :
  forall c A Rs e,
    coloring c (CEunit A Rs e) (S c) (CCunit c A Rs e)

| Coloring_link :
  forall c1 c2 c3 x e1 e2 cce1 cce2,
    coloring c1 e1 c2 cce1 ->
    coloring c2 e2 c3 cce2 ->
    coloring c1 (CElink x e1 e2) c3 (CClink x cce1 cce2).

Hint Constructors coloring : core.

(* `(c, A)` is one of the units of `cce`. *)
Inductive has_unit : ccexp -> color -> analysis_result -> Prop :=
| Has_unit_unit :
  forall A Rs c e,
    has_unit (CCunit c A Rs e) c A

| Has_unit_link1 :
  forall x cce1 cce2 c A,
    has_unit cce1 c A ->
    has_unit (CClink x cce1 cce2) c A

| Has_unit_link2 :
  forall x cce1 cce2 c A,
    has_unit cce2 c A ->
    has_unit (CClink x cce1 cce2) c A.

Hint Constructors has_unit : core.

Lemma coloring_mono {c1 ce c2 cce} :
  coloring c1 ce c2 cce ->
  c1 <= c2.
Proof. intros Hcol; induction Hcol; lia. Qed.

Lemma coloring_range {c1 ce c2 cce} :
  coloring c1 ce c2 cce ->
  forall c A, has_unit cce c A -> c1 <= c < c2.
Proof.
  intros Hcol.
  induction Hcol as [c A e | c1 c2 c3 x e1 e2 cce1 cce2 Hc1 IH1 Hc2 IH2];
    intros c0 A0 Hunit.
  - inv Hunit; lia.
  - inv Hunit.
    + match goal with
      | [Hu : has_unit cce1 c0 A0 |- _] => destruct (IH1 c0 A0 Hu) as [Hlo Hhi]
      end.
      pose proof (coloring_mono Hc2) as Hm; lia.
    + match goal with
      | [Hu : has_unit cce2 c0 A0 |- _] => destruct (IH2 c0 A0 Hu) as [Hlo Hhi]
      end.
      pose proof (coloring_mono Hc1) as Hm; lia.
Qed.

(* Distinct units get distinct colors, so a color names at most one unit. *)
Lemma coloring_unique {c1 ce c2 cce} :
  coloring c1 ce c2 cce ->
  forall c A A',
    has_unit cce c A ->
    has_unit cce c A' ->
    A = A'.
Proof.
  intros Hcol.
  induction Hcol as [c A e | c1 c2 c3 x e1 e2 cce1 cce2 Hc1 IH1 Hc2 IH2];
    intros c0 A0 A0' Hu Hu'.
  - inv Hu; inv Hu'; reflexivity.
  - inv Hu; inv Hu'.
    + match goal with
      | [Ha : has_unit cce1 c0 A0, Hb : has_unit cce1 c0 A0' |- _] =>
          exact (IH1 c0 A0 A0' Ha Hb)
      end.
    + exfalso.
      match goal with
      | [Ha : has_unit cce1 c0 A0, Hb : has_unit cce2 c0 A0' |- _] =>
          destruct (coloring_range Hc1 c0 A0 Ha) as [Hlo Hhi];
          destruct (coloring_range Hc2 c0 A0' Hb) as [Hlo' Hhi']
      end; lia.
    + exfalso.
      match goal with
      | [Ha : has_unit cce2 c0 A0, Hb : has_unit cce1 c0 A0' |- _] =>
          destruct (coloring_range Hc2 c0 A0 Ha) as [Hlo Hhi];
          destruct (coloring_range Hc1 c0 A0' Hb) as [Hlo' Hhi']
      end; lia.
    + match goal with
      | [Ha : has_unit cce2 c0 A0, Hb : has_unit cce2 c0 A0' |- _] =>
          exact (IH2 c0 A0 A0' Ha Hb)
      end.
Qed.

(* `Θ` agrees with the coloring of `cce`. *)
Definition analysis_context_of (Θ : analysis_context) (cce : ccexp) : Prop :=
  forall c A, has_unit cce c A -> A = Θ c.

(* A value crossing the boundary has escaped, whoever holds it. *)
Lemma cboundary_cescaped {c v} :
  cboundary v ->
  cescaped c v.
Proof.
  intros Htop.
  destruct v as [A' [c' l'] w].
  destruct w as [f ρ xs e | t vs]; unfold cboundary in Htop; [| contradiction].
  unfold cescaped; intros _; exact Htop.
Qed.

Lemma cboundary_cescaped_list {c vs} :
  Forall cboundary vs ->
  Forall (cescaped c) vs.
Proof. intros H; induction H; constructor; eauto using cboundary_cescaped. Qed.

(* A value crossing the boundary is bound as `cbinding` requires at a
     variable holding `AVtop`: foreign values are stood for by `AVtop`, and the
     unit's own closures coming back have escaped. *)
Lemma cboundary_cbinding {θ c x v} :
  wf_cval θ v ->
  cboundary v ->
  (AVtop \in ai_env (θ c) x) ->
  cbinding c (θ c) x v.
Proof.
  intros Hwf Htop Hx.
  destruct v as [A' [c' l'] w].
  pose proof (wf_cval_CTag_inv Hwf) as [HA' _].
  subst A'.
  destruct w as [f ρ xs e | t vs]; unfold cboundary in Htop; [| contradiction].
  unfold cbinding; split.
  - intros Heq; subst c'; right; split; [exact Htop | exact Hx].
  - intros _; exact Hx.
Qed.

Lemma cboundary_cbinding_list {θ c xs vs ρ ρ'} :
  Forall (wf_cval θ) vs ->
  Forall cboundary vs ->
  (forall x, List.In x xs -> AVtop \in ai_env (θ c) x) ->
  set_lists xs vs ρ = Some ρ' ->
  Forall2 (cbinding c (θ c)) xs vs.
Proof.
  intros Hwf Htop Hx Hset.
  revert vs ρ' Hwf Htop Hx Hset.
  induction xs as [| x xs IH]; intros vs ρ' Hwf Htop Hx Hset; simpl in Hset.
  - destruct vs as [| v vs]; [constructor | discriminate Hset].
  - destruct vs as [| v vs]; [discriminate Hset |].
    destruct (set_lists xs vs ρ) as [ρ'' |] eqn:Heq; [| discriminate Hset].
    inv Hwf; inv Htop.
    constructor.
    + apply cboundary_cbinding; [assumption | assumption | apply Hx; left; reflexivity].
    + eapply IH; [eassumption | eassumption | | exact Heq].
      intros y Hy; apply Hx; right; exact Hy.
Qed.

(* Top-level Checking Semantics for the *Colored* Top-level Expression *)
(* The colors are already in the tree, so the top-level semantics does not
   mention `Θ` at all: it just runs each unit at the color preprocessing gave
   it, and unions the interactions the units record.
   `Θ` reappears only in the theorems, through `analysis_context_of`. *)
Inductive cbstep_top (ρ : cenv) : ccexp -> fuel -> cres -> interactions -> Prop :=
| CbstepT_link_Res :
  forall {x cce1 cce2 i1 i2 A c l v r I1 I2},
    cbstep_top_fuel ρ cce1 i1 (CRes (CTag A c l v)) I1 ->
    cbstep_top_fuel (M.set x (CTag A c l v) ρ) cce2 i2 r I2 ->
    cbstep_top ρ (CClink x cce1 cce2) (S (i1 + i2)) r (I1 :|: I2)

| CbstepT_link_OOT :
  forall {x cce1 cce2 i I1},
    cbstep_top_fuel ρ cce1 i COOT I1 ->
    cbstep_top ρ (CClink x cce1 cce2) (S i) COOT I1

with cbstep_top_fuel (ρ : cenv) : ccexp -> fuel -> cres -> interactions -> Prop :=
| CbstepTF_unit :
  forall {A c e i Rs r I},
    cbstep_fuel A c true ρ e i Rs r I ->
    cbstep_top_fuel ρ (CCunit c A Rs e) i r I

| CbstepTF_link_OOT :
  forall {x cce1 cce2},
    cbstep_top_fuel ρ (CClink x cce1 cce2) 0 COOT (Empty_set _)

| CbstepTF_link_Step :
  forall {x cce1 cce2 i r I},
    cbstep_top ρ (CClink x cce1 cce2) i r I ->
    cbstep_top_fuel ρ (CClink x cce1 cce2) (S i) r I.

Hint Constructors cbstep_top : core.
Hint Constructors cbstep_top_fuel : core.

Scheme cbstep_top_ind' := Minimality for cbstep_top Sort Prop
with cbstep_top_fuel_ind' := Minimality for cbstep_top_fuel Sort Prop.

(* The step-index is aligned between the two semantics. *)
Lemma cbstep_fuel_cbstep_top_fuel A I c ρ e j Rs r:
  cbstep_fuel A c true ρ e j Rs r I ->
  cbstep_top_fuel ρ (CCunit c A Rs e) j r I.
Proof. intros; eauto. Qed.

Lemma cbstep_top_fuel_cbstep_fuel A Rs c ρ e j r I:
  cbstep_top_fuel ρ (CCunit c A Rs e) j r I ->
  cbstep_fuel A c true ρ e j Rs r I.
Proof. intros H. fcrush. Qed.

(* Every result of the top-level semantics crosses the program boundary. *)
Lemma cbstep_top_cboundary_res :
  forall ρ cce i r I,
    cbstep_top ρ cce i r I ->
    cboundary_res r.
Proof.
  intros ρ cce i r I Hstep.
  induction Hstep using cbstep_top_ind'
    with (P := fun ρ cce i r I => cboundary_res r)
         (P0 := fun ρ cce i r I => cboundary_res r);
    simpl; auto.
  eapply cbstep_fuel_cboundary_res; eauto.
Qed.

Lemma cbstep_top_fuel_cboundary_res ρ cce i r I :
  cbstep_top_fuel ρ cce i r I ->
  cboundary_res r.
Proof.
  intros Hstep.
  inv Hstep; simpl; eauto using cbstep_top_cboundary_res, cbstep_fuel_cboundary_res.
Qed.

(* `analysis_context_of` reads off a single unit, and restricts to subtrees. *)
Lemma analysis_context_of_unit {Θ Rs A c e} :
  analysis_context_of Θ (CCunit c A Rs e) ->
  A = Θ c.
Proof. intros HΘ; exact (HΘ c A (Has_unit_unit A Rs c e)). Qed.

Lemma analysis_context_of_link1 {Θ x cce1 cce2} :
  analysis_context_of Θ (CClink x cce1 cce2) ->
  analysis_context_of Θ cce1.
Proof.
  intros HΘ c A Hunit.
  exact (HΘ c A (Has_unit_link1 x cce1 cce2 c A Hunit)).
Qed.

Lemma analysis_context_of_link2 {Θ x cce1 cce2} :
  analysis_context_of Θ (CClink x cce1 cce2) ->
  analysis_context_of Θ cce2.
Proof.
  intros HΘ c A Hunit.
  exact (HΘ c A (Has_unit_link2 x cce1 cce2 c A Hunit)).
Qed.

(* A value returned by a linked program agrees with Θ. *)
Lemma cbstep_top_wf_cres Θ :
  forall ρ cce i r I,
    cbstep_top ρ cce i r I ->
    analysis_context_of Θ cce ->
    wf_cenv Θ ρ ->
    wf_cres Θ r.
Proof.
  intros ρ cce i r I Hstep.
  induction Hstep as
    [ ρ x cce1 cce2 i1 i2 A c l v r I1 I2 Hfuel1 IH1 Hforeign Hfuel2 IH2
    | ρ x cce1 cce2 i I1 Hfuel1 IH1
    | ρ A c e i Rs r I Hfuel Hres
    | ρ x cce1 cce2
    | ρ x cce1 cce2 i r I Htop IHtop ]
    using cbstep_top_ind'
    with (P := fun ρ cce i r I =>
                 analysis_context_of Θ cce ->
                 wf_cenv Θ ρ ->
                 wf_cres Θ r)
         (P0 := fun ρ cce i r I =>
                  analysis_context_of Θ cce ->
                  wf_cenv Θ ρ ->
                  wf_cres Θ r).

  - (* CbstepT_link_Res: the linked value agrees with Θ, so the second unit
       still runs in a Θ-consistent environment *)
    intros HΘ Hρ.
    pose proof (wf_cres_CRes_inv (IH1 (analysis_context_of_link1 HΘ) Hρ))
      as Hclo.
    pose proof (wf_cenv_set x (CTag A c l v) Hρ Hclo) as Hρx.
    exact (Hfuel2 (analysis_context_of_link2 HΘ) Hρx).

  - (* CbstepT_link_OOT: no value is returned *)
    intros HΘ Hρ.
    apply WF_COOT.

  - (* CbstepTF_unit *)
    intros HΘ Hρ.
    pose proof (analysis_context_of_unit HΘ) as Han.
    eapply (cbstep_fuel_wf_cres Θ A c true ρ e i Rs r I); eauto.

  - (* CbstepTF_link_OOT: no value is returned *)
    intros HΘ Hρ.
    apply WF_COOT.

  - (* CbstepTF_link_Step *)
    intros HΘ Hρ.
    exact (IHtop HΘ Hρ).
Qed.

Lemma cbstep_top_fuel_wf_cres Θ ρ cce i r I :
  analysis_context_of Θ cce ->
  wf_cenv Θ ρ ->
  cbstep_top_fuel ρ cce i r I ->
  wf_cres Θ r.
Proof.
  intros HΘ Hρ Hstep.
  inv Hstep.
  - pose proof (analysis_context_of_unit HΘ) as Hana.
    eapply (cbstep_fuel_wf_cres Θ A); eauto.
  - apply WF_COOT.
  - match goal with
    | [Hs : cbstep_top _ _ _ _ _ |- _] =>
        exact (cbstep_top_wf_cres Θ _ _ _ _ _ Hs HΘ Hρ)
    end.
Qed.

(* Top-level Closure Property *)
(* Each unit of the linked program respects *every* unit's internal set: the
   per-unit theorem applies at each `CCunit`, and linking only unions what the
   two sides recorded.  *)
Lemma cbstep_top_approx_int Θ :
  forall ρ cce i r I,
    cbstep_top ρ cce i r I ->
    analysis_context_of Θ cce ->
    wf_cenv Θ ρ ->
    forall c0, approx_int c0 (ai_int (Θ c0)) I.
Proof.
  intros ρ cce i r I Hstep.
  induction Hstep as
    [ ρ x cce1 cce2 i1 i2 A c l v r I1 I2 Hfuel1 IH1 Hforeign Hfuel2 IH2
    | ρ x cce1 cce2 i I1 Hfuel1 IH1
    | ρ A c e i Rs r I Hfuel Hres
    | ρ x cce1 cce2
    | ρ x cce1 cce2 i r I Htop IHtop ]
    using cbstep_top_ind'
    with (P := fun ρ cce i r I =>
                 analysis_context_of Θ cce ->
                 wf_cenv Θ ρ ->
                 forall c0, approx_int c0 (ai_int (Θ c0)) I)
         (P0 := fun ρ cce i r I =>
                  analysis_context_of Θ cce ->
                  wf_cenv Θ ρ ->
                  forall c0, approx_int c0 (ai_int (Θ c0)) I).

  -
    (* CbstepT_link_Res *)
    intros HΘ Hρ c0.
    pose proof (analysis_context_of_link1 HΘ) as HΘ1.
    pose proof (analysis_context_of_link2 HΘ) as HΘ2.
    pose proof (wf_cres_CRes_inv
                  (cbstep_top_fuel_wf_cres Θ ρ cce1 i1 _ I1 HΘ1 Hρ Hfuel1))
      as Hclo.
    pose proof (wf_cenv_set x (CTag A c l v) Hρ Hclo) as Hρx.
    eapply approx_int_union; eauto.

  - (* CbstepT_link_OOT: only the first unit ran *)
    intros HΘ Hρ c0.
    exact (IH1 (analysis_context_of_link1 HΘ) Hρ c0).

  - (* CbstepTF_unit: hand off to the per-unit theorem *)
    intros HΘ Hρ c0.
    pose proof (analysis_context_of_unit HΘ) as Han.
    symmetry in Han.
    eapply cbstep_fuel_approx_int_handover; eauto.

  - (* CbstepTF_link_OOT: nothing is recorded *)
    intros HΘ Hρ c0.
    apply approx_int_empty.

  - (* CbstepTF_link_Step *)
    intros HΘ Hρ c0.
    exact (IHtop HΘ Hρ c0).
Qed.

Lemma cbstep_top_fuel_approx_int Θ ρ cce i r I :
  cbstep_top_fuel ρ cce i r I ->
  analysis_context_of Θ cce ->
  wf_cenv Θ ρ ->
  forall c0, approx_int c0 (ai_int (Θ c0)) I.
Proof.
  intros Hstep HΘ Hρ c0.
  inv Hstep.
  - pose proof (analysis_context_of_unit HΘ) as Han.
    symmetry in Han.
    eapply cbstep_fuel_approx_int_handover; eauto.
  - apply approx_int_empty.
  - eapply cbstep_top_approx_int; eauto.
Qed.

Lemma cbstep_top_respect Θ :
  forall ρ cce i r I,
    cbstep_top ρ cce i r I ->
    analysis_context_of Θ cce ->
    wf_cenv Θ ρ ->
    forall c0, interactions_respect (ainternals_of (ai_int (Θ c0))) c0 I.
Proof. intros; eauto using approx_int_respect, cbstep_top_approx_int. Qed.

Lemma cbstep_top_fuel_respect Θ ρ cce i r I :
  cbstep_top_fuel ρ cce i r I ->
  analysis_context_of Θ cce ->
  wf_cenv Θ ρ ->
  forall c0, interactions_respect (ainternals_of (ai_int (Θ c0))) c0 I.
Proof. intros; eauto using approx_int_respect, cbstep_top_fuel_approx_int. Qed.

Section LRTop.

  (* Cross-language Logical Relations *)

  Variable θ : analysis_context.
  Hypothesis θ_escape_ok : analysis_context_escape_ok θ.

  Definition E_top' (P : nat -> wval -> clval -> Prop) (i : nat) (ρ1 : env) (e1 : exp) (ρ2 : cenv) (e2 : ccexp) : Prop :=
    forall j1 r1,
      j1 <= i ->
      bstep_fuel ρ1 e1 j1 r1 ->
      exists j2 r2 I2,
        cbstep_top_fuel ρ2 e2 j2 r2 I2 /\
        R' P (i - j1) r1 r2.

  (* Related values that cross the program boundary. *)
  Definition V_top i v1 v2 := V θ i v1 v2 /\ cboundary v2.

  Definition R_top := R' V_top.
  Definition E_top := E_top' V_top.

  Lemma V_V_top i v1 v2 :
    cboundary v2 ->
    (V θ i v1 v2 <-> V_top i v1 v2).
  Proof. unfold V_top; tauto. Qed.

  Lemma R_R_top :
    forall i r1 r2,
      cboundary_res r2 ->
      (R θ i r1 r2 <-> R_top i r1 r2).
  Proof.
    unfold R, R_top, R', cboundary_res.
    intros.
    split; destruct r1; destruct r2; try contradiction;
      intros; eauto;
      eapply V_V_top; eauto.
  Qed.

  Lemma E_E_top c A Rs i ρ1 ρ2 e :
    E θ A c true i ρ1 ρ2 e Rs ->
    E_top i ρ1 e ρ2 (CCunit c A Rs e).
  Proof.
    unfold E, E_top, E', E_top'.
    intros.
    edestruct H as [j2 [r2 [I2 [Hcbstep HR]]]]; eauto.
    exists j2, r2, I2; split; eauto.
    eapply R_R_top; eauto.
    eapply cbstep_fuel_cboundary_res; eauto.
  Qed.

  Lemma E_top_E c A Rs i ρ1 ρ2 e :
    E_top i ρ1 e ρ2 (CCunit c A Rs e) ->
    E θ A c true i ρ1 ρ2 e Rs.
  Proof.
    unfold E, E_top, E', E_top'.
    intros.
    edestruct H as [j2 [r2 [I2 [Hcbstep HR]]]]; eauto.
    exists j2, r2, I2; split; eauto.
    eapply cbstep_top_fuel_cbstep_fuel; eauto.
    eapply R_R_top; eauto.
    eapply cbstep_top_fuel_cboundary_res; eauto.
  Qed.

  Definition G_top i Γ1 ρ1 ρ2 :=
    wf_env Γ1 ρ1 /\
      wf_cenv θ ρ2 /\
      forall x,
        (x \in Γ1) ->
        exists v1 v2,
          M.get x ρ1 = Some v1 /\
            M.get x ρ2 = Some v2 /\
            V_top i v1 v2.

  Lemma G_top_wf_env_l i Γ1 ρ1 ρ2 :
    G_top i Γ1 ρ1 ρ2 ->
    wf_env Γ1 ρ1.
  Proof. unfold G_top. intros; tauto. Qed.

  Lemma G_top_wf_cenv_r i Γ1 ρ1 ρ2 :
    G_top i Γ1 ρ1 ρ2 ->
    wf_cenv θ ρ2.
  Proof. unfold G_top. intros; tauto. Qed.

  Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 :
    G_top i Γ1 ρ1 ρ2 ->
    Γ2 \subset Γ1 ->
    G_top i Γ2 ρ1 ρ2.
  Proof. unfold G_top. fcrush. Qed.

  (* Top-level Monotonicity Lemmas *)
  Lemma V_top_mono i :
    forall {j v1 v2},
      V_top i v1 v2 ->
      j <= i ->
      V_top j v1 v2.
  Proof.
    intros.
    eapply V_V_top; eauto.
    fcrush.
    eapply V_mono; eauto.
    eapply V_V_top; eauto.
    fcrush.
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
    destruct (H j1 r1) as [j2 [r2 [I2 [Hr2 HR]]]]; auto; try lia.
    exists j2, r2, I2; split; eauto.
    apply R_top_mono with (i - j1); try lia; auto.
  Qed.

  Lemma G_top_mono {Γ1 ρ1 ρ2} i j:
    G_top i Γ1 ρ1 ρ2 ->
    j <= i ->
    G_top j Γ1 ρ1 ρ2.
  Proof.
    unfold G_top.
    intros.
    destruct H as [Hwf1 [Hwf2 HG]].
    repeat (split; eauto); intros.
    edestruct HG as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto.
    eexists; eexists; repeat (split; eauto).
    apply V_top_mono with i; eauto.
    fcrush.
  Qed.

End LRTop.

  Definition trans_correct_top e ce :=
    (occurs_free_top ce) \subset (occurs_free e) /\
      forall cce c1 c2 θ,
        coloring c1 ce c2 cce ->
        analysis_context_of θ cce ->
        forall i ρ1 ρ2,
          G_top θ i (occurs_free e) ρ1 ρ2 ->
          E_top θ i ρ1 e ρ2 cce.

  Theorem top A e Rs :
    acheck A e Rs ->
    escapes_ok A ->
    Rs \subset (ai_esc A) ->
    trans_correct_top e (CEunit A Rs e).
  Proof.
    unfold trans_correct_top.
    intros Hack Hesc Hsub; intros.
    split; intros.
    apply occurs_free_top_cexp; eauto.
    inv H.

    assert (Hwa : well_annotated θ A c1 (occurs_free e) e).
    {
      eapply fundamental_property; eauto.
      unfold analysis_context_escape_ok.
      admit.
      unfold analysis_context_of in H0; fcrush.
      eapply well_scoped_intro; eauto.
      fcrush.
    }

    eapply E_E_top; eauto.
    unfold well_annotated in Hwa.
    eapply Hwa; eauto.

  Admitted.

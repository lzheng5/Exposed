From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From SemAnnotate Require Import LabeledANF SimpleCFA.

(* Some Indepedent Properties for the Simple Value Set Analysis *)

Section Closure.
  (* Closure Properties *)
  (* Internal labels don't interact with `l_top_intro1` nor `l_top_elim`. *)
  (* We show this property for the abstract semantics and the colored collecting semantics. *)

  (* --------------------------------------------------------------- *)
  (* Uncolored Closure                                               *)
  (* --------------------------------------------------------------- *)

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
      ((l, l') \in I) ->
      areachable I l l'

  | AReachable_interact_r :
    forall l',
      ((l', l) \in I) ->
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
  (* Colored Closure                                                 *)
  (* --------------------------------------------------------------- *)

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
      induction Hr as [x | x y Hin | x y Hin | x y z H1 IH1 H2];
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

  (* --------------------------------------------------------------- *)
  (* The Analysis and the Checking Semantics Respect the Closure      *)
  (* --------------------------------------------------------------- *)

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

  Lemma cbstep_fuel_closed A c bdr ρ e i Rs r I :
    cbstep_fuel A c bdr ρ e i Rs r I ->
    internals_closed (ainternals_of (ai_int A)) c I.
  Proof.
    intros.
    inv H.
    - eapply internals_closed_empty; eauto.
    - eapply approx_int_closed; eauto.
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

End Closure.

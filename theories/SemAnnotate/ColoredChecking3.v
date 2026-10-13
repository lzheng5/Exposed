From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From SemAnnotate Require Import LabeledANF.
From LambdaWeb Require Import Base.

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

(* REVISIT: unused *)
Definition all_clabels (I : interactions) : clabels :=
  fun cl => exists cl', (cl, cl') \in I \/ (cl', cl) \in I.

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

(* Internal Label Set *)
Definition internals : Type := labels.

(* Internal with respect to `U` paired with its corresponding color `c` *)
Definition cinternal (U : internals) (c : color) (cl : clabel) : Prop :=
  fst cl = c /\ (snd cl \in U).

(* `U` only contains internal labels in `I`. *)
Definition internals_sound (U : internals) (I : interactions) (cl : clabel) : Prop :=
  (snd cl \in U) -> internal I cl.

(* Closure Property *)
(* `U` paired with `c` is closed under reachable interactions `I`.
    Note that `U` is not necessarily the most precise internal events in `I`. *)
Definition internals_closed (U : internals) (c : color) (I : interactions) : Prop :=
  forall l cl',
    (l \in U) ->
    (cl' \in (reachable I (c, l))) ->
    cinternal U c cl'.

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

(* Edge-wise characterization of closure *)
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

Lemma interactions_respect_sound {U c I} :
  interactions_respect U c I ->
  forall cl,
    fst cl = c ->
    internals_sound U I cl.
Proof.
  intros Hres cl Hc Hmem.
  exact (interactions_respect_internal Hres cl (conj Hc Hmem)).
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
| CTAG : internals -> clabel -> A -> ctag A.

Hint Constructors ctag : core.

(* Value *)
Inductive cval : Type :=
| CVfun : var -> M.t (ctag cval) -> list var -> exp -> cval
| CVconstr : ctor_tag -> list (ctag cval) -> cval.

Hint Constructors cval : core.

Definition clval := ctag cval.

Definition CTag U c l cv := CTAG cval U (c, l) cv.

(* Environment *)
Definition cenv := M.t clval.

(* Result *)
Inductive cres : Type :=
| COOT
| CRes : clval -> cres.

Hint Constructors cres : core.

(* The Key Invariant *)
Definition interaction_sound (U_i : internals) (cl_i : clabel)
                             (U_e : internals) (cl_e : clabel) : Prop :=
  match cl_i, cl_e with
  | (c_i, l_i), (c_e, l_e) =>
      (* Same color: the interaction stays within one compilation unit, so
         both endpoints are governed by one and the same internal set. *)
      (c_i = c_e ->
         (U_i <--> U_e) /\ ((l_i \in U_i) <-> (l_e \in U_e)))
      /\
      (* Different colors: a foreign interaction, so neither endpoint may be
         claimed as internal by either unit. *)
      (c_i <> c_e ->
         ~ (l_i \in U_i) /\ ~ (l_i \in U_e) /\
         ~ (l_e \in U_i) /\ ~ (l_e \in U_e))
  end.

(* Colors are decidable, so the two implications above can always be turned
   into the corresponding case split. *)
Lemma interaction_sound_inv U_i c_i l_i U_e c_e l_e :
  interaction_sound U_i (c_i, l_i) U_e (c_e, l_e) ->
  (c_i = c_e /\ (U_i <--> U_e) /\ ((l_i \in U_i) <-> (l_e \in U_e)))
  \/
  (c_i <> c_e /\
     ~ (l_i \in U_i) /\ ~ (l_i \in U_e) /\
     ~ (l_e \in U_i) /\ ~ (l_e \in U_e)).
Proof.
  intros [Hsame Hdiff].
  destruct (Nat.eq_dec c_i c_e) as [Heq | Hneq].
  - left.
    destruct (Hsame Heq) as [Hset Hiff].
    split; [exact Heq | split; [exact Hset | exact Hiff]].
  - right.
    destruct (Hdiff Hneq) as [Hl_i_U_i [Hl_i_U_e [Hl_e_U_i Hl_e_U_e]]].
    split; [exact Hneq
           | split; [exact Hl_i_U_i
           | split; [exact Hl_i_U_e
           | split; [exact Hl_e_U_i | exact Hl_e_U_e]]]].
Qed.

(* If the introduction site is internal, the interaction is internal: the
   colors agree, the two units share an internal set, and the elimination
   site is internal as well. *)
Lemma interaction_sound_intro U_i c_i l_i U_e c_e l_e :
  interaction_sound U_i (c_i, l_i) U_e (c_e, l_e) ->
  (l_i \in U_i) ->
  c_i = c_e /\ (U_i <--> U_e) /\ (l_e \in U_e).
Proof.
  intros Hsnd Hin.
  destruct (interaction_sound_inv _ _ _ _ _ _ Hsnd)
    as [[Heq [Hset Hiff]] | [_ [Hl_i_U_i _]]].
  - split; [exact Heq | split; [exact Hset | apply (proj1 Hiff); exact Hin]].
  - contradiction.
Qed.

(* Symmetrically for the elimination site. *)
Lemma interaction_sound_elim U_i c_i l_i U_e c_e l_e :
  interaction_sound U_i (c_i, l_i) U_e (c_e, l_e) ->
  (l_e \in U_e) ->
  c_i = c_e /\ (U_i <--> U_e) /\ (l_i \in U_i).
Proof.
  intros Hsnd Hin.
  destruct (interaction_sound_inv _ _ _ _ _ _ Hsnd)
    as [[Heq [Hset Hiff]] | [_ [_ [_ [_ Hl_e_U_e]]]]].
  - split; [exact Heq | split; [exact Hset | apply (proj2 Hiff); exact Hin]].
  - contradiction.
Qed.

(* Checking Semantics based on the Collecting Semantics *)
(* This semantics specifies the validity of the internal program components, U, based on the collected interactions, I. *)
Inductive cbstep (U : internals) (c : color) (ρ : cenv) : exp -> fuel -> cres -> interactions -> Prop :=
| Cbstep_ret :
  forall {x v},
    M.get x ρ = Some v ->
    (* Note a foreign value can be returned as long as it is not eliminated in a foreign context. *)
    cbstep U c ρ (Eret x) 0 (CRes v) (Empty_set _)

| Cbstep_fun :
  forall {I f l xs e k i r},
    cbstep_fuel U c (M.set f (CTag U c l (CVfun f ρ xs e)) ρ) k i r I ->
    cbstep U c ρ (Efun f l xs e k) i r I

| Cbstep_app :
  forall {I' U' f f' c' l l' xs ρ' xs' e vs ρ'' i r},
    M.get f ρ = Some (CTag U' c' l' (CVfun f' ρ' xs' e)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (CTag U' c' l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    cbstep_fuel U' c' ρ'' e i r I' ->
    interaction_sound U' (c', l') U (c, l) ->
    cbstep U c ρ (Eapp f l xs) i r (((c', l'), (c, l)) |: I')

with cbstep_fuel (U : internals) (c : color) (ρ : cenv) : exp -> fuel -> cres -> interactions -> Prop :=
| CbstepF_OOT :
  forall {e},
    cbstep_fuel U c ρ e 0 COOT (Empty_set _)

| CbstepF_Step :
  forall {I e i r},
    cbstep U c ρ e i r I ->
    cbstep_fuel U c ρ e (S i) r I.

Hint Constructors cbstep : core.
Hint Constructors cbstep_fuel : core.

Scheme cbstep_ind' := Minimality for cbstep Sort Prop
with cbstep_fuel_ind' := Minimality for cbstep_fuel Sort Prop.

Lemma cbstep_deterministic_aux v v' {U I I' c ρ e i i' r r'}:
  cbstep U c ρ e i r I ->
  cbstep U c ρ e i' r' I' ->
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
  induction H using cbstep_ind' with (P := fun U c ρ e i r I =>
                                             forall I' v i' r' v',
                                               cbstep U c ρ e i' r' I' ->
                                               r = CRes v -> r' = CRes v' ->
                                               v = v' /\ i = i' /\ I <--> I')
                                     (P0 := fun U c ρ e i r I =>
                                              forall I' v i' r' v',
                                                cbstep_fuel U c ρ e i' r' I' ->
                                                r = CRes v -> r' = CRes v' ->
                                                v = v' /\ i = i' /\ I <--> I');
    intros; subst.
  - inv H0; inv H1; invc; fcrush.
  - inv H0.
    edestruct IHcbstep; eauto; subst.
  - inv H4; invc.
    edestruct IHcbstep as [Heqv [Heqi HeqI]]; eauto; subst.
    hauto l: on use: Extensionality_Ensembles unfold: Same_set, Included, interactions.
  (* - inv H6; invc.
    edestruct IHcbstep as [Heqv [Heqi HeqI]]; eauto; subst.
    edestruct IHcbstep0 as [Heqv' [Heqi' HeqI']]; eauto; subst.
    hauto l: on use: Extensionality_Ensembles unfold: Same_set, Included, interactions.
  - fcrush.
  - inv H1; invc.
    edestruct IHcbstep as [Heqv [Heqi HeqI]]; eauto.
  - inv H4; invc.
    edestruct IHcbstep as [Heqv [Heqi HeqI]]; eauto; subst.
    hauto lq: on use: Extensionality_Ensembles unfold: Same_set, Included, interactions.
  - inv H4; invc.
    destruct (find_tag_deterministic H0 H9); subst.
    edestruct IHcbstep as [Heqv [Heqi HeqI]]; eauto; subst.
    hauto lq: on use: Extensionality_Ensembles unfold: Same_set, Included, interactions.
*)

  - fcrush.
  - match goal with
    | [Hs : cbstep_fuel _ _ _ _ _ _ _ |- _] => inv Hs
    end;
      edestruct IHcbstep as [Heqv [Heqi HeqI]]; eauto.
Qed.

Lemma cbstep_fuel_deterministic_aux v v' {U I I' c ρ e i i' r r'}:
  cbstep_fuel U c ρ e i r I ->
  cbstep_fuel U c ρ e i' r' I' ->
  r = CRes v ->
  r' = CRes v' ->
  (v = v' /\ i = i' /\ I <--> I').
Proof.
  intros Hstep Hstep' Heqr Heqr'; subst.
  inv Hstep; inv Hstep'.
  match goal with
  | [Hs : cbstep _ _ _ _ _ (CRes v) _, Hs' : cbstep _ _ _ _ _ (CRes v') _ |- _] =>
      edestruct (cbstep_deterministic_aux v v' Hs Hs') as [Heqv [Heqi HeqI]];
        subst; eauto
  end.
Qed.

Theorem cbstep_deterministic v v' {U I I' c ρ e i i'}:
  cbstep U c ρ e i (CRes v) I ->
  cbstep U c ρ e i' (CRes v') I' ->
  (v = v' /\ i = i' /\ I <--> I').
Proof. srun eauto using cbstep_deterministic_aux. Qed.

Theorem cbstep_fuel_deterministic v v' {U I I' c ρ e i i'}:
  cbstep_fuel U c ρ e i (CRes v) I ->
  cbstep_fuel U c ρ e i' (CRes v') I' ->
  (v = v' /\ i = i' /\ I <--> I').
Proof. srun eauto using cbstep_fuel_deterministic_aux. Qed.

(* Internals Context *)
(* Assigns to each color the internal set of the compilation unit wearing it.
   This is the *global* counterpart of the "unique colored context" condition
   built into `interaction_sound`: there, two interacting labels of the same
   color are forced to agree on their internal set, but only where they
   actually interact.  `internals_context` forces every occurrence of a color to agree. *)
Definition internals_context := color -> internals.

(* Well-formed Value and Environment w.r.t. an Internals Context *)
(* Every tag occurring in a value, or in an environment, assigns to its color
   the internal set that `Θ` prescribes for it. *)
Inductive wf_cval (Θ : internals_context) : clval -> Prop :=
| WF_TAG :
  forall U c l v,
    U <--> Θ c ->
    wf_cval' Θ v ->
    wf_cval Θ (CTag U c l v)

with wf_cval' (Θ : internals_context) : cval -> Prop :=
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

with wf_cenv (Θ : internals_context) : cenv -> Prop :=
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
Inductive wf_cres (Θ : internals_context) : cres -> Prop :=
| WF_COOT :
  wf_cres Θ COOT

| WF_CRes :
  forall v,
    wf_cval Θ v ->
    wf_cres Θ (CRes v).

Hint Constructors wf_cres : core.

(* Inversion *)
Lemma wf_cval_CTag_inv {Θ U c l v} :
  wf_cval Θ (CTag U c l v) ->
  (U <--> Θ c) /\ wf_cval' Θ v.
Proof. intros Hwf; inv Hwf; split; assumption. Qed.

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

(* Interaction Closure Property *)
(* Each interaction recorded by the checking semantics respects *every* unit's
   internal set.  The local `interaction_sound` side condition at each call
   site suffices, once the color context is globally consistent. *)
Lemma cbstep_respect Θ :
  forall U c ρ e i r I,
    cbstep U c ρ e i r I ->
    U <--> Θ c ->
    wf_cenv Θ ρ ->
    forall c0, interactions_respect (Θ c0) c0 I.
Proof.
  intros U c ρ e i r I Hstep.
  induction Hstep as
    [ U c ρ x v Hget
    | U c ρ I f l xs e k i r Hfuel IHfuel
    | U c ρ I' U' f f' c' l l' xs ρ' xs' e vs ρ'' i r
        Hget Hgetl Hsetl Hfuel IHfuel Hsnd
    | U c ρ e
    | U c ρ I e i r Hsub IHstep ]
    using cbstep_ind'
    with (P := fun U c ρ e i r I =>
                 U <--> Θ c ->
                 wf_cenv Θ ρ ->
                 forall c0, interactions_respect (Θ c0) c0 I)
         (P0 := fun U c ρ e i r I =>
                  U <--> Θ c ->
                  wf_cenv Θ ρ ->
                  forall c0, interactions_respect (Θ c0) c0 I).

  - (* Cbstep_ret: nothing is recorded *)
    intros HU Hρ c0.
    apply interactions_respect_empty.

  - (* Cbstep_fun: the new binding agrees with Θ, so the IH applies *)
    intros HU Hρ c0.
    pose proof (wf_cenv_set f (CTag U c l (CVfun f ρ xs e)) Hρ
                  (WF_TAG Θ U c l (CVfun f ρ xs e) HU
                     (WF_CVfun Θ f ρ xs e Hρ))) as Hρf.
    eauto.

  - (* Cbstep_app *)
    intros HU Hρ c0.
    (* the callee's tag agrees with Θ, and so does its environment *)
    pose proof (wf_cenv_get Hρ f _ Hget) as Hclo.
    destruct (wf_cval_CTag_inv Hclo) as [HU' Hfun].
    pose proof (wf_cval_CVfun_inv Hfun) as Hρ'.
    pose proof (wf_cenv_get_list Hρ xs vs Hgetl) as Hvs.
    pose proof (wf_cenv_set f' (CTag U' c' l' (CVfun f' ρ' xs' e)) Hρ' Hclo)
      as Hρ'f.
    pose proof (wf_cenv_set_lists _ Hρ'f vs xs' ρ'' Hvs Hsetl) as Hρ''.
    pose proof (IHfuel HU' Hρ'') as HI'.
    apply interactions_respect_add; [| exact (HI' c0)].
    destruct (interaction_sound_inv _ _ _ _ _ _ Hsnd)
      as [[Heqc [Hsets Hiff]] | [Hneqc [Hn_i_i [Hn_i_e [Hn_e_i Hn_e_e]]]]].
    + (* internal interaction: the colors agree, so both endpoints are
         internal to the same unit, or neither is *)
      subst c'.
      split; intros [Hc0 Hmem]; simpl in Hc0, Hmem; subst c0.
      * split; [reflexivity | simpl].
        apply (proj1 HU); apply (proj1 Hiff); apply (proj2 HU'); exact Hmem.
      * split; [reflexivity | simpl].
        apply (proj1 HU'); apply (proj2 Hiff); apply (proj2 HU); exact Hmem.
    + (* foreign interaction: neither endpoint is internal to any unit, so the
         colors recorded in `cinternal` make both sides of the iff false *)
      split; intros [Hc0 Hmem]; simpl in Hc0, Hmem; subst c0; exfalso.
      * apply Hn_i_i; apply (proj2 HU'); exact Hmem.
      * apply Hn_e_e; apply (proj2 HU); exact Hmem.

  - (* CbstepF_OOT: nothing is recorded *)
    intros HU Hρ c0.
    apply interactions_respect_empty.

  - (* CbstepF_Step *)
    intros HU Hρ c0.
    eauto.
Qed.

Lemma cbstep_fuel_respect Θ :
  forall U c ρ e i r I,
    cbstep_fuel U c ρ e i r I ->
    U <--> Θ c ->
    wf_cenv Θ ρ ->
    forall c0, interactions_respect (Θ c0) c0 I.
Proof.
  intros U c ρ e i r I Hstep HU Hρ c0.
  inv Hstep.
  - apply interactions_respect_empty.
  - match goal with
    | [Hs : cbstep _ _ _ _ _ _ _ |- _] =>
        exact (cbstep_respect Θ _ _ _ _ _ _ _ Hs HU Hρ c0)
    end.
Qed.

Lemma cbstep_closed Θ U c ρ e i r I :
  U <--> Θ c ->
  wf_cenv Θ ρ ->
  cbstep U c ρ e i r I ->
  internals_closed U c I.
Proof.
  intros HU Hρ Hstep.
  apply interactions_respect_closed.
  apply (interactions_respect_Same_set U (Θ c) c I HU).
  exact (cbstep_respect Θ U c ρ e i r I Hstep HU Hρ c).
Qed.

Lemma cbstep_fuel_closed Θ U c ρ e i r I :
  U <--> Θ c ->
  wf_cenv Θ ρ ->
  cbstep_fuel U c ρ e i r I ->
  internals_closed U c I.
Proof.
  intros HU Hρ Hstep.
  apply interactions_respect_closed.
  apply (interactions_respect_Same_set U (Θ c) c I HU).
  exact (cbstep_fuel_respect Θ U c ρ e i r I Hstep HU Hρ c).
Qed.

(* A returned value agrees with Θ as well. *)
Lemma cbstep_wf_cres Θ :
  forall U c ρ e i r I,
    cbstep U c ρ e i r I ->
    U <--> Θ c ->
    wf_cenv Θ ρ ->
    wf_cres Θ r.
Proof.
  intros U c ρ e i r I Hstep.
  induction Hstep as
    [ U c ρ x v Hget
    | U c ρ I f l xs e k i r Hfuel IHfuel
    | U c ρ I' U' f f' c' l l' xs ρ' xs' e vs ρ'' i r
        Hget Hgetl Hsetl Hfuel IHfuel Hsnd
    | U c ρ e
    | U c ρ I e i r Hsub IHstep ]
    using cbstep_ind'
    with (P := fun U c ρ e i r I =>
                 U <--> Θ c -> wf_cenv Θ ρ -> wf_cres Θ r)
         (P0 := fun U c ρ e i r I =>
                  U <--> Θ c -> wf_cenv Θ ρ -> wf_cres Θ r).

  - (* Cbstep_ret: the value comes straight out of the environment *)
    intros HU Hρ.
    apply WF_CRes.
    eapply wf_cenv_get; eauto.

  - (* Cbstep_fun: the new binding agrees with Θ, so the IH applies *)
    intros HU Hρ.
    pose proof (wf_cenv_set f (CTag U c l (CVfun f ρ xs e)) Hρ
                  (WF_TAG Θ U c l (CVfun f ρ xs e) HU
                     (WF_CVfun Θ f ρ xs e Hρ))) as Hρf.
    eauto.

  - (* Cbstep_app: the callee runs at its own color, with its own internals *)
    intros HU Hρ.
    pose proof (wf_cenv_get Hρ f _ Hget) as Hclo.
    destruct (wf_cval_CTag_inv Hclo) as [HU' Hfun].
    pose proof (wf_cval_CVfun_inv Hfun) as Hρ'.
    pose proof (wf_cenv_get_list Hρ xs vs Hgetl) as Hvs.
    pose proof (wf_cenv_set f' (CTag U' c' l' (CVfun f' ρ' xs' e)) Hρ' Hclo)
      as Hρ'f.
    pose proof (wf_cenv_set_lists _ Hρ'f vs xs' ρ'' Hvs Hsetl) as Hρ''.
    eauto.

  - (* CbstepF_OOT: no value is returned *)
    intros HU Hρ.
    apply WF_COOT.

  - (* CbstepF_Step *)
    intros HU Hρ.
    eauto.
Qed.

Lemma cbstep_fuel_wf_cres Θ U c ρ e i r I :
  U <--> Θ c ->
  wf_cenv Θ ρ ->
  cbstep_fuel U c ρ e i r I ->
  wf_cres Θ r.
Proof.
  intros HU Hρ Hstep.
  inv Hstep.
  - apply WF_COOT.
  - match goal with
    | [Hs : cbstep _ _ _ _ _ _ _ |- _] =>
        exact (cbstep_wf_cres Θ U c ρ e _ _ _ Hs HU Hρ)
    end.
Qed.

(* Cross-semantics Logical Relations *)
Section LR.

  Variable θ : internals_context.

  Definition R' (P : nat -> wval -> clval -> Prop) (i : nat) (r1 : res) (r2 : cres) :=
    match r1, r2 with
    | OOT, COOT => True
    | Res v1, CRes v2 => P i v1 v2
    | _, _ => False
    end.

  Definition E' (P : nat -> wval -> clval -> Prop) (U : internals) (c : color) (i : nat) (ρ1 : env) (ρ2 : cenv) (e : exp) : Prop :=
    forall j1 r1,
      j1 <= i ->
      bstep_fuel ρ1 e j1 r1 ->
      exists j2 r2 I2,
        cbstep_fuel U c ρ2 e j2 r2 I2 /\
          R' P (i - j1) r1 r2.


  Fixpoint V (i : nat) (wv : wval) (cv : clval) {struct i} : Prop :=
    wf_val wv /\
      wf_cval θ cv /\
      match wv, cv with
      | TAG _ l1 v1, CTAG _ U2 (c2, l2) v2 =>
          l1 = l2 /\
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
                      forall j U c l vs1 vs2 ρ3 ρ4,
                        j <= i0 ->
                        Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                        set_lists xs1 vs1 (M.set f1 (Tag l1 (Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                        set_lists xs2 vs2 (M.set f2 (CTag U2 c2 l2 (CVfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                        interaction_sound U2 (c2, l2) U (c, l) ->
                        E' V U2 c2 (i0 - (i0 - j)) ρ3 ρ4 e1
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
    - repeat (split; auto).
      destruct v; destruct c0; try contradiction.
      + fcrush.
      + fcrush.
    - repeat (split; auto).
      destruct v; destruct c0; try contradiction.
      + destruct HV as [Heqv [Heql [Heqe HV]]]; subst.
        repeat (split; eauto); intros.
        rename i0 into U0.
        specialize (HV j0 U c0 l vs1 vs2 ρ3 ρ4).
        rewrite normalize_step in *; try lia.
        eapply HV; eauto; try lia.
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

  Lemma E_mono {U c ρ1 ρ2 e} i j:
    E U c i ρ1 ρ2 e ->
    j <= i ->
    E U c j ρ1 ρ2 e.
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

  Definition well_annotated U c Γ e :=
    U <--> θ c /\
    forall i ρ1 ρ2,
      G i Γ ρ1 ρ2 ->
      E U c i ρ1 ρ2 e.

  Lemma ret_compat U c Γ x :
    U <--> θ c ->
    (x \in Γ) ->
    well_annotated U c Γ (Eret x).
  Proof.
    unfold well_annotated, E, E', R, R', Ensembles.Included, Ensembles.In.
    intros; simpl.
    split; auto; intros.

    inv H3.
    - fcrush.
    - destruct r1.
      fcrush.
      inv H4.
      edestruct (G_get H1) as [v2 [Heqv2 HV]]; eauto.
      exists 1, (CRes v2), (Empty_set _); split; eauto; simpl.
      eapply V_mono; eauto; lia.
  Qed.

  Lemma Vfun_V Γ f l U c xs e  :
    occurs_free e \subset FromList xs :|: (f |: Γ) ->
    well_annotated U c (FromList xs :|: (f |: Γ)) e ->
    forall {i ρ1 ρ2},
      wf_val (Tag l (Vfun f ρ1 xs e)) ->
      wf_cval θ (CTag U c l (CVfun f ρ2 xs e)) ->
      G i Γ ρ1 ρ2 ->
      V i (Tag l (Vfun f ρ1 xs e)) (CTag U c l (CVfun f ρ2 xs e)).
  Proof.
    unfold well_annotated.
    intros HS [HU He] i.
    induction i; simpl; intros; auto;
      repeat (split; auto);
      intros; (repeat split; auto).
    eapply (He (i - (i - j)) ρ3 ρ4); eauto.

    eapply G_subset; eauto.
    eapply G_set_lists; eauto.
    eapply G_set; eauto.
    + apply G_mono with (S i); eauto; lia.
    + apply V_mono with i; try lia.
      eapply IHi; eauto.
      apply G_mono with (S i); eauto; lia.
    + eapply Included_refl; eauto.
  Qed.

  Lemma fun_compat U c Γ e k f l xs :
    occurs_free e \subset FromList xs :|: (f |: Γ) ->
    well_annotated U c (FromList xs :|: (f |: Γ)) e ->
    well_annotated U c (f |: Γ) k ->
    well_annotated U c Γ (Efun f l xs e k).
  Proof.
    unfold well_annotated, E, E'.
    intros HS He [HU Hk].
    split; auto; intros.

    inv H1.
    - fcrush.
    - destruct r1.
      fcrush.
      assert (Hwfρ1 : wf_env Γ ρ1) by eauto using G_wf_env_l.
      assert (Hwfρ2 : wf_cenv θ ρ2) by eauto using G_wf_cenv_r.
      inv H2.
      edestruct (Hk (i - 1) (M.set f (Tag l (Vfun f ρ1 xs e)) ρ1) (M.set f (CTag U c l (CVfun f ρ2 xs e)) ρ2)) with (j1 := c0) (r1 := (Res w)) as [j2 [r2 [I2 [Hk2 Rr]]]]; eauto; try lia.
      + eapply G_subset.
        eapply G_set; eauto.
        eapply G_mono with i; eauto; lia.
        * eapply Vfun_V; eauto.
          apply G_mono with i; eauto; lia.
        * apply Included_refl.
      + edestruct R_res_inv_l as [w2 [Heqw2 HV]]; eauto; subst.
        exists (S j2), (CRes w2), I2; split; eauto.
        eapply R_mono; eauto; lia.
  Qed.

  Lemma app_compat U Γ xs f l c :
    U <--> θ c ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    well_annotated U c Γ (Eapp f l xs).
  Proof.
    unfold well_annotated, E, E'.
    intross HU Hf Hxs; simpl.
    split; auto; intros.

    inv H1.
    - fcrush.
    - destruct r1.
      fcrush.
      inv H2.
      edestruct (G_get H f) as [fv2 [Heqfv2 HV]]; eauto.
      destruct i.
      inv H0.
      rename w into v.
      destruct fv2; destruct c1; destruct c2; simpl in HV; invc;
        rename i0 into U0.
      2 : { fcrush. }
      destruct HV as [Hwf1 [Hwf2 [Heql [Heqf [Heqxs [Heqe HV]]]]]]; subst; invc.

      edestruct (G_get_list H xs vs) as [vs2 [Heqvs2 Vvs]]; eauto; invc.

      destruct (set_lists_length3 (M.set v0 (CTag U0 c1 l0 (CVfun v0 t l1 e0)) t) l1 vs2) as [ρ4 Heqρ4].
      unfold clval in *.
      rewrite (set_lists_length_eq _ _ _ _ H9); auto.
      eapply Forall2_length; eauto.

      assert (HI : interaction_sound U0 (c1, l0) U (c, l)).
      {
        unfold interaction_sound.
        split; intros; subst.
        - (* internal context *)
          inv Hwf2.
          assert (U0 <--> U) by sfirstorder.
          split; auto.
          admit. (* stuck *)
        - (* foreign context *)
          (* stuck here *)
          admit.
      }

      assert (HE : E U0 c1 (i - (i - i)) ρ'' ρ4 e0).
      {
        eapply (HV i U c l vs vs2); eauto.
        apply V_mono_Forall with (S i); auto; lia.
      }

      apply (E_mono _ i) in HE; try lia.
      unfold E, E' in HE.
      destruct (HE c0 (Res v)) as [j2 [r2 [I2 [He0 Rr]]]]; try lia; auto.
      exists (S j2), r2, (((c1, l0), (c, l)) |: I2); split; eauto.
  Abort.


  Lemma fundamental_property {U c Γ e}:
    U <--> θ c ->
    well_scoped Γ e ->
    well_annotated U c Γ e.
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

End LR.

(* Top Level *)
(* The top-level consists of two phases: coloring and running. *)

(* Top-level Compilation Unit & Linking *)
(* This is what an analysis should annotate the compilation unit with *)
Inductive cexp : Type :=
| CEunit : internals -> exp -> cexp
| CElink : var -> cexp -> cexp -> cexp.

Hint Constructors cexp : core.

(* Linking *)
Definition clink x e1 e2 : cexp := CElink x e1 e2.

Inductive occurs_free_top : cexp -> vars :=
| Free_cexp :
  forall e U x,
    occurs_free e x ->
    occurs_free_top (CEunit U e) x

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

Lemma occurs_free_top_cexp U e :
  (occurs_free_top (CEunit U e)) <--> (occurs_free e).
Proof. split; unfold Ensembles.Included, Ensembles.In; fcrush. Qed.

(* Phase 1: Coloring *)
(* Colored Linking Tree *)
(* The result of the preprocessing step.  A `cexp` is colorless: a unit only
   declares the internal labels it claims.  Colors are artificial names handed
   out once, at link time, so that the *dynamic* semantics can tell two units
   apart; nothing in a unit's own source mentions them. *)
Inductive ccexp : Type :=
| CCunit : internals -> color -> exp -> ccexp
| CClink : var -> ccexp -> ccexp -> ccexp.

Hint Constructors ccexp : core.

(* `coloring c1 ce c2 cce` hands the colors `c1, c1+1, ..., c2-1` to the units
   of `ce`, left to right.  The counter is the whole point: it makes the
   assignment *injective*, which is exactly what `interaction_sound` leans on
   when it concludes, from two labels sharing a color, that they are governed
   by one and the same internal set. *)
Inductive coloring : color -> cexp -> color -> ccexp -> Prop :=
| Coloring_unit :
  forall c U e,
    coloring c (CEunit U e) (S c) (CCunit U c e)

| Coloring_link :
  forall c1 c2 c3 x e1 e2 cce1 cce2,
    coloring c1 e1 c2 cce1 ->
    coloring c2 e2 c3 cce2 ->
    coloring c1 (CElink x e1 e2) c3 (CClink x cce1 cce2).

Hint Constructors coloring : core.

(* `(c, U)` is one of the units of `cce`. *)
Inductive has_unit : ccexp -> color -> internals -> Prop :=
| Has_unit_unit :
  forall U c e,
    has_unit (CCunit U c e) c U

| Has_unit_link1 :
  forall x cce1 cce2 c U,
    has_unit cce1 c U ->
    has_unit (CClink x cce1 cce2) c U

| Has_unit_link2 :
  forall x cce1 cce2 c U,
    has_unit cce2 c U ->
    has_unit (CClink x cce1 cce2) c U.

Hint Constructors has_unit : core.

Lemma coloring_mono {c1 ce c2 cce} :
  coloring c1 ce c2 cce ->
  c1 <= c2.
Proof. intros Hcol; induction Hcol; lia. Qed.

Lemma coloring_range {c1 ce c2 cce} :
  coloring c1 ce c2 cce ->
  forall c U, has_unit cce c U -> c1 <= c < c2.
Proof.
  intros Hcol.
  induction Hcol as [c U e | c1 c2 c3 x e1 e2 cce1 cce2 Hc1 IH1 Hc2 IH2];
    intros c0 U0 Hunit.
  - inv Hunit; lia.
  - inv Hunit.
    + match goal with
      | [Hu : has_unit cce1 c0 U0 |- _] => destruct (IH1 c0 U0 Hu) as [Hlo Hhi]
      end.
      pose proof (coloring_mono Hc2) as Hm; lia.
    + match goal with
      | [Hu : has_unit cce2 c0 U0 |- _] => destruct (IH2 c0 U0 Hu) as [Hlo Hhi]
      end.
      pose proof (coloring_mono Hc1) as Hm; lia.
Qed.

(* Distinct units get distinct colors, so a color names at most one unit. *)
Lemma coloring_unique {c1 ce c2 cce} :
  coloring c1 ce c2 cce ->
  forall c U U',
    has_unit cce c U ->
    has_unit cce c U' ->
    U = U'.
Proof.
  intros Hcol.
  induction Hcol as [c U e | c1 c2 c3 x e1 e2 cce1 cce2 Hc1 IH1 Hc2 IH2];
    intros c0 U0 U0' Hu Hu'.
  - inv Hu; inv Hu'; reflexivity.
  - inv Hu; inv Hu'.
    + match goal with
      | [Ha : has_unit cce1 c0 U0, Hb : has_unit cce1 c0 U0' |- _] =>
          exact (IH1 c0 U0 U0' Ha Hb)
      end.
    + exfalso.
      match goal with
      | [Ha : has_unit cce1 c0 U0, Hb : has_unit cce2 c0 U0' |- _] =>
          destruct (coloring_range Hc1 c0 U0 Ha) as [Hlo Hhi];
          destruct (coloring_range Hc2 c0 U0' Hb) as [Hlo' Hhi']
      end; lia.
    + exfalso.
      match goal with
      | [Ha : has_unit cce2 c0 U0, Hb : has_unit cce1 c0 U0' |- _] =>
          destruct (coloring_range Hc2 c0 U0 Ha) as [Hlo Hhi];
          destruct (coloring_range Hc1 c0 U0' Hb) as [Hlo' Hhi']
      end; lia.
    + match goal with
      | [Ha : has_unit cce2 c0 U0, Hb : has_unit cce2 c0 U0' |- _] =>
          exact (IH2 c0 U0 U0' Ha Hb)
      end.
Qed.

(* The internals context is *read off* the colored tree rather than supplied:
   `Θ c` is the internal set of the unit that was handed the color `c`. *)
Definition ictx_of (cce : ccexp) : internals_context :=
  fun c => fun l => exists U, has_unit cce c U /\ (l \in U).

(* `Θ` agrees with the coloring of `cce`. *)
Definition internals_context_of (Θ : internals_context) (cce : ccexp) : Prop :=
  forall c U, has_unit cce c U -> U <--> Θ c.

Lemma ictx_of_correct {c1 ce c2 cce} :
  coloring c1 ce c2 cce ->
  internals_context_of (ictx_of cce) cce.
Proof.
  intros Hcol c U Hunit.
  unfold ictx_of, Ensembles.In.
  split; intros l Hl.
  - exists U; split; [exact Hunit | exact Hl].
  - destruct Hl as [U' [Hunit' Hl']].
    rewrite <- (coloring_unique Hcol c U' U Hunit' Hunit); exact Hl'.
Qed.

(* Top-level Checking Semantics for the *Colored* Top-level Expression *)
(* The colors are already in the tree, so the top-level semantics does not
   mention `Θ` at all: it just runs each unit at the color preprocessing gave
   it, and unions the interactions the units record.
   `Θ` reappears only in the theorems, through `internals_context_of`. *)
Inductive cbstep_top (ρ : cenv) : ccexp -> fuel -> cres -> interactions -> Prop :=
| CbstepT_link_Res :
  forall {x cce1 cce2 i1 i2 U c l v r I1 I2},
    cbstep_top_fuel ρ cce1 i1 (CRes (CTag U c l v)) I1 ->
    ~ (l \in U) -> (* Values crossing the program boundary are foreign values. *)
    cbstep_top_fuel (M.set x (CTag U c l v) ρ) cce2 i2 r I2 ->
    cbstep_top ρ (CClink x cce1 cce2) (S (i1 + i2)) r (I1 :|: I2)

| CbstepT_link_OOT :
  forall {x cce1 cce2 i I1},
    cbstep_top_fuel ρ cce1 i COOT I1 ->
    cbstep_top ρ (CClink x cce1 cce2) (S i) COOT I1

with cbstep_top_fuel (ρ : cenv) : ccexp -> fuel -> cres -> interactions -> Prop :=
| CbstepTF_unit :
  forall {U c e i r I},
    cbstep_fuel U c ρ e i r I ->
    cbstep_top_fuel ρ (CCunit U c e) i r I

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
Lemma cbstep_fuel_cbstep_top_fuel U I c ρ e j r:
  cbstep_fuel U c ρ e j r I ->
  cbstep_top_fuel ρ (CCunit U c e) j r I.
Proof.
  intros H. eapply CbstepTF_unit; eauto.
Qed.

Lemma cbstep_top_fuel_cbstep_fuel U c ρ e j r I:
  cbstep_top_fuel ρ (CCunit U c e) j r I ->
  cbstep_fuel U c ρ e j r I.
Proof. intros H. fcrush. Qed.

(* `internals_context_of` reads off a single unit, and restricts to subtrees. *)
Lemma internals_context_of_unit {Θ U c e} :
  internals_context_of Θ (CCunit U c e) ->
  U <--> Θ c.
Proof. intros HΘ; exact (HΘ c U (Has_unit_unit U c e)). Qed.

Lemma internals_context_of_link1 {Θ x cce1 cce2} :
  internals_context_of Θ (CClink x cce1 cce2) ->
  internals_context_of Θ cce1.
Proof.
  intros HΘ c U Hunit.
  exact (HΘ c U (Has_unit_link1 x cce1 cce2 c U Hunit)).
Qed.

Lemma internals_context_of_link2 {Θ x cce1 cce2} :
  internals_context_of Θ (CClink x cce1 cce2) ->
  internals_context_of Θ cce2.
Proof.
  intros HΘ c U Hunit.
  exact (HΘ c U (Has_unit_link2 x cce1 cce2 c U Hunit)).
Qed.

(* A value returned by a linked program agrees with Θ. *)
Lemma cbstep_top_wf_cres Θ :
  forall ρ cce i r I,
    cbstep_top ρ cce i r I ->
    internals_context_of Θ cce ->
    wf_cenv Θ ρ ->
    wf_cres Θ r.
Proof.
  intros ρ cce i r I Hstep.
  induction Hstep as
    [ ρ x cce1 cce2 i1 i2 U c l v r I1 I2 Hfuel1 IH1 Hforeign Hfuel2 IH2
    | ρ x cce1 cce2 i I1 Hfuel1 IH1
    | ρ U c e i r I Hfuel
    | ρ x cce1 cce2
    | ρ x cce1 cce2 i r I Htop IHtop ]
    using cbstep_top_ind'
    with (P := fun ρ cce i r I =>
                 internals_context_of Θ cce ->
                 wf_cenv Θ ρ ->
                 wf_cres Θ r)
         (P0 := fun ρ cce i r I =>
                  internals_context_of Θ cce ->
                  wf_cenv Θ ρ ->
                  wf_cres Θ r).

  - (* CbstepT_link_Res: the linked value agrees with Θ, so the second unit
       still runs in a Θ-consistent environment *)
    intros HΘ Hρ.
    pose proof (wf_cres_CRes_inv (IH1 (internals_context_of_link1 HΘ) Hρ))
      as Hclo.
    pose proof (wf_cenv_set x (CTag U c l v) Hρ Hclo) as Hρx.
    exact (IH2 (internals_context_of_link2 HΘ) Hρx).

  - (* CbstepT_link_OOT: no value is returned *)
    intros HΘ Hρ.
    apply WF_COOT.

  - (* CbstepTF_unit *)
    intros HΘ Hρ.
    exact (cbstep_fuel_wf_cres Θ U c ρ e i r I
             (internals_context_of_unit HΘ) Hρ Hfuel).

  - (* CbstepTF_link_OOT: no value is returned *)
    intros HΘ Hρ.
    apply WF_COOT.

  - (* CbstepTF_link_Step *)
    intros HΘ Hρ.
    exact (IHtop HΘ Hρ).
Qed.

Lemma cbstep_top_fuel_wf_cres Θ ρ cce i r I :
  internals_context_of Θ cce ->
  wf_cenv Θ ρ ->
  cbstep_top_fuel ρ cce i r I ->
  wf_cres Θ r.
Proof.
  intros HΘ Hρ Hstep.
  inv Hstep.
  - match goal with
    | [Hs : cbstep_fuel _ _ _ _ _ _ _ |- _] =>
        exact (cbstep_fuel_wf_cres Θ _ _ _ _ _ _ _
                 (internals_context_of_unit HΘ) Hρ Hs)
    end.
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
Lemma cbstep_top_respect Θ :
  forall ρ cce i r I,
    cbstep_top ρ cce i r I ->
    internals_context_of Θ cce ->
    wf_cenv Θ ρ ->
    forall c0, interactions_respect (Θ c0) c0 I.
Proof.
  intros ρ cce i r I Hstep.
  induction Hstep as
    [ ρ x cce1 cce2 i1 i2 U c l v r I1 I2 Hfuel1 IH1 Hforeign Hfuel2 IH2
    | ρ x cce1 cce2 i I1 Hfuel1 IH1
    | ρ U c e i r I Hfuel
    | ρ x cce1 cce2
    | ρ x cce1 cce2 i r I Htop IHtop ]
    using cbstep_top_ind'
    with (P := fun ρ cce i r I =>
                 internals_context_of Θ cce ->
                 wf_cenv Θ ρ ->
                 forall c0, interactions_respect (Θ c0) c0 I)
         (P0 := fun ρ cce i r I =>
                  internals_context_of Θ cce ->
                  wf_cenv Θ ρ ->
                  forall c0, interactions_respect (Θ c0) c0 I).

  - (* CbstepT_link_Res *)
    intros HΘ Hρ c0.
    pose proof (internals_context_of_link1 HΘ) as HΘ1.
    pose proof (internals_context_of_link2 HΘ) as HΘ2.
    pose proof (wf_cres_CRes_inv
                  (cbstep_top_fuel_wf_cres Θ ρ cce1 i1 _ I1 HΘ1 Hρ Hfuel1))
      as Hclo.
    pose proof (wf_cenv_set x (CTag U c l v) Hρ Hclo) as Hρx.
    exact (interactions_respect_union (Θ c0) c0 I1 I2
             (IH1 HΘ1 Hρ c0) (IH2 HΘ2 Hρx c0)).

  - (* CbstepT_link_OOT: only the first unit ran *)
    intros HΘ Hρ c0.
    exact (IH1 (internals_context_of_link1 HΘ) Hρ c0).

  - (* CbstepTF_unit: hand off to the per-unit theorem *)
    intros HΘ Hρ c0.
    exact (cbstep_fuel_respect Θ U c ρ e i r I Hfuel
             (internals_context_of_unit HΘ) Hρ c0).

  - (* CbstepTF_link_OOT: nothing is recorded *)
    intros HΘ Hρ c0.
    apply interactions_respect_empty.

  - (* CbstepTF_link_Step *)
    intros HΘ Hρ c0.
    exact (IHtop HΘ Hρ c0).
Qed.

Lemma cbstep_top_fuel_respect Θ ρ cce i r I :
  cbstep_top_fuel ρ cce i r I ->
  internals_context_of Θ cce ->
  wf_cenv Θ ρ ->
  forall c0, interactions_respect (Θ c0) c0 I.
Proof.
  intros Hstep HΘ Hρ c0.
  inv Hstep.
  - match goal with
    | [Hs : cbstep_fuel _ _ _ _ _ _ _ |- _] =>
        exact (cbstep_fuel_respect Θ _ _ _ _ _ _ _ Hs
                 (internals_context_of_unit HΘ) Hρ c0)
    end.
  - apply interactions_respect_empty.
  - match goal with
    | [Hs : cbstep_top _ _ _ _ _ |- _] =>
        exact (cbstep_top_respect Θ _ _ _ _ _ Hs HΘ Hρ c0)
    end.
Qed.

(* Every unit of the linked program is closed under the interactions the whole
   program records --- not just under its own. *)
Lemma cbstep_top_closed Θ ρ cce i r I :
  internals_context_of Θ cce ->
  wf_cenv Θ ρ ->
  cbstep_top ρ cce i r I ->
  forall c U, has_unit cce c U -> internals_closed U c I.
Proof.
  intros HΘ Hρ Hstep c U Hunit.
  apply interactions_respect_closed.
  apply (interactions_respect_Same_set U (Θ c) c I (HΘ c U Hunit)).
  exact (cbstep_top_respect Θ ρ cce i r I Hstep HΘ Hρ c).
Qed.

Lemma cbstep_top_fuel_closed Θ ρ cce i r I :
  internals_context_of Θ cce ->
  wf_cenv Θ ρ ->
  cbstep_top_fuel ρ cce i r I ->
  forall c U, has_unit cce c U -> internals_closed U c I.
Proof.
  intros HΘ Hρ Hstep c U Hunit.
  apply interactions_respect_closed.
  apply (interactions_respect_Same_set U (Θ c) c I (HΘ c U Hunit)).
  exact (cbstep_top_fuel_respect Θ ρ cce i r I Hstep HΘ Hρ c).
Qed.

(* Bipartite Interaction *)
(* The interactions form a bipartite graph if each compilation unit is uniquely labeled *)
Definition interactions_bipartite (I : interactions) : Prop :=
  forall cl1 cl2,
    ((cl1, cl2) \in I) ->
    cl1 <> cl2.

Lemma interactions_bipartite_empty :
  interactions_bipartite (Empty_set interaction).
Proof. intros cl1 cl2 Hin; destruct Hin. Qed.

(* Introduction and elimination labels *)
(* An interaction ((c', l'), (c, l)) always has an *introduction* label on the
   left -- `l'` was attached to a closure by `Cbstep_fun`, so it comes from an
   `Efun` node -- and an *elimination* label on the right -- `l` is the label of
   the `Eapp` node being executed.  Separating the two syntactically is what
   makes the two endpoints distinguishable. *)
Inductive intro_label : exp -> labels :=
| Intro_fun1 :
  forall f l xs e k,
    intro_label (Efun f l xs e k) l

| Intro_fun2 :
  forall f l0 l1 xs e k,
    intro_label e l1 ->
    intro_label (Efun f l0 xs e k) l1

| Intro_fun3 :
  forall f l0 l1 xs e k,
    intro_label k l1 ->
    intro_label (Efun f l0 xs e k) l1

| Intro_letapp :
  forall x f l0 l1 xs k,
    intro_label k l1 ->
    intro_label (Eletapp x f l0 xs k) l1

| Intro_constr :
  forall x l0 l1 t xs k,
    intro_label k l1 ->
    intro_label (Econstr x l0 t xs k) l1

| Intro_proj :
  forall x l0 l1 n y e,
    intro_label e l1 ->
    intro_label (Eproj x l0 n y e) l1

| Intro_case_hd :
  forall y l0 l1 t e cl,
    intro_label e l1 ->
    intro_label (Ecase y l0 ((t, e) :: cl)) l1

| Intro_case_tl :
  forall y l0 l1 t e cl,
    intro_label (Ecase y l0 cl) l1 ->
    intro_label (Ecase y l0 ((t, e) :: cl)) l1.

Inductive elim_label : exp -> labels :=
| Elim_app1 :
  forall f l xs,
    elim_label (Eapp f l xs) l

| Elim_letapp1 :
  forall x f l xs k,
    elim_label (Eletapp x f l xs k) l

| Elim_letapp2 :
  forall x f l0 l1 xs k,
    elim_label k l1 ->
    elim_label (Eletapp x f l0 xs k) l1

| Elim_fun1 :
  forall f l0 l1 xs e k,
    elim_label e l1 ->
    elim_label (Efun f l0 xs e k) l1

| Elim_fun2 :
  forall f l0 l1 xs e k,
    elim_label k l1 ->
    elim_label (Efun f l0 xs e k) l1

| Elim_constr :
  forall x l0 l1 t xs k,
    elim_label k l1 ->
    elim_label (Econstr x l0 t xs k) l1

| Elim_proj :
  forall x l0 l1 n y e,
    elim_label e l1 ->
    elim_label (Eproj x l0 n y e) l1

| Elim_case_hd :
  forall y l0 l1 t e cl,
    elim_label e l1 ->
    elim_label (Ecase y l0 ((t, e) :: cl)) l1

| Elim_case_tl :
  forall y l0 l1 t e cl,
    elim_label (Ecase y l0 cl) l1 ->
    elim_label (Ecase y l0 ((t, e) :: cl)) l1.

Hint Constructors intro_label : core.
Hint Constructors elim_label : core.

Lemma intro_label_has_label e :
  intro_label e \subset has_label e.
Proof.
  intros l Hl.
  induction Hl; eauto.
Qed.

Lemma elim_label_has_label e :
  elim_label e \subset has_label e.
Proof.
  intros l Hl.
  induction Hl; eauto.
Qed.

(* Label Context *)
(* Assigns to each color the labels that the compilation unit can use. *)
Definition labels_context := color -> labels.

(* `Λ c` maps to the introduction labels of the compilation unit containing `e`. *)
(* The unit of color `c` draws its closure labels from `Λ c`, and never applies
   a value at one of them.  Both halves are inherited by *subexpressions*, and
   neither mentions a running environment -- that is what makes the invariant
   survive `set_lists`, where arguments cross unit boundaries. *)
Definition labels_separated (Λ : labels_context) (c : color) (e : exp) : Prop :=
  (intro_label e \subset Λ c) /\
  (forall l, (l \in elim_label e) -> ~ (l \in Λ c)).

Lemma labels_separated_fun_label {Λ c f l xs e k} :
  labels_separated Λ c (Efun f l xs e k) ->
  l \in Λ c.
Proof. intros [Hintro Helim]; apply Hintro; apply Intro_fun1. Qed.

Lemma labels_separated_fun_body {Λ c f l xs e k} :
  labels_separated Λ c (Efun f l xs e k) ->
  labels_separated Λ c e.
Proof.
  intros [Hintro Helim]; split.
  - intros l1 Hl1; apply Hintro; apply Intro_fun2; exact Hl1.
  - intros l1 Hl1; apply Helim; apply Elim_fun1; exact Hl1.
Qed.

Lemma labels_separated_fun_cont {Λ c f l xs e k} :
  labels_separated Λ c (Efun f l xs e k) ->
  labels_separated Λ c k.
Proof.
  intros [Hintro Helim]; split.
  - intros l1 Hl1; apply Hintro; apply Intro_fun3; exact Hl1.
  - intros l1 Hl1; apply Helim; apply Elim_fun2; exact Hl1.
Qed.

Lemma labels_separated_app_label {Λ c f l xs} :
  labels_separated Λ c (Eapp f l xs) ->
  ~ (l \in Λ c).
Proof. intros [Hintro Helim]; apply Helim; apply Elim_app1. Qed.

(* Every closure carries a label drawn from its own unit's introduction labels,
   and a body that keeps introduction and elimination labels apart. *)
Inductive intro_labeled (Λ : labels_context) : clval -> Prop :=
| IL_TAG :
  forall U c l v,
    (l \in Λ c) ->
    intro_labeled' Λ c v ->
    intro_labeled Λ (CTag U c l v)

with intro_labeled' (Λ : labels_context) : color -> cval -> Prop :=
| IL_CVfun :
  forall c f ρ xs e,
    intro_cenv Λ ρ ->
    labels_separated Λ c e ->
    intro_labeled' Λ c (CVfun f ρ xs e)

| IL_CVconstr_nil :
  forall c t,
    intro_labeled' Λ c (CVconstr t [])

| IL_CVconstr :
  forall c t v vs,
    intro_labeled Λ v ->
    intro_labeled' Λ c (CVconstr t vs) ->
    intro_labeled' Λ c (CVconstr t (v :: vs))

with intro_cenv (Λ : labels_context) : cenv -> Prop :=
| IL_cenv :
  forall ρ,
    (forall x v, ρ ! x = Some v -> intro_labeled Λ v) ->
    intro_cenv Λ ρ.

Hint Constructors intro_labeled : core.
Hint Constructors intro_labeled' : core.
Hint Constructors intro_cenv : core.

Scheme intro_labeled_mut := Induction for intro_labeled Sort Prop
with intro_labeled'_mut := Induction for intro_labeled' Sort Prop
with intro_cenv_mut := Induction for intro_cenv Sort Prop.

Lemma intro_labeled_CTag_inv {Λ U c l v} :
  intro_labeled Λ (CTag U c l v) ->
  (l \in Λ c) /\ intro_labeled' Λ c v.
Proof. intros Hil; inv Hil; split; assumption. Qed.

Lemma intro_labeled_CVfun_inv {Λ c f ρ xs e} :
  intro_labeled' Λ c (CVfun f ρ xs e) ->
  intro_cenv Λ ρ /\ labels_separated Λ c e.
Proof. intros Hil; inv Hil; split; assumption. Qed.

Lemma intro_cenv_get {Λ ρ} :
  intro_cenv Λ ρ ->
  forall x v,
    ρ ! x = Some v ->
    intro_labeled Λ v.
Proof. fcrush. Qed.

Lemma intro_cenv_get_list {Λ ρ} :
  intro_cenv Λ ρ ->
  forall xs vs,
    get_list xs ρ = Some vs ->
    Forall (intro_labeled Λ) vs.
Proof.
  intros Henv xs.
  induction xs as [| x xs IHxs]; simpl; intros vs Hget; fcrush.
Qed.

Lemma intro_cenv_set {Λ ρ} x v :
  intro_cenv Λ ρ ->
  intro_labeled Λ v ->
  intro_cenv Λ (M.set x v ρ).
Proof.
  intros Henv Hv.
  inv Henv.
  constructor; intros y w Hget.
  destruct (M.elt_eq x y); subst.
  - rewrite M.gss in *; fcrush.
  - rewrite M.gso in *; fcrush.
Qed.

Lemma intro_cenv_set_lists {Λ} :
  forall ρ,
    intro_cenv Λ ρ ->
    forall vs xs ρ',
      Forall (intro_labeled Λ) vs ->
      set_lists xs vs ρ = Some ρ' ->
      intro_cenv Λ ρ'.
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
    | [Hv : intro_labeled Λ v, Hvs' : Forall (intro_labeled Λ) vs |- _] =>
        exact (intro_cenv_set x v (IHvs xs ρ'' Hvs' Heqρ'') Hv)
    end.
Qed.

Lemma cbstep_bipartite Λ :
  forall U c ρ e i r I,
    cbstep U c ρ e i r I ->
    intro_cenv Λ ρ ->
    labels_separated Λ c e ->
    interactions_bipartite I.
Proof.
  intros U c ρ e i r I Hstep.
  induction Hstep as
    [ U c ρ x v Hget
    | U c ρ I f l xs e k i r IHfuel
    | U c ρ I' U' f f' c' l l' xs ρ' xs' e vs ρ'' i r
        Hget Hgetl Hsetl IHfuel Hsnd
    | U c ρ e
    | U c ρ I e i r IHstep ]
    using cbstep_ind'
    with (P := fun U c ρ e i r I =>
                 intro_cenv Λ ρ ->
                 labels_separated Λ c e ->
                 interactions_bipartite I)
         (P0 := fun U c ρ e i r I =>
                  intro_cenv Λ ρ ->
                  labels_separated Λ c e ->
                  interactions_bipartite I).

  - (* Cbstep_ret: nothing is recorded *)
    intros Hρ Hsep.
    apply interactions_bipartite_empty.

  - (* Cbstep_fun: the closure's label comes from Λ c *)
    intros Hρ Hsep.
    apply IHHstep.
    + apply intro_cenv_set; [exact Hρ |].
      apply IL_TAG; [exact (labels_separated_fun_label Hsep) |].
      apply IL_CVfun; [exact Hρ | exact (labels_separated_fun_body Hsep)].
    + exact (labels_separated_fun_cont Hsep).

  - (* Cbstep_app *)
    intros Hρ Hsep.
    pose proof (intro_cenv_get Hρ f _ Hget) as Hclo.
    destruct (intro_labeled_CTag_inv Hclo) as [Hl' Hfun].
    destruct (intro_labeled_CVfun_inv Hfun) as [Hρ' Hsep'].
    pose proof (intro_cenv_get_list Hρ xs vs Hgetl) as Hvs.
    pose proof (intro_cenv_set f' (CTag U' c' l' (CVfun f' ρ' xs' e)) Hρ' Hclo)
      as Hρ'f.
    pose proof (intro_cenv_set_lists _ Hρ'f vs xs' ρ'' Hvs Hsetl) as Hρ''.
    pose proof (Hsnd Hρ'' Hsep') as HI'.
    intros cl1 cl2 Hin.
    inv Hin.
    + (* the interaction just recorded: an intro label against an elim label *)
      match goal with [Hsing : _ \in [set _] |- _] => inv Hsing end.
      intros Heq; inv Heq.
      exact (labels_separated_app_label Hsep Hl').
    + match goal with [HI : _ \in I' |- _] => exact (HI' cl1 cl2 HI) end.

  - (* CbstepF_OOT: nothing is recorded *)
    intros Hρ Hsep.
    apply interactions_bipartite_empty.

  - (* CbstepF_Step *)
    intros Hρ Hsep.
    exact (IHIHstep Hρ Hsep).
Qed.

Lemma cbstep_fuel_bipartite Λ :
  forall U c ρ e i r I,
    cbstep_fuel U c ρ e i r I ->
    intro_cenv Λ ρ ->
    labels_separated Λ c e ->
    interactions_bipartite I.
Proof.
  intros U c ρ e i r I Hstep Hρ Hsep.
  inv Hstep.
  - apply interactions_bipartite_empty.
  - match goal with
    | [Hs : cbstep _ _ _ _ _ _ _ |- _] =>
        exact (cbstep_bipartite Λ _ _ _ _ _ _ _ Hs Hρ Hsep)
    end.
Qed.

(* The purely syntactic bridge *)
(* An `Ecase`'s branches contribute exactly the labels that `unique_label_case`
   accumulates in `L`. *)
Lemma unique_label_case_subset {cl L} :
  unique_label_case cl L ->
  forall y l0,
    (intro_label (Ecase y l0 cl) \subset L) /\ (elim_label (Ecase y l0 cl) \subset L).
Proof.
  intros Hcase.
  induction Hcase as [| t e cl L Hdisj Huniq Hcase IH]; intros y l0.
  - split; intros l Hl; inv Hl.
  - destruct (IH y l0) as [Hintro Helim].
    split; intros l Hl; inv Hl.
    + left; apply intro_label_has_label; assumption.
    + right; apply Hintro; assumption.
    + left; apply elim_label_has_label; assumption.
    + right; apply Helim; assumption.
Qed.

(* `inv` leaves membership facts as raw applications (`elim_label e l`) while
   the premises of `unique_label` carry them as `Ensembles.In`.  Ltac matches
   syntactically, so normalize to the raw form before matching on either. *)
Ltac label_norm := try (unfold Ensembles.In in *).

(* Reduce every `intro_label` / `elim_label` fact in the context to the
   `has_label` fact it implies. *)
Ltac label_has :=
  repeat match goal with
         | [H : intro_label ?e1 ?x |- _] =>
             apply (intro_label_has_label e1 x) in H; unfold Ensembles.In in H
         | [H : elim_label ?e1 ?x |- _] =>
             apply (elim_label_has_label e1 x) in H; unfold Ensembles.In in H
         end.

(* The ways an introduction label and an elimination label of a uniquely
   labeled expression could coincide, each ruled out by a premise of
   `unique_label`.  The induction hypotheses are applied by an explicit clause
   rather than by `eauto`: their conclusion is headed by `not`, which `eauto`
   does not unfold, so it would never see that they prove `False`. *)
Ltac label_contra :=
  label_norm;
  first
    [ (* both labels sit in the same subterm *)
      match goal with
      | [IH : forall lz, intro_label ?e1 lz -> ~ elim_label ?e1 lz,
         Hi : intro_label ?e1 ?x, He : elim_label ?e1 ?x |- False] =>
          exact (IH x Hi He)
      | [IH : forall yz lz0 lz, intro_label (Ecase yz lz0 ?cl1) lz ->
                                ~ elim_label (Ecase yz lz0 ?cl1) lz,
         Hi : intro_label (Ecase ?y1 ?l1 ?cl1) ?x,
         He : elim_label (Ecase ?y1 ?l1 ?cl1) ?x |- False] =>
          exact (IH y1 l1 x Hi He)
      end

    | (* one label in a case branch, the other in the remaining branches *)
      match goal with
      | [Hd : Disjoint _ (has_label ?e1) ?L1, Hc : unique_label_case ?cl1 ?L1,
         Hi : intro_label ?e1 ?x,
         He : elim_label (Ecase ?y ?l1 ?cl1) ?x |- False] =>
          exact (Disjoint_In_l _ _ x Hd (intro_label_has_label e1 x Hi)
                   (proj2 (unique_label_case_subset Hc y l1) x He))
      | [Hd : Disjoint _ (has_label ?e1) ?L1, Hc : unique_label_case ?cl1 ?L1,
         Hi : intro_label (Ecase ?y ?l1 ?cl1) ?x,
         He : elim_label ?e1 ?x |- False] =>
          exact (Disjoint_In_l _ _ x Hd (elim_label_has_label e1 x He)
                   (proj1 (unique_label_case_subset Hc y l1) x Hi))
      end

    | (* otherwise both labels are `has_label` facts, and either the node's own
         label does not occur in that subterm, or the two subterms are
         disjoint *)
      label_has;
      match goal with
      | [Hn : ~ has_label ?e1 ?x, H : has_label ?e1 ?x |- False] =>
          exact (Hn H)
      | [Hd : Disjoint _ (has_label ?e1) (has_label ?e2),
         H1 : has_label ?e1 ?x, H2 : has_label ?e2 ?x |- False] =>
          exact (Disjoint_In_l _ _ x Hd H1 H2)
      end

    | solve [eauto] ].

(* Unique labeling is exactly what separates introduction from elimination:
   an `Efun` label can never also be an `Eapp` label. *)
Lemma unique_label_separated e :
  unique_label e ->
  forall l, (l \in intro_label e) -> ~ (l \in elim_label e).
Proof.
  intros Huniq.
  induction Huniq using unique_label_mut
    with (P := fun e0 _ => forall l,
                 (l \in intro_label e0) -> ~ (l \in elim_label e0))
         (P0 := fun cl L _ => forall y l0 l,
                  (l \in intro_label (Ecase y l0 cl)) ->
                  ~ (l \in elim_label (Ecase y l0 cl))).

  - (* Unique_ret: nothing is introduced *)
    intros lab Hintro; inv Hintro.

  - (* Unique_fun *)
    intros lab Hintro Helim.
    inv Hintro; inv Helim; label_contra.

  - (* Unique_app: nothing is introduced *)
    intros lab Hintro; inv Hintro.

  - (* Unique_letapp *)
    intros lab Hintro Helim.
    inv Hintro; inv Helim; label_contra.

  - (* Unique_constr *)
    intros lab Hintro Helim.
    inv Hintro; inv Helim; label_contra.

  - (* Unique_proj *)
    intros lab Hintro Helim.
    inv Hintro; inv Helim; label_contra.

  - (* Unique_case: the branches carry it *)
    intros lab Hintro Helim; label_contra.

  - (* Unique_case_nil: nothing is introduced *)
    intros y l0 lab Hintro; inv Hintro.

  - (* Unique_case_tl *)
    intros y l0 lab Hintro Helim.
    inv Hintro; inv Helim; label_contra.
Qed.

(* Top-level Bipartite Interaction *)

(* Each unit of a colored tree, paired with its code. *)
Inductive has_code : ccexp -> color -> exp -> Prop :=
| Has_code_unit :
  forall U c e,
    has_code (CCunit U c e) c e

| Has_code_link1 :
  forall x cce1 cce2 c e,
    has_code cce1 c e ->
    has_code (CClink x cce1 cce2) c e

| Has_code_link2 :
  forall x cce1 cce2 c e,
    has_code cce2 c e ->
    has_code (CClink x cce1 cce2) c e.

Hint Constructors has_code : core.

Lemma coloring_range_code {c1 ce c2 cce} :
  coloring c1 ce c2 cce ->
  forall c e, has_code cce c e -> c1 <= c < c2.
Proof.
  intros Hcol.
  induction Hcol as [c U e | c1 c2 c3 x e1 e2 cce1 cce2 Hc1 IH1 Hc2 IH2];
    intros c0 e0 Hcode.
  - inv Hcode; lia.
  - inv Hcode.
    + match goal with
      | [Hu : has_code cce1 c0 e0 |- _] => destruct (IH1 c0 e0 Hu) as [Hlo Hhi]
      end.
      pose proof (coloring_mono Hc2) as Hm; lia.
    + match goal with
      | [Hu : has_code cce2 c0 e0 |- _] => destruct (IH2 c0 e0 Hu) as [Hlo Hhi]
      end.
      pose proof (coloring_mono Hc1) as Hm; lia.
Qed.

Lemma coloring_unique_code {c1 ce c2 cce} :
  coloring c1 ce c2 cce ->
  forall c e e',
    has_code cce c e ->
    has_code cce c e' ->
    e = e'.
Proof.
  intros Hcol.
  induction Hcol as [c U e | c1 c2 c3 x e1 e2 cce1 cce2 Hc1 IH1 Hc2 IH2];
    intros c0 e0 e0' Hu Hu'.
  - inv Hu; inv Hu'; reflexivity.
  - inv Hu; inv Hu'.
    + match goal with
      | [Ha : has_code cce1 c0 e0, Hb : has_code cce1 c0 e0' |- _] =>
          exact (IH1 c0 e0 e0' Ha Hb)
      end.
    + exfalso.
      match goal with
      | [Ha : has_code cce1 c0 e0, Hb : has_code cce2 c0 e0' |- _] =>
          destruct (coloring_range_code Hc1 c0 e0 Ha) as [Hlo Hhi];
          destruct (coloring_range_code Hc2 c0 e0' Hb) as [Hlo' Hhi']
      end; lia.
    + exfalso.
      match goal with
      | [Ha : has_code cce2 c0 e0, Hb : has_code cce1 c0 e0' |- _] =>
          destruct (coloring_range_code Hc2 c0 e0 Ha) as [Hlo Hhi];
          destruct (coloring_range_code Hc1 c0 e0' Hb) as [Hlo' Hhi']
      end; lia.
    + match goal with
      | [Ha : has_code cce2 c0 e0, Hb : has_code cce2 c0 e0' |- _] =>
          exact (IH2 c0 e0 e0' Ha Hb)
      end.
Qed.

(* `Λ` agrees with the coloring of `cce`. *)
Definition labels_context_of (Λ : labels_context) (cce : ccexp) : Prop :=
  forall c e, has_code cce c e -> labels_separated Λ c e.

Lemma labels_context_of_unit {Λ U c e} :
  labels_context_of Λ (CCunit U c e) ->
  labels_separated Λ c e.
Proof. intros HΛ; exact (HΛ c e (Has_code_unit U c e)). Qed.

Lemma labels_context_of_link1 {Λ x cce1 cce2} :
  labels_context_of Λ (CClink x cce1 cce2) ->
  labels_context_of Λ cce1.
Proof.
  intros HΛ c e Hcode.
  exact (HΛ c e (Has_code_link1 x cce1 cce2 c e Hcode)).
Qed.

Lemma labels_context_of_link2 {Λ x cce1 cce2} :
  labels_context_of Λ (CClink x cce1 cce2) ->
  labels_context_of Λ cce2.
Proof.
  intros HΛ c e Hcode.
  exact (HΛ c e (Has_code_link2 x cce1 cce2 c e Hcode)).
Qed.

(* The introduction labels of each unit, read off the colored tree. *)
Definition lctx_of (cce : ccexp) : labels_context :=
  fun c => fun l => exists e, has_code cce c e /\ (l \in intro_label e).

(* Uniquely labeled units give a separated labels context: a label can only be
   an introduction label of its own unit, and there it is not an elimination
   label. *)
Lemma lctx_of_correct {c1 ce c2 cce} :
  coloring c1 ce c2 cce ->
  (forall c e, has_code cce c e -> unique_label e) ->
  labels_context_of (lctx_of cce) cce.
Proof.
  intros Hcol Huniq c e Hcode.
  unfold lctx_of, Ensembles.In.
  split.
  - intros l Hl; exists e; split; [exact Hcode | exact Hl].
  - intros l Hl [e' [Hcode' Hl']].
    rewrite <- (coloring_unique_code Hcol c e' e Hcode' Hcode) in Hl.
    exact (unique_label_separated e' (Huniq c e' Hcode') l Hl' Hl).
Qed.

(* `intro_labeled` of a returned value, as for `wf_cres`. *)
Lemma cbstep_intro_res_aux Λ :
  forall U c ρ e i r I,
    cbstep U c ρ e i r I ->
    intro_cenv Λ ρ ->
    labels_separated Λ c e ->
    forall v, r = CRes v -> intro_labeled Λ v.
Proof.
  intros U c ρ e i r I Hstep.
  induction Hstep as
    [ U c ρ x v Hget
    | U c ρ I f l xs e k i r Hfuel IHfuel
    | U c ρ I' U' f f' c' l l' xs ρ' xs' e vs ρ'' i r
        Hget Hgetl Hsetl Hfuel IHfuel Hsnd
    | U c ρ e
    | U c ρ I e i r Hsub IHstep ]
    using cbstep_ind'
    with (P := fun U c ρ e i r I =>
                 intro_cenv Λ ρ -> labels_separated Λ c e ->
                 forall v, r = CRes v -> intro_labeled Λ v)
         (P0 := fun U c ρ e i r I =>
                  intro_cenv Λ ρ -> labels_separated Λ c e ->
                  forall v, r = CRes v -> intro_labeled Λ v).

  - (* Cbstep_ret *)
    intros Hρ Hsep v0 Heqr.
    inv Heqr.
    eapply intro_cenv_get; eauto.

  - (* Cbstep_fun *)
    intros Hρ Hsep v0 Heqr.
    apply (IHfuel (intro_cenv_set f (CTag U c l (CVfun f ρ xs e)) Hρ
                     (IL_TAG Λ U c l (CVfun f ρ xs e)
                        (labels_separated_fun_label Hsep)
                        (IL_CVfun Λ c f ρ xs e Hρ
                           (labels_separated_fun_body Hsep))))
                  (labels_separated_fun_cont Hsep) v0 Heqr).

  - (* Cbstep_app *)
    intros Hρ Hsep v0 Heqr.
    pose proof (intro_cenv_get Hρ f _ Hget) as Hclo.
    destruct (intro_labeled_CTag_inv Hclo) as [Hl' Hfun].
    destruct (intro_labeled_CVfun_inv Hfun) as [Hρ' Hsep'].
    pose proof (intro_cenv_get_list Hρ xs vs Hgetl) as Hvs.
    pose proof (intro_cenv_set f' (CTag U' c' l' (CVfun f' ρ' xs' e)) Hρ' Hclo)
      as Hρ'f.
    pose proof (intro_cenv_set_lists _ Hρ'f vs xs' ρ'' Hvs Hsetl) as Hρ''.
    exact (IHfuel Hρ'' Hsep' v0 Heqr).

  - (* CbstepF_OOT *)
    intros Hρ Hsep v0 Heqr; discriminate Heqr.

  - (* CbstepF_Step *)
    intros Hρ Hsep v0 Heqr.
    exact (IHstep Hρ Hsep v0 Heqr).
Qed.

Lemma cbstep_intro_res Λ U c ρ e i v I :
  intro_cenv Λ ρ ->
  labels_separated Λ c e ->
  cbstep U c ρ e i (CRes v) I ->
  intro_labeled Λ v.
Proof.
  intros Hρ Hsep Hstep.
  exact (cbstep_intro_res_aux Λ U c ρ e i (CRes v) I Hstep Hρ Hsep v eq_refl).
Qed.

Lemma cbstep_fuel_intro_res Λ U c ρ e i v I :
  intro_cenv Λ ρ ->
  labels_separated Λ c e ->
  cbstep_fuel U c ρ e i (CRes v) I ->
  intro_labeled Λ v.
Proof.
  intros Hρ Hsep Hstep.
  inv Hstep.
  match goal with
  | [Hs : cbstep _ _ _ _ _ (CRes v) _ |- _] =>
      exact (cbstep_intro_res Λ U c ρ e _ v _ Hρ Hsep Hs)
  end.
Qed.

Lemma interactions_bipartite_union I1 I2 :
  interactions_bipartite I1 ->
  interactions_bipartite I2 ->
  interactions_bipartite (I1 :|: I2).
Proof.
  unfold interactions_bipartite.
  intros H1 H2 cl1 cl2 Hin.
  inv Hin.
  - match goal with [HI : _ \in I1 |- _] => exact (H1 cl1 cl2 HI) end.
  - match goal with [HI : _ \in I2 |- _] => exact (H2 cl1 cl2 HI) end.
Qed.

(* Top-level `intro_labeled` of a returned value. *)
Lemma cbstep_top_intro_res_aux Λ :
  forall ρ cce i r I,
    cbstep_top ρ cce i r I ->
    labels_context_of Λ cce ->
    intro_cenv Λ ρ ->
    forall v, r = CRes v -> intro_labeled Λ v.
Proof.
  intros ρ cce i r I Hstep.
  induction Hstep as
    [ ρ x cce1 cce2 i1 i2 U c l v r I1 I2 Hfuel1 IH1 Hforeign Hfuel2 IH2
    | ρ x cce1 cce2 i I1 Hfuel1 IH1
    | ρ U c e i r I Hfuel
    | ρ x cce1 cce2
    | ρ x cce1 cce2 i r I Htop IHtop ]
    using cbstep_top_ind'
    with (P := fun ρ cce i r I =>
                 labels_context_of Λ cce -> intro_cenv Λ ρ ->
                 forall v, r = CRes v -> intro_labeled Λ v)
         (P0 := fun ρ cce i r I =>
                  labels_context_of Λ cce -> intro_cenv Λ ρ ->
                  forall v, r = CRes v -> intro_labeled Λ v).

  - (* CbstepT_link_Res *)
    intros HΛ Hρ v0 Heqr.
    pose proof (IH1 (labels_context_of_link1 HΛ) Hρ (CTag U c l v) eq_refl) as Hclo.
    pose proof (intro_cenv_set x (CTag U c l v) Hρ Hclo) as Hρx.
    exact (IH2 (labels_context_of_link2 HΛ) Hρx v0 Heqr).

  - (* CbstepT_link_OOT *)
    intros HΛ Hρ v0 Heqr; discriminate Heqr.

  - (* CbstepTF_unit *)
    intros HΛ Hρ v0 Heqr; subst r.
    exact (cbstep_fuel_intro_res Λ U c ρ e i v0 I Hρ
             (labels_context_of_unit HΛ) Hfuel).

  - (* CbstepTF_link_OOT *)
    intros HΛ Hρ v0 Heqr; discriminate Heqr.

  - (* CbstepTF_link_Step *)
    intros HΛ Hρ v0 Heqr.
    exact (IHtop HΛ Hρ v0 Heqr).
Qed.

Lemma cbstep_top_intro_res Λ ρ cce i v I :
  labels_context_of Λ cce ->
  intro_cenv Λ ρ ->
  cbstep_top ρ cce i (CRes v) I ->
  intro_labeled Λ v.
Proof.
  intros HΛ Hρ Hstep.
  exact (cbstep_top_intro_res_aux Λ ρ cce i (CRes v) I Hstep HΛ Hρ v eq_refl).
Qed.

Lemma cbstep_top_fuel_intro_res Λ ρ cce i v I :
  labels_context_of Λ cce ->
  intro_cenv Λ ρ ->
  cbstep_top_fuel ρ cce i (CRes v) I ->
  intro_labeled Λ v.
Proof.
  intros HΛ Hρ Hstep.
  inv Hstep.
  - match goal with
    | [Hs : cbstep_fuel _ _ _ _ _ (CRes v) _ |- _] =>
        exact (cbstep_fuel_intro_res Λ _ _ _ _ _ v _ Hρ
                 (labels_context_of_unit HΛ) Hs)
    end.
  - match goal with
    | [Hs : cbstep_top _ _ _ (CRes v) _ |- _] =>
        exact (cbstep_top_intro_res Λ _ _ _ v _ HΛ Hρ Hs)
    end.
Qed.

(* The interactions of a whole linked program are bipartite. *)
Lemma cbstep_top_bipartite Λ :
  forall ρ cce i r I,
    cbstep_top ρ cce i r I ->
    labels_context_of Λ cce ->
    intro_cenv Λ ρ ->
    interactions_bipartite I.
Proof.
  intros ρ cce i r I Hstep.
  induction Hstep as
    [ ρ x cce1 cce2 i1 i2 U c l v r I1 I2 Hfuel1 IH1 Hforeign Hfuel2 IH2
    | ρ x cce1 cce2 i I1 Hfuel1 IH1
    | ρ U c e i r I Hfuel
    | ρ x cce1 cce2
    | ρ x cce1 cce2 i r I Htop IHtop ]
    using cbstep_top_ind'
    with (P := fun ρ cce i r I =>
                 labels_context_of Λ cce -> intro_cenv Λ ρ ->
                 interactions_bipartite I)
         (P0 := fun ρ cce i r I =>
                  labels_context_of Λ cce -> intro_cenv Λ ρ ->
                  interactions_bipartite I).

  - (* CbstepT_link_Res *)
    intros HΛ Hρ.
    pose proof (labels_context_of_link1 HΛ) as HΛ1.
    pose proof (labels_context_of_link2 HΛ) as HΛ2.
    pose proof (cbstep_top_fuel_intro_res Λ ρ cce1 i1 (CTag U c l v) I1
                  HΛ1 Hρ Hfuel1) as Hclo.
    pose proof (intro_cenv_set x (CTag U c l v) Hρ Hclo) as Hρx.
    exact (interactions_bipartite_union I1 I2 (IH1 HΛ1 Hρ) (IH2 HΛ2 Hρx)).

  - (* CbstepT_link_OOT *)
    intros HΛ Hρ.
    exact (IH1 (labels_context_of_link1 HΛ) Hρ).

  - (* CbstepTF_unit *)
    intros HΛ Hρ.
    exact (cbstep_fuel_bipartite Λ U c ρ e i r I Hfuel Hρ
             (labels_context_of_unit HΛ)).

  - (* CbstepTF_link_OOT *)
    intros HΛ Hρ.
    apply interactions_bipartite_empty.

  - (* CbstepTF_link_Step *)
    intros HΛ Hρ.
    exact (IHtop HΛ Hρ).
Qed.

Lemma cbstep_top_fuel_bipartite Λ ρ cce i r I :
  cbstep_top_fuel ρ cce i r I ->
  labels_context_of Λ cce ->
  intro_cenv Λ ρ ->
  interactions_bipartite I.
Proof.
  intros Hstep HΛ Hρ.
  inv Hstep.
  - match goal with
    | [Hs : cbstep_fuel _ _ _ _ _ _ _ |- _] =>
        exact (cbstep_fuel_bipartite Λ _ _ _ _ _ _ _ Hs Hρ
                 (labels_context_of_unit HΛ))
    end.
  - apply interactions_bipartite_empty.
  - match goal with
    | [Hs : cbstep_top _ _ _ _ _ |- _] =>
        exact (cbstep_top_bipartite Λ _ _ _ _ _ Hs HΛ Hρ)
    end.
Qed.

(* If every compilation unit is uniquely labeled, the interactions the linked
   program records form a bipartite graph. *)
Theorem cbstep_top_bipartite_unique_label c1 ce c2 cce ρ i r I :
  coloring c1 ce c2 cce ->
  (forall c e, has_code cce c e -> unique_label e) ->
  intro_cenv (lctx_of cce) ρ ->
  cbstep_top ρ cce i r I ->
  interactions_bipartite I.
Proof.
  intros Hcol Huniq Hρ Hstep.
  exact (cbstep_top_bipartite (lctx_of cce) ρ cce i r I Hstep
           (lctx_of_correct Hcol Huniq) Hρ).
Qed.

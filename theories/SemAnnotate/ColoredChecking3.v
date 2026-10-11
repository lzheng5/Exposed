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
Definition internals : Type := clabels.

(* `U` contains labels of only a single color, `c`, which is the attached to each compilation units. *)
Definition internals_monochromatic (U : internals) (c : color) : Prop :=
  forall cl, (cl \in U) -> fst cl = c.

(* `U` only contains internal labels in `I`. *)
Definition internals_sound (U : internals) (I : interactions) (cl : clabel) : Prop :=
  (cl \in U) -> internal I cl.

(* Closure Property *)
(* `U` is closed under reachable interactions `I`.
    Note that `U` is not necessarily all the internal events in `I`. *)
Definition internals_closed (U : internals) (I : interactions) : Prop :=
  forall cl cl',
    (cl \in U) ->
    (cl' \in (reachable I cl)) ->
    (cl' \in U).

Lemma empty_internals_closed I :
  internals_closed (Empty_set _) I.
Proof. unfold internals_closed. sfirstorder. Qed.

Lemma internals_closed_empty U :
  internals_closed U (Empty_set interaction).
Proof.
  unfold internals_closed, Ensembles.In.
  intros cl cl' HclU Hreach.
  assert (Heq : cl' = cl).
  { clear HclU.
    induction Hreach as [| ? Hin | ? Hin | ? ? ? IH1 ? IH2]; sfirstorder. }
  subst; exact HclU.
Qed.

Lemma internals_closed_equivalent U I I' :
  I <--> I' ->
  (internals_closed U I <-> internals_closed U I').
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
  unfold internals_closed.
  split; intros Hclosed cl cl' HclU Hr.
  - eapply Hclosed; [exact HclU |].
    eapply (Hreach I' I); eauto.
  - eapply Hclosed; [exact HclU |].
    eapply (Hreach I I'); eauto.
Qed.

Lemma internals_mono_closed_sound U I c :
  internals_closed U I ->
  internals_monochromatic U c ->
  forall cl,
    internals_sound U I cl.
Proof.
  unfold internals_closed, internals_monochromatic, internals_sound, internal,
    colors_of, Ensembles.Included, Ensembles.In in *.
  intros Hclosed Hmono cl HclU.
  destruct cl as [c0 l].
  pose proof (Hmono (c0, l) HclU) as Heqc; simpl in Heqc; subst c0.
  intros x [l0 Hreach].
  assert (HxU : U (x, l0)) by (eapply Hclosed; [exact HclU | exact Hreach]).
  pose proof (Hmono (x, l0) HxU) as Heqx; simpl in Heqx; subst.
  constructor.
Qed.

Lemma internals_closed_sound_l {U I} :
  internals_closed U I ->
  forall cl cl',
    ((cl, cl') \in I) ->
    internals_sound U I cl ->
    internals_sound U I cl'.
Proof.
  unfold internals_closed, internals_sound, internal, colors_of,
    Ensembles.Included, Ensembles.In in *.
  intros Hclosed cl cl' Hin Hsnd Hcl'U.
  destruct cl as [c l].
  destruct cl' as [c' l'].
  assert (Hreach_l : reachable I (c, l) (c', l')) by (apply Reachable_interact_l; exact Hin).
  assert (Hreach_r : reachable I (c', l') (c, l)) by (apply Reachable_interact_r; exact Hin).
  assert (HclU : U (c, l)) by (eapply Hclosed; [exact Hcl'U | exact Hreach_r]).
  pose proof (Hsnd HclU) as Hic.
  assert (Heqc : c' = c).
  { pose proof (Hic c' (ex_intro _ l' Hreach_l)) as Hmem.
    inversion Hmem; subst; reflexivity. }
  subst c'.
  intros y Hy.
  destruct Hy as [l0 Hreach2].
  assert (Hreach3 : reachable I (c, l) (y, l0)) by (eapply Reachable_step; [exact Hreach_l | exact Hreach2]).
  apply Hic.
  exists l0; exact Hreach3.
Qed.

Lemma internals_closed_sound_r {U I} :
  internals_closed U I ->
  forall cl cl',
    ((cl, cl') \in I) ->
    internals_sound U I cl' ->
    internals_sound U I cl.
Proof.
  unfold internals_closed, internals_sound, internal, colors_of,
    Ensembles.Included, Ensembles.In in *.
  intros Hclosed cl cl' Hin Hsnd HclU.
  destruct cl as [c l].
  destruct cl' as [c' l'].
  assert (Hreach_l : reachable I (c, l) (c', l')) by (apply Reachable_interact_l; exact Hin).
  assert (Hreach_r : reachable I (c', l') (c, l)) by (apply Reachable_interact_r; exact Hin).
  assert (Hcl'U : U (c', l')) by (eapply Hclosed; [exact HclU | exact Hreach_l]).
  pose proof (Hsnd Hcl'U) as Hic.
  assert (Heqc : c = c').
  { pose proof (Hic c (ex_intro _ l Hreach_r)) as Hmem.
    inversion Hmem; subst; reflexivity. }
  subst c'.
  intros y Hy.
  destruct Hy as [l0 Hreach2].
  assert (Hreach3 : reachable I (c, l') (y, l0)) by (eapply Reachable_step; [exact Hreach_r | exact Hreach2]).
  apply Hic.
  exists l0; exact Hreach3.
Qed.

(* Edge-wise characterization of closure *)
(* `U` is closed under `I` exactly when every *single* interaction of `I` joins
   two labels that are either both internal to `U` or both outside of it:
   reachability can then never leave `U`.  This is the form that the checking
   semantics produces one interaction at a time. *)
Definition interactions_respect (U : internals) (I : interactions) : Prop :=
  forall cl_i cl_e, ((cl_i, cl_e) \in I) -> ((cl_i \in U) <-> (cl_e \in U)).

Lemma interactions_respect_closed U I :
  interactions_respect U I ->
  internals_closed U I.
Proof.
  unfold interactions_respect, internals_closed, Ensembles.In.
  intros Hres cl cl' HclU Hreach.
  revert HclU.
  induction Hreach as [x | x y Hin | x y Hin | x y z Hxy IHxy Hyz IHyz].
  - intros HxU; exact HxU.
  - intros HxU; exact (proj1 (Hres x y Hin) HxU).
  - intros HxU; exact (proj2 (Hres y x Hin) HxU).
  - intros HxU; apply IHyz, IHxy, HxU.
Qed.

(* The converse: a single interaction of `I` is itself a reachability step, in
   both directions, so closure already forces every edge to be respected. *)
Lemma internals_closed_respect U I :
  internals_closed U I ->
  interactions_respect U I.
Proof.
  unfold internals_closed, interactions_respect, Ensembles.In.
  intros Hclosed cl_i cl_e Hin.
  split; intros Hmem.
  - exact (Hclosed cl_i cl_e Hmem (Reachable_interact_l I cl_i cl_e Hin)).
  - exact (Hclosed cl_e cl_i Hmem (Reachable_interact_r I cl_e cl_i Hin)).
Qed.

Theorem internals_closed_iff_respect U I :
  internals_closed U I <-> interactions_respect U I.
Proof.
  split; [exact (internals_closed_respect U I) | exact (interactions_respect_closed U I)].
Qed.

Lemma interactions_respect_empty U :
  interactions_respect U (Empty_set interaction).
Proof.
  unfold interactions_respect, Ensembles.In.
  intros cl_i cl_e Hin; destruct Hin.
Qed.

Lemma interactions_respect_add U cl_i cl_e I :
  ((cl_i \in U) <-> (cl_e \in U)) ->
  interactions_respect U I ->
  interactions_respect U ((cl_i, cl_e) |: I).
Proof.
  unfold interactions_respect.
  intros Hiff Hres cl_i' cl_e' Hin.
  inv Hin.
  - match goal with [Hsing : _ \in [set _] |- _] => inv Hsing end.
    assumption.
  - match goal with [HI : _ \in I |- _] => exact (Hres cl_i' cl_e' HI) end.
Qed.

Lemma interactions_respect_Same_set U U' I :
  U <--> U' ->
  interactions_respect U' I ->
  interactions_respect U I.
Proof.
  unfold interactions_respect, Ensembles.In.
  intros [Hsub Hsub'] Hres cl_i cl_e Hin.
  split; intros Hmem.
  - apply Hsub'; apply (proj1 (Hres cl_i cl_e Hin)); apply Hsub; exact Hmem.
  - apply Hsub'; apply (proj2 (Hres cl_i cl_e Hin)); apply Hsub; exact Hmem.
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

Definition interaction_sound (U_i : internals) (cl_i : clabel)
                                     (U_e : internals) (cl_e : clabel) : Prop :=
  match cl_i, cl_e with
  | (c_i, _), (c_e, _) =>
      (* Same color: the interaction stays within one compilation unit, so
         both endpoints are governed by one and the same internal set. *)
      (c_i = c_e ->
         (U_i <--> U_e) /\ ((cl_i \in U_i) <-> (cl_e \in U_e)))
      /\
      (* Different colors: a foreign interaction, so neither endpoint may be
         claimed as internal by either unit. *)
      (c_i <> c_e ->
         ~ (cl_i \in U_i) /\ ~ (cl_i \in U_e) /\
         ~ (cl_e \in U_i) /\ ~ (cl_e \in U_e))
  end.

(* Colors are decidable, so the two implications above can always be turned
   into the corresponding case split. *)
Lemma interaction_sound_inv U_i c_i l_i U_e c_e l_e :
  interaction_sound U_i (c_i, l_i) U_e (c_e, l_e) ->
  (c_i = c_e /\ (U_i <--> U_e) /\
     (((c_i, l_i) \in U_i) <-> ((c_e, l_e) \in U_e)))
  \/
  (c_i <> c_e /\
     ~ ((c_i, l_i) \in U_i) /\ ~ ((c_i, l_i) \in U_e) /\
     ~ ((c_e, l_e) \in U_i) /\ ~ ((c_e, l_e) \in U_e)).
Proof.
  intros [Hsame Hdiff].
  destruct (Nat.eq_dec c_i c_e) as [Heq | Hneq].
  - left.
    destruct (Hsame Heq) as [Hset Hiff].
    split; [exact Heq | split; [exact Hset | exact Hiff]].
  - right.
    destruct (Hdiff Hneq) as [Hcl_i_U_i [Hcl_i_U_e [Hcl_e_U_i Hcl_e_U_e]]].
    split; [exact Hneq
           | split; [exact Hcl_i_U_i
           | split; [exact Hcl_i_U_e
           | split; [exact Hcl_e_U_i | exact Hcl_e_U_e]]]].
Qed.

(* If the introduction site is internal, the interaction is internal: the
   colors agree, the two units share an internal set, and the elimination
   site is internal as well. *)
Lemma interaction_sound_intro U_i c_i l_i U_e c_e l_e :
  interaction_sound U_i (c_i, l_i) U_e (c_e, l_e) ->
  ((c_i, l_i) \in U_i) ->
  c_i = c_e /\ (U_i <--> U_e) /\ ((c_e, l_e) \in U_e).
Proof.
  intros Hsnd Hin.
  destruct (interaction_sound_inv _ _ _ _ _ _ Hsnd)
    as [[Heq [Hset Hiff]] | [_ [Hcl_i_U_i _]]].
  - split; [exact Heq | split; [exact Hset | apply (proj1 Hiff); exact Hin]].
  - contradiction.
Qed.

(* Symmetrically for the elimination site. *)
Lemma interaction_sound_elim U_i c_i l_i U_e c_e l_e :
  interaction_sound U_i (c_i, l_i) U_e (c_e, l_e) ->
  ((c_e, l_e) \in U_e) ->
  c_i = c_e /\ (U_i <--> U_e) /\ ((c_i, l_i) \in U_i).
Proof.
  intros Hsnd Hin.
  destruct (interaction_sound_inv _ _ _ _ _ _ Hsnd)
    as [[Heq [Hset Hiff]] | [_ [_ [_ [_ Hcl_e_U_e]]]]].
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
    internals_monochromatic U c ->
    cbstep_fuel U c ρ e 0 COOT (Empty_set _)

| CbstepF_Step :
  forall {I e i r},
    internals_monochromatic U c ->
    cbstep U c ρ e i r I ->
    cbstep_fuel U c ρ e (S i) r I.

Hint Constructors cbstep : core.
Hint Constructors cbstep_fuel : core.

Scheme cbstep_ind' := Minimality for cbstep Sort Prop
with cbstep_fuel_ind' := Minimality for cbstep_fuel Sort Prop.

(* Color Context *)
(* Assigns to each color the internal set of the compilation unit wearing it.
   This is the *global* counterpart of the "unique colored context" condition
   built into `interaction_sound`: there, two interacting labels of the same
   color are forced to agree on their internal set, but only where they
   actually interact.  `color_context` forces every occurrence of a color to agree. *)
Definition color_context := color -> internals.

(* Each unit's internal set only mentions that unit's own color. *)
Definition color_context_monochromatic (Θ : color_context) : Prop :=
  forall c, internals_monochromatic (Θ c) c.

(* A label is in `Θ c0` only if `c0` is its own color. *)
Lemma color_context_monochromatic_In {Θ c0 c l} :
  color_context_monochromatic Θ ->
  ((c, l) \in Θ c0) ->
  c0 = c.
Proof.
  unfold color_context_monochromatic, internals_monochromatic.
  intros HΘ Hin.
  symmetry; exact (HΘ c0 (c, l) Hin).
Qed.

(* Unique Color Context / Well-formedness *)
(* Every tag occurring in a value, or in an environment, assigns to its color
   the internal set that `Θ` prescribes for it. *)
Inductive unique_context (Θ : color_context) : clval -> Prop :=
| UC_TAG :
  forall U c l v,
    U <--> Θ c ->
    unique_context' Θ v ->
    unique_context Θ (CTag U c l v)

with unique_context' (Θ : color_context) : cval -> Prop :=
| UC_CVfun :
  forall f ρ xs e,
    unique_cenv Θ ρ ->
    unique_context' Θ (CVfun f ρ xs e)

| UC_CVconstr_nil :
  forall t,
    unique_context' Θ (CVconstr t [])

| UC_CVconstr :
  forall t v vs,
    unique_context Θ v ->
    unique_context' Θ (CVconstr t vs) ->
    unique_context' Θ (CVconstr t (v :: vs))

with unique_cenv (Θ : color_context) : cenv -> Prop :=
| UC_cenv :
  forall ρ,
    (forall x v, ρ ! x = Some v -> unique_context Θ v) ->
    unique_cenv Θ ρ.

Hint Constructors unique_context : core.
Hint Constructors unique_context' : core.
Hint Constructors unique_cenv : core.

Scheme unique_context_mut := Induction for unique_context Sort Prop
with unique_context'_mut := Induction for unique_context' Sort Prop
with unique_cenv_mut := Induction for unique_cenv Sort Prop.

(* Inversion *)
Lemma unique_context_CTag_inv {Θ U c l v} :
  unique_context Θ (CTag U c l v) ->
  (U <--> Θ c) /\ unique_context' Θ v.
Proof. intros Huc; inv Huc; split; assumption. Qed.

Lemma unique_context_CVfun_inv {Θ f ρ xs e} :
  unique_context' Θ (CVfun f ρ xs e) ->
  unique_cenv Θ ρ.
Proof. intros Huc; inv Huc; assumption. Qed.

(* `unique_cenv` is preserved by the environment operations of the semantics *)
Lemma unique_cenv_get {Θ ρ} :
  unique_cenv Θ ρ ->
  forall x v,
    ρ ! x = Some v ->
    unique_context Θ v.
Proof. fcrush. Qed.

Lemma unique_cenv_get_list {Θ ρ} :
  unique_cenv Θ ρ ->
  forall xs vs,
    get_list xs ρ = Some vs ->
    Forall (unique_context Θ) vs.
Proof.
  intros Henv xs.
  induction xs as [| x xs IHxs]; simpl; intros vs Hget; fcrush.
Qed.

Lemma unique_cenv_set {Θ ρ} x v :
  unique_cenv Θ ρ ->
  unique_context Θ v ->
  unique_cenv Θ (M.set x v ρ).
Proof.
  intros Henv Hv.
  inv Henv.
  constructor; intros y w Hget.
  destruct (M.elt_eq x y); subst.
  - rewrite M.gss in *; fcrush.
  - rewrite M.gso in *; fcrush.
Qed.

Lemma unique_cenv_set_lists {Θ} :
  forall ρ,
    unique_cenv Θ ρ ->
    forall vs xs ρ',
      Forall (unique_context Θ) vs ->
      set_lists xs vs ρ = Some ρ' ->
      unique_cenv Θ ρ'.
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
    | [Hv : unique_context Θ v, Hvs' : Forall (unique_context Θ) vs |- _] =>
        exact (unique_cenv_set x v (IHvs xs ρ'' Hvs' Heqρ'') Hv)
    end.
Qed.

(* Each interaction recorded by the checking semantics respects *every* unit's
   internal set.  The local `interaction_sound` side condition at each call
   site suffices, once the color context is globally consistent. *)
Lemma cbstep_respect Θ :
  color_context_monochromatic Θ ->
  forall U c ρ e i r I,
    cbstep U c ρ e i r I ->
    U <--> Θ c ->
    unique_cenv Θ ρ ->
    forall c0, interactions_respect (Θ c0) I.
Proof.
  intros HΘ U c ρ e i r I Hstep.
  induction Hstep as
    [ U c ρ x v Hget
    | U c ρ I f l xs e k i r IHfuel
    | U c ρ I' U' f f' c' l l' xs ρ' xs' e vs ρ'' i r
        Hget Hgetl Hsetl IHfuel Hsnd
    | U c ρ e Hmono
    | U c ρ I e i r Hmono IHstep ]
    using cbstep_ind'
    with (P := fun U c ρ e i r I =>
                 U <--> Θ c ->
                 unique_cenv Θ ρ ->
                 forall c0, interactions_respect (Θ c0) I)
         (P0 := fun U c ρ e i r I =>
                  U <--> Θ c ->
                  unique_cenv Θ ρ ->
                  forall c0, interactions_respect (Θ c0) I).

  - (* Cbstep_ret: nothing is recorded *)
    intros HU Hρ c0.
    apply interactions_respect_empty.

  - (* Cbstep_fun: the new binding agrees with Θ, so the IH applies *)
    intros HU Hρ c0.
    pose proof (unique_cenv_set f (CTag U c l (CVfun f ρ xs e)) Hρ
                  (UC_TAG Θ U c l (CVfun f ρ xs e) HU
                     (UC_CVfun Θ f ρ xs e Hρ))) as Hρf.
    exact (IHHstep HU Hρf c0).

  - (* Cbstep_app *)
    intros HU Hρ c0.
    (* the callee's tag agrees with Θ, and so does its environment *)
    pose proof (unique_cenv_get Hρ f _ Hget) as Hclo.
    destruct (unique_context_CTag_inv Hclo) as [HU' Hfun].
    pose proof (unique_context_CVfun_inv Hfun) as Hρ'.
    pose proof (unique_cenv_get_list Hρ xs vs Hgetl) as Hvs.
    pose proof (unique_cenv_set f' (CTag U' c' l' (CVfun f' ρ' xs' e)) Hρ' Hclo)
      as Hρ'f.
    pose proof (unique_cenv_set_lists _ Hρ'f vs xs' ρ'' Hvs Hsetl) as Hρ''.
    pose proof (Hsnd HU' Hρ'') as HI'.
    apply interactions_respect_add; [| exact (HI' c0)].
    destruct (interaction_sound_inv _ _ _ _ _ _ H)
      as [[Heqc [Hsets Hiff]] | [Hneqc [Hn_i_i [Hn_i_e [Hn_e_i Hn_e_e]]]]].
    + (* internal interaction: both endpoints live in the one set for c *)
      subst c'.
      split; intros Hmem.
      * pose proof (color_context_monochromatic_In HΘ Hmem) as Heq0; subst c0.
        apply (proj1 HU); apply (proj1 Hiff); apply (proj2 HU'); exact Hmem.
      * pose proof (color_context_monochromatic_In HΘ Hmem) as Heq0; subst c0.
        apply (proj1 HU'); apply (proj2 Hiff); apply (proj2 HU); exact Hmem.
    + (* foreign interaction: neither endpoint is in any unit's set *)
      split; intros Hmem; exfalso.
      * pose proof (color_context_monochromatic_In HΘ Hmem) as Heq0; subst c0.
        apply Hn_i_i; apply (proj2 HU'); exact Hmem.
      * pose proof (color_context_monochromatic_In HΘ Hmem) as Heq0; subst c0.
        apply Hn_e_e; apply (proj2 HU); exact Hmem.

  - (* CbstepF_OOT: nothing is recorded *)
    intros HU Hρ c0.
    apply interactions_respect_empty.

  - (* CbstepF_Step *)
    intros HU Hρ c0.
    exact (IHIHstep HU Hρ c0).
Qed.

Lemma cbstep_fuel_respect Θ :
  color_context_monochromatic Θ ->
  forall U c ρ e i r I,
    cbstep_fuel U c ρ e i r I ->
    U <--> Θ c ->
    unique_cenv Θ ρ ->
    forall c0, interactions_respect (Θ c0) I.
Proof.
  intros HΘ U c ρ e i r I Hstep HU Hρ c0.
  inv Hstep.
  - apply interactions_respect_empty.
  - match goal with
    | [Hs : cbstep _ _ _ _ _ _ _ |- _] =>
        exact (cbstep_respect Θ HΘ _ _ _ _ _ _ _ Hs HU Hρ c0)
    end.
Qed.

Lemma cbstep_closed Θ U c ρ e i r I :
  color_context_monochromatic Θ ->
  U <--> Θ c ->
  unique_cenv Θ ρ ->
  cbstep U c ρ e i r I ->
  internals_closed U I.
Proof.
  intros HΘ HU Hρ Hstep.
  apply interactions_respect_closed.
  apply (interactions_respect_Same_set U (Θ c) I HU).
  exact (cbstep_respect Θ HΘ U c ρ e i r I Hstep HU Hρ c).
Qed.

Lemma cbstep_fuel_closed Θ U c ρ e i r I :
  color_context_monochromatic Θ ->
  U <--> Θ c ->
  unique_cenv Θ ρ ->
  cbstep_fuel U c ρ e i r I ->
  internals_closed U I.
Proof.
  intros HΘ HU Hρ Hstep.
  apply interactions_respect_closed.
  apply (interactions_respect_Same_set U (Θ c) I HU).
  exact (cbstep_fuel_respect Θ HΘ U c ρ e i r I Hstep HU Hρ c).
Qed.

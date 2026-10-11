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

(* Color Context *)
(* Assigns to each color the internal set of the compilation unit wearing it.
   This is the *global* counterpart of the "unique colored context" condition
   built into `interaction_sound`: there, two interacting labels of the same
   color are forced to agree on their internal set, but only where they
   actually interact.  `internals_context` forces every occurrence of a color to agree. *)
Definition internals_context := color -> internals.

(* Unique Color Context / Well-formedness *)
(* Every tag occurring in a value, or in an environment, assigns to its color
   the internal set that `Θ` prescribes for it. *)
Inductive unique_context (Θ : internals_context) : clval -> Prop :=
| UC_TAG :
  forall U c l v,
    U <--> Θ c ->
    unique_context' Θ v ->
    unique_context Θ (CTag U c l v)

with unique_context' (Θ : internals_context) : cval -> Prop :=
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

with unique_cenv (Θ : internals_context) : cenv -> Prop :=
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

(* Interaction Closure Property *)
(* Each interaction recorded by the checking semantics respects *every* unit's
   internal set.  The local `interaction_sound` side condition at each call
   site suffices, once the color context is globally consistent. *)
Lemma cbstep_respect Θ :
  forall U c ρ e i r I,
    cbstep U c ρ e i r I ->
    U <--> Θ c ->
    unique_cenv Θ ρ ->
    forall c0, interactions_respect (Θ c0) c0 I.
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
                 U <--> Θ c ->
                 unique_cenv Θ ρ ->
                 forall c0, interactions_respect (Θ c0) c0 I)
         (P0 := fun U c ρ e i r I =>
                  U <--> Θ c ->
                  unique_cenv Θ ρ ->
                  forall c0, interactions_respect (Θ c0) c0 I).

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
    exact (IHIHstep HU Hρ c0).
Qed.

Lemma cbstep_fuel_respect Θ :
  forall U c ρ e i r I,
    cbstep_fuel U c ρ e i r I ->
    U <--> Θ c ->
    unique_cenv Θ ρ ->
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
  unique_cenv Θ ρ ->
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
  unique_cenv Θ ρ ->
  cbstep_fuel U c ρ e i r I ->
  internals_closed U c I.
Proof.
  intros HU Hρ Hstep.
  apply interactions_respect_closed.
  apply (interactions_respect_Same_set U (Θ c) c I HU).
  exact (cbstep_fuel_respect Θ U c ρ e i r I Hstep HU Hρ c).
Qed.

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

Lemma coloring_monotone {c1 ce c2 cce} :
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
      pose proof (coloring_monotone Hc2) as Hm; lia.
    + match goal with
      | [Hu : has_unit cce2 c0 U0 |- _] => destruct (IH2 c0 U0 Hu) as [Hlo Hhi]
      end.
      pose proof (coloring_monotone Hc1) as Hm; lia.
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
Definition ctx_of (cce : ccexp) : internals_context :=
  fun c => fun l => exists U, has_unit cce c U /\ (l \in U).

(* `Θ` agrees with the coloring of `cce`. *)
Definition internals_context_of (Θ : internals_context) (cce : ccexp) : Prop :=
  forall c U, has_unit cce c U -> U <--> Θ c.

Lemma ctx_of_correct {c1 ce c2 cce} :
  coloring c1 ce c2 cce ->
  internals_context_of (ctx_of cce) cce.
Proof.
  intros Hcol c U Hunit.
  unfold ctx_of, Ensembles.In.
  split; intros l Hl.
  - exists U; split; [exact Hunit | exact Hl].
  - destruct Hl as [U' [Hunit' Hl']].
    rewrite <- (coloring_unique Hcol c U' U Hunit' Hunit); exact Hl'.
Qed.

(* Top-level Checking Semantics for the *Colored* Top-level Expression *)
(* The colors are already in the tree, so the top-level semantics does not
   mention `Θ` at all: it just runs each unit at the color preprocessing gave
   it, and unions the interactions the units record.  `Θ` reappears only in the theorems,
   through `internals_context_of`. *)
Inductive cbstep_top (ρ : cenv) : ccexp -> fuel -> cres -> interactions -> Prop :=
| CbstepT_link_Res :
  forall {x cce1 cce2 i1 i2 v r I1 I2},
    cbstep_top_fuel ρ cce1 i1 (CRes v) I1 ->
    cbstep_top_fuel (M.set x v ρ) cce2 i2 r I2 ->
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

(* TODO: the glue that carries `unique_cenv` across a link.  `CbstepT_link_Res`
   binds the result of one unit into the next unit's environment, so the
   top-level theorem needs the per-unit result to agree with Θ:

     Lemma cbstep_unique_res Θ U c ρ e i v I :
       U <--> Θ c ->
       unique_cenv Θ ρ ->
       cbstep U c ρ e i (CRes v) I ->
       unique_context Θ v.

   It is the analogue of `cbstep_wf_res`, by `cbstep_ind'`.  With it, the
   top-level statement follows by induction on `cbstep_top_ind'`, using
   `cbstep_fuel_respect` at each unit and `interactions_respect_union` at each
   link:

     Theorem cbstep_top_closed Θ ρ cce i r I :
       internals_context_of Θ cce ->
       unique_cenv Θ ρ ->
       cbstep_top ρ cce i r I ->
       forall c U, has_unit cce c U -> internals_closed U c I. *)

(* Bipartite Interaction *)
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

(* TODO: the remaining, purely syntactic bridge.  For a uniquely labeled unit
   `e`, taking Λ c := intro_label e discharges `labels_separated Λ c e`:
     Lemma unique_label_separated e :
       unique_label e ->
       forall l, (l \in intro_label e) -> ~ (l \in elim_label e).
   It follows from `Unique_fun` (an `Efun` label occurs in neither subtree) and
   the two `_has_label` subset lemmas above, by `unique_label_mut`. *)

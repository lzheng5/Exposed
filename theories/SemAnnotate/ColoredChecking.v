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

(* Colored Label Pair Sets *)
(* Each pair has the format (l_intro, l_elim). *)
Definition clabel_pairs := Ensemble (clabel * clabel).

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

(* Colored Checking Semantics *)
(* `L` is the colored label set produced by running the entire linked labeled program,
   so `L` contains all the information we need to specify what happens within the current program context. *)
Inductive cbstep (L : clabel_pairs) (c : color) (ρ : cenv) : exp -> fuel -> cres -> Prop :=
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

with cbstep_fuel (L : clabel_pairs) (c : color) (ρ : cenv) : exp -> fuel -> cres -> Prop :=
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

(* Value Refinement *)
Inductive refine_val : wval -> clval -> Prop :=
| Refine_wval :
  forall l c v v',
    refine_val' v v' ->
    refine_val (Tag l v) (CTag c l v')

with refine_val' : val -> cval -> Prop :=
| Refine_fun :
  forall Γ f ρ ρ' xs e,
    (occurs_free e) \subset (FromList xs :|: (f |: Γ)) ->
    refine_env Γ ρ ρ' ->
    refine_val' (Vfun f ρ xs e) (CVfun f ρ' xs e)

| Refine_constr_nil :
  forall c,
    refine_val' (Vconstr c []) (CVconstr c [])

| Refine_constr :
  forall c v vs v' vs',
    refine_val v v' ->
    refine_val' (Vconstr c vs) (CVconstr c vs') ->
    refine_val' (Vconstr c (v :: vs)) (CVconstr c (v' :: vs'))

with refine_env : vars -> env -> cenv -> Prop :=
| Refine_env :
  forall Γ ρ ρ',
    (forall x,
        (x \in Γ) ->
        exists v1 v2,
          M.get x ρ = Some v1 /\
          M.get x ρ' = Some v2 /\
          refine_val v1 v2) ->
    refine_env Γ ρ ρ'.

Hint Constructors refine_val : core.
Hint Constructors refine_val' : core.
Hint Constructors refine_env : core.

Scheme refine_val_mut := Induction for refine_val Sort Prop
with refine_val'_mut := Induction for refine_val' Sort Prop
with refine_env_mut := Induction for refine_env Sort Prop.

Inductive refine_res : res -> cres -> Prop :=
| Refine_COOT :
  refine_res OOT COOT

| Refine_CRes :
  forall v v',
    refine_val v v' ->
    refine_res (Res v) (CRes v').

Hint Constructors refine_res : core.

(* Helper lemmas on refine_env / refine_val *)
Lemma refine_env_get x v {Γ ρ1 ρ2} :
  refine_env Γ ρ1 ρ2 ->
  x \in Γ ->
  ρ1 ! x = Some v ->
  exists v', ρ2 ! x = Some v' /\ refine_val v v'.
Proof.
  intros Henv Hget Hr1. inv Henv.
  edestruct H as [v1 [v2 [Heqv1 [Heqv2 Href]]]]; eauto; invc; eauto.
Qed.

Lemma refine_env_subset Γ1 {Γ2 ρ1 ρ2} :
  refine_env Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  refine_env Γ2 ρ1 ρ2.
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  constructor; intros.
  inv H; fcrush.
Qed.

Lemma refine_env_get_list xs vs {Γ ρ1 ρ2} :
  refine_env Γ ρ1 ρ2 ->
  FromList xs \subset Γ ->
  get_list xs ρ1 = Some vs ->
  exists vs', get_list xs ρ2 = Some vs' /\ Forall2 refine_val vs vs'.
Proof.
  intros Henv. revert vs.
  induction xs as [|x xs IH]; intros vs HS Hget; simpl in *.
  - inv Hget. exists []; split; auto.
  - destruct (ρ1 ! x) as [v|] eqn:Hx; [|discriminate].
    destruct (get_list xs ρ1) as [vs0|] eqn:Hxs; [|discriminate].
    inv Hget.
    edestruct (refine_env_get x v Henv) as [v' [Hv' Hrv]]; eauto.
    + unfold Ensembles.Included, Ensembles.In in *.
      fcrush.
    + edestruct (IH vs0) as [vs' [Hvs' Hrvs]]; eauto.
      unfold Ensembles.Included, Ensembles.In in *.
      fcrush.
      rewrite Hv', Hvs'. exists (v' :: vs'); split; auto.
Qed.

Lemma refine_env_set x v v' {Γ ρ1 ρ2} :
  refine_env Γ ρ1 ρ2 ->
  refine_val v v' ->
  refine_env (x |: Γ) (M.set x v ρ1) (M.set x v' ρ2).
Proof.
  intros Henv Hrv. constructor. intros y Hy.
  destruct (M.elt_eq x y) as [<-|Hne].
  - repeat (rewrite M.gss in *); invc.
    fcrush.
  - repeat (rewrite M.gso in * by auto).
    inv Henv.
    edestruct H as [w' [Hw' Hrw]]; eauto.
    unfold Ensembles.Included, Ensembles.In in *.
    fcrush.
Qed.

Lemma refine_env_set_lists xs vs vs' {Γ ρ1 ρ2 ρ1' ρ2'} :
  Forall2 refine_val vs vs' ->
  refine_env Γ ρ1 ρ2 ->
  set_lists xs vs ρ1 = Some ρ1' ->
  set_lists xs vs' ρ2 = Some ρ2' ->
  refine_env (FromList xs :|: Γ) ρ1' ρ2'.
Proof.
  intros Hf2. revert xs ρ1 ρ2 ρ1' ρ2'.
  induction Hf2 as [|v v' vs_rest vs_rest' Hrv _ IH];
    intros xs ρ1 ρ2 ρ1' ρ2' Henv Hset1 Hset2.
  - destruct xs as [|x xs_rest]; simpl in *.
    + inv Hset1; inv Hset2; auto.
      eapply refine_env_subset; eauto.
      rewrite FromList_nil.
      rewrite Union_Empty_set_neut_l.
      fcrush.
    + discriminate.
  - destruct xs as [|x xs_rest]; simpl in *; [discriminate|].
    destruct (set_lists xs_rest vs_rest ρ1) as [ρ3|] eqn:H3; [|discriminate].
    destruct (set_lists xs_rest vs_rest' ρ2) as [ρ4|] eqn:H4; [|discriminate].
    inv Hset1; inv Hset2.
    eapply (refine_env_subset (x |: (FromList xs_rest :|: Γ))).
    + eapply refine_env_set; eauto.
    + rewrite FromList_cons.
      rewrite <- Union_assoc.
      apply Included_refl.
Qed.

Lemma refine_val_Vfun_inv {l f ρ xs e v''} :
  refine_val (Tag l (Vfun f ρ xs e)) v'' ->
  exists c ρ' Γ,
    v'' = CTag c l (CVfun f ρ' xs e) /\
    occurs_free e \subset (FromList xs :|: (f |: Γ)) /\
    refine_env Γ ρ ρ'.
Proof.
  intros H.
  inv H.
  match goal with [Hv : refine_val' _ _ |- _] => inv Hv end.
  do 3 eexists. eauto.
Qed.

Lemma refine_val'_Vconstr_inv {t vs v''} :
  refine_val' (Vconstr t vs) v'' ->
  exists vs', v'' = CVconstr t vs' /\ Forall2 refine_val vs vs'.
Proof.
  intros H. remember (Vconstr t vs) as v0 eqn:Heq.
  revert t vs Heq.
  induction H; intros t0 vs0 Heq; inv Heq.
  - exists []; split; auto.
  - destruct (IHrefine_val' t0 vs eq_refl) as [vs1 [Heq Hr]].
    inv Heq. exists (v' :: vs1); split; auto.
Qed.

Lemma refine_val_Vconstr_inv {l t vs v''} :
  refine_val (Tag l (Vconstr t vs)) v'' ->
  exists c vs', v'' = CTag c l (CVconstr t vs') /\ Forall2 refine_val vs vs'.
Proof.
  intros H. inv H. apply refine_val'_Vconstr_inv in H3 as [vs' [-> Hr]]; eauto.
Qed.

Lemma refine_val'_Vconstr {t vs vs'} :
  Forall2 refine_val vs vs' ->
  refine_val' (Vconstr t vs) (CVconstr t vs').
Proof. intros Hr. induction Hr; auto. Qed.

Lemma refine_val_Vconstr {l c t vs vs'} :
  Forall2 refine_val vs vs' ->
  refine_val (Tag l (Vconstr t vs)) (CTag c l (CVconstr t vs')).
Proof. intros Hr. constructor. apply refine_val'_Vconstr; auto. Qed.

(* Correlation lemmas: bstep and cbstep that both terminate on the same expression agree on fuel and value. *)
Lemma bstep_cbstep_aux v1 v2 {L c ρ1 ρ2 e c1 r1 c2 r2} :
  bstep ρ1 e c1 r1 ->
  refine_env (occurs_free e) ρ1 ρ2 ->
  cbstep L c ρ2 e c2 r2 ->
  r1 = Res v1 ->
  r2 = CRes v2 ->
  c1 = c2 /\ refine_val v1 v2.
Proof.
  intros Hb.
  revert v1 v2 ρ2 L c c2 r2.
  induction Hb using bstep_ind'
    with (P := fun ρ1 e c1 r1 =>
                 forall v1 v2 ρ2 L c c2 r2,
                   refine_env (occurs_free e) ρ1 ρ2 ->
                   cbstep L c ρ2 e c2 r2 ->
                   r1 = Res v1 -> r2 = CRes v2 ->
                   c1 = c2 /\ refine_val v1 v2)
         (P0 := fun ρ1 e c1 r1 =>
                  forall v1 v2 ρ2 L c c2 r2,
                    refine_env (occurs_free e) ρ1 ρ2 ->
                    cbstep_fuel L c ρ2 e c2 r2 ->
                    r1 = Res v1 -> r2 = CRes v2 ->
                    c1 = c2 /\ refine_val v1 v2);
    intros v1 v2 ρ2 L0 c0 c2 r2 Henv Hc Heq1 Heq2; subst.

  - (* BStep_ret: FV(Eret x) = {x} *)
    inv Heq1. inv Hc.
    edestruct (refine_env_get x v1 Henv (ltac:(constructor)) H) as [v' [Hv' Hrv]].
    invc; fcrush.

  - (* BStep_fun: FV(Efun f l xs e_body k) *)
    inv Hc.
    assert (Href_clos : refine_val (Tag w (Vfun f ρ xs e))
                          (CTag c0 w (CVfun f ρ2 xs e))).
    { constructor. econstructor.
      - eapply free_fun_e_inv. apply Included_refl.
      - exact Henv. }
    eapply IHHb.
    + (* FV(k) ⊆ f |: FV(Efun) via free_fun_k_subset; refine_env_set + subset *)
      eapply refine_env_subset.
      * eapply refine_env_set; eauto.
      * apply free_fun_k_subset.
    + eauto. + eauto. + eauto.

  - (* BStep_app: FV(Eapp f l xs) = {f} ∪ xs *)
    inv Hc.
    edestruct (refine_env_get f (Tag w' (Vfun f' ρ' xs' e)) Henv (ltac:(constructor)) H) as [vf [Hvf Hrf]].
    invc.
    destruct (refine_val_Vfun_inv Hrf) as [c'' [ρ_2' [Γ_c [Heq [HFVe Hre]]]]].
    inv Heq.
    edestruct (refine_env_get_list xs _ Henv
                 (ltac:(unfold Ensembles.Included, Ensembles.In; intros z Hz; constructor; auto))
                 H0) as [vs2 [Hvs2 Hrvs]].
    invc.
    assert (Href_f : refine_val (Tag w' (Vfun f' ρ' xs' e))
                       (CTag c'' w' (CVfun f' ρ_2' xs' e))).
    { constructor. econstructor; eauto. }
    assert (Hrenv : refine_env (f' |: Γ_c)
                      (M.set f' (Tag w' (Vfun f' ρ' xs' e)) ρ')
                      (M.set f' (CTag c'' w' (CVfun f' ρ_2' xs' e)) ρ_2')).
    { apply refine_env_set; eauto. }
    pose proof (refine_env_set_lists xs' vs vs2 Hrvs Hrenv H1 H8) as Hre''.
    eapply IHHb; eauto.
    eapply refine_env_subset; eauto.

  - (* BStep_letapp_Res *)
    inv Hc.
    + (* Cbstep_letapp_Res *)
      edestruct (refine_env_get f (Tag w' (Vfun f' ρ' xs' e)) Henv (ltac:(apply Free_letapp2)) H) as [vf [Hvf Hrf]].
      invc.
      destruct (refine_val_Vfun_inv Hrf) as [c'' [ρ_2' [Γ_c [Heq [HFVe Hre]]]]].
      inv Heq.
      assert (Hxs_in : FromList xs \subset occurs_free (Eletapp x f w xs k))
        by (apply free_letapp_xs_subset).
      edestruct (refine_env_get_list xs _ Henv Hxs_in H0) as [vs2 [Hvs2 Hrvs]].
      invc.
      assert (Href_f : refine_val (Tag w' (Vfun f' ρ' xs' e))
                           (CTag c'' w' (CVfun f' ρ_2' xs' e))).
        { constructor. econstructor; eauto. }
        assert (Hrenv : refine_env (f' |: Γ_c)
                          (M.set f' (Tag w' (Vfun f' ρ' xs' e)) ρ')
                          (M.set f' (CTag c'' w' (CVfun f' ρ_2' xs' e)) ρ_2')).
        { apply refine_env_set; eauto. }
        pose proof (refine_env_set_lists xs' vs vs2 Hrvs Hrenv H1 H13) as Hre''.
        edestruct (IHHb v v0) as [Hc0 Hrv0]; eauto.
        { eapply refine_env_subset; eauto. }
        edestruct (IHHb0 v1 v2) as [Hc0' Hrv2]; eauto.
        { eapply refine_env_subset.
          - apply refine_env_set; eauto.
          - apply free_letapp_k_subset. }

  - fcrush.

  - (* BStep_constr: FV(Econstr x l t xs e) *)
    inv Hc.
    edestruct (refine_env_get_list xs _ Henv
                 (ltac:(unfold Ensembles.Included, Ensembles.In; intros z Hz; constructor; auto))
                 H) as [vs2 [Hvs2 Hrvs]].
    invc.
    eapply IHHb; eauto.
    eapply refine_env_subset.
    + apply refine_env_set; [exact Henv | apply refine_val_Vconstr; auto].
    + apply free_constr_k_subset.

  - (* BStep_proj: FV(Eproj x l i y e) *)
    inv Hc.
    edestruct (refine_env_get y (Tag w' (Vconstr t vs)) Henv (ltac:(constructor)) H) as [vc [Hvc Hrc]].
    invc.
      destruct (refine_val_Vconstr_inv Hrc) as [W'' [vs' [Heq Hrvs]]].
      inv Heq.
      edestruct (Forall2_nth_error H0 Hrvs) as [v' [Hnv' Hrv']]; eauto.
      unfold clval in *; invc.
      eapply IHHb; eauto.
      eapply refine_env_subset.
      * apply refine_env_set; [exact Henv | exact Hrv'].
      * apply free_proj_k_subset.

  - (* BStep_case *)
    inv Hc.
    edestruct (refine_env_get x (Tag w' (Vconstr t vs)) Henv (ltac:(constructor)) H) as [vc [Hvc Hrc]].
    invc.
      destruct (refine_val_Vconstr_inv Hrc) as [W'' [vs' [Heq _]]].
      inv Heq.
      destruct (find_tag_deterministic H0 H6); subst.
      eapply IHHb; eauto.
      eapply refine_env_subset; [exact Henv |].
      eapply free_case_e_inv; eauto. apply Included_refl.

  - discriminate.

  - inv Hc. edestruct IHHb as [Hc0 Hrv0]; eauto.
Qed.

Lemma bstep_cbstep_refine L c ρ1 ρ2 e c1 c2 v1 v2 :
  bstep ρ1 e c1 (Res v1) ->
  refine_env (occurs_free e) ρ1 ρ2 ->
  cbstep L c ρ2 e c2 (CRes v2) ->
  c1 = c2 /\ refine_val v1 v2.
Proof. intros; eapply bstep_cbstep_aux; eauto. Qed.

Lemma bstep_fuel_cbstep_fuel_refine L c ρ1 ρ2 e c1 c2 v1 v2 :
  bstep_fuel ρ1 e c1 (Res v1) ->
  refine_env (occurs_free e) ρ1 ρ2 ->
  cbstep_fuel L c ρ2 e c2 (CRes v2) ->
  c1 = c2 /\ refine_val v1 v2.
Proof.
  intros Hb Henv Hc. inv Hb. inv Hc.
  edestruct bstep_cbstep_refine as [Heq Hrv]; eauto.
Qed.

(* Well-formed Value and Environment *)
Inductive wf_cval : clval -> Prop :=
| WF_TAG :
  forall l c v,
    wf_cval' v ->
    wf_cval (CTag c l v)

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

Lemma wf_cval_CVconstr t l c vs :
  Forall wf_cval vs ->
  wf_cval (CTag c l (CVconstr t vs)).
Proof.
  intros H.
  induction H; simpl; auto; intros.
  fcrush.
Qed.

Lemma wf_cval_CVconstr_inv {t l c vs} :
  wf_cval (CTag c l (CVconstr t vs)) ->
  Forall wf_cval vs.
Proof.
  intros.
  remember (CTag c l (CVconstr t vs)) as v.
  revert t vs Heqv.
  induction H using wf_cval_mut with (P0 := fun v wf =>
                                              forall t vs,
                                                v = (CVconstr t vs) ->
                                                Forall wf_cval vs)
                                     (P1 := fun ρ wf => True);
    intros; eauto.
  - inv Heqv; invc.
    fcrush.
  - fcrush.
  - fcrush.
  - fcrush.
Qed.

Lemma cbstep_wf_res L c ρ e i r :
  wf_cenv ρ ->
  cbstep L c ρ e i r ->
  wf_cres r.
Proof.
  intros Hw H.
  induction H using cbstep_ind' with
    (P0 := fun c ρ e i r => wf_cenv ρ -> wf_cres r);
    intros; auto.

  - (* Cbstep_ret *)
    constructor.
    eapply wf_cenv_get; eauto.

  - (* Cbstep_fun *)
    apply IHcbstep.
    eapply wf_cenv_set; eauto.

  - (* Cbstep_app *)
    assert (Hwfclo : wf_cval (CTag c' l' (CVfun f' ρ' xs' e))).
    { eapply wf_cenv_get; eauto. }
    assert (Hwfρ' : wf_cenv ρ').
    { inv Hwfclo.
      match goal with [Hv : wf_cval' _ |- _] => inv Hv end; auto. }
    assert (Hwfvs : Forall wf_cval vs).
    { eapply wf_cenv_get_list. apply Hw. eassumption. }
    assert (Hwfρf : wf_cenv (M.set f' (CTag c' l' (CVfun f' ρ' xs' e)) ρ')).
    { eapply wf_cenv_set; eauto. }
    apply IHcbstep.
    eapply wf_cenv_set_lists
      with (ρ := M.set f' (CTag c' l' (CVfun f' ρ' xs' e)) ρ'); eauto.

  - (* Cbstep_letapp_Res *)
    assert (Hwfclo : wf_cval (CTag c' l' (CVfun f' ρ' xs' e))).
    { eapply wf_cenv_get; eauto. }
    assert (Hwfρ' : wf_cenv ρ').
    { inv Hwfclo.
      match goal with [Hv : wf_cval' _ |- _] => inv Hv end; auto. }
    assert (Hwfvs : Forall wf_cval vs).
    { eapply wf_cenv_get_list. apply Hw. eassumption. }
    assert (Hwfρf : wf_cenv (M.set f' (CTag c' l' (CVfun f' ρ' xs' e)) ρ')).
    { eapply wf_cenv_set; eauto. }
    assert (Hwfρ'' : wf_cenv ρ'').
    { eapply wf_cenv_set_lists
        with (ρ := M.set f' (CTag c' l' (CVfun f' ρ' xs' e)) ρ'); eauto. }
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
    assert (Hwfvc : wf_cval (CTag c' l' (CVconstr t vs))).
    { eapply wf_cenv_get; eauto. }
    eapply Forall_nth_error; eauto.
    eapply wf_cval_CVconstr_inv; eauto.
Qed.

Lemma cbstep_fuel_wf_res L c ρ e i r :
  wf_cenv ρ ->
  cbstep_fuel L c ρ e i r ->
  wf_cres r.
Proof.
  intros.
  inv H0; eauto using cbstep_wf_res.
Qed.

(* Valid `clabel_pairs` Specification *)
Definition cintro (L : clabel_pairs) (cl1 : clabel) : Prop :=
  exists cl2, ((cl1, cl2) \in L).

Definition celim (L : clabel_pairs) (cl1 : clabel) : Prop :=
  exists cl2, ((cl2, cl1) \in L).

Inductive valid_clabel_pairs (L : clabel_pairs) (c : color) (Γ : vars) : exp -> Prop :=
| Valid_Clabel_Pairs_ret :
  forall x,
    (x \in Γ) ->
    valid_clabel_pairs L c Γ (Eret x)

| Valid_Clabel_Pairs_fun :
  forall {f l xs e k},
    (* Note if the introduced value with (c, l) is never used, then it won't be in L. *)
    valid_clabel_pairs L c (FromList xs :|: (f |: Γ)) e ->
    valid_clabel_pairs L c (f |: Γ) k ->
    valid_clabel_pairs L c Γ (Efun f l xs e k)

| Valid_Clabel_Pairs_app :
  forall {f l xs},
    celim L (c, l) ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    valid_clabel_pairs L c Γ (Eapp f l xs)

| Valid_Clabel_Pairs_letapp :
  forall {x f l xs k},
    celim L (c, l) ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    valid_clabel_pairs L c (x |: Γ) k ->
    valid_clabel_pairs L c Γ (Eletapp x f l xs k)

| Valid_Clabel_Pairs_constr :
  forall {x l t xs k},
    (FromList xs \subset Γ) ->
    valid_clabel_pairs L c (x |: Γ) k ->
    valid_clabel_pairs L c Γ (Econstr x l t xs k)

| Valid_Clabel_Pairs_proj :
  forall {l x y k n},
    celim L (c, l) ->
    (y \in Γ) ->
    valid_clabel_pairs L c (x |: Γ) k ->
    valid_clabel_pairs L c Γ (Eproj x l n y k)

| Valid_Clabel_Pairs_case_nil :
  forall {l x},
    celim L (c, l) ->
    (x \in Γ) ->
    valid_clabel_pairs L c Γ (Ecase x l [])

| Valid_Clabel_Pairs_case_cons :
  forall {x l e t cl},
    celim L (c, l) ->
    (x \in Γ) ->
    valid_clabel_pairs L c Γ e ->
    valid_clabel_pairs L c Γ (Ecase x l cl) ->
    valid_clabel_pairs L c Γ (Ecase x l ((t, e) :: cl)).

Hint Constructors valid_clabel_pairs : core.

(* If the labels are unique across the compilation unit, then no
   colored label is both an intro site and an elim site, i.e. the two
   components of L are disjoint. In particular cl1 <> cl2 for every
   pair (cl1, cl2) \in L. *)
Definition clabel_pairs_diff (L : clabel_pairs) : Prop := forall cl, cintro L cl -> ~ celim L cl.

(* The converse direction is the same statement: both say ~ (cintro /\ celim). *)
Lemma clabel_pairs_diff_celim {L cl} :
  clabel_pairs_diff L ->
  celim L cl ->
  ~ cintro L cl.
Proof.
  intros Hdiff Helim Hintro.
  eapply Hdiff; eauto.
Qed.

Lemma clabel_pairs_diff_neq {L cl1 cl2} :
  clabel_pairs_diff L ->
  ((cl1, cl2) \in L) ->
  cl1 <> cl2.
Proof.
  intros Hdiff Hin Heq; subst.
  eapply Hdiff; eexists; eauto.
Qed.

(* Cross-semantics Logical Relations *)
Definition R' (P : nat -> wval -> clval -> Prop) (i : nat) (r1 : res) (r2 : cres) :=
  match r1, r2 with
  | OOT, COOT => True
  | Res v1, CRes v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> wval -> clval -> Prop) (L : clabel_pairs) (c : color) (i : nat) (ρ1 : env) (ρ2 : cenv) (e : exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    bstep_fuel ρ1 e j1 r1 ->
    exists j2 r2,
      cbstep_fuel L c ρ2 e j2 r2 /\
        R' P (i - j1) r1 r2.

(* L is sound for a particular program trace of e *)
Definition clabel_pairs_sound L c Γ ρ1 ρ2 e :=
  forall i r1,
    bstep_fuel ρ1 e i r1 ->
    refine_env Γ ρ1 ρ2 ->
    exists r2,
      cbstep_fuel L c ρ2 e i r2 /\
        refine_res r1 r2.

Fixpoint V (i : nat) (wv : wval) (cv : clval) {struct i} : Prop :=
  wf_val wv /\
  wf_cval cv /\
  refine_val wv cv /\
  match wv, cv with
  | TAG _ l1 v1, CTAG _ (c2, l2) v2 =>
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
                    forall L j vs1 vs2 ρ3 ρ4,
                      j <= i0 ->
                      Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                      set_lists xs1 vs1 (M.set f1 (Tag l1 (Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                      set_lists xs2 vs2 (M.set f2 (CTag c2 l2 (CVfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                      clabel_pairs_diff L ->
                      clabel_pairs_sound L c2 (occurs_free e1) ρ3 ρ4 e1 ->
                      E' V L c2 (i0 - (i0 - j)) ρ3 ρ4 e1
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

Lemma V_refine_val {i v1 v2} :
  V i v1 v2 ->
  refine_val v1 v2.
Proof. intros; destruct i; simpl in *; fcrush. Qed.

Lemma V_refine_val_Forall {i vs1 vs2} :
  Forall2 (V i) vs1 vs2 ->
  Forall2 refine_val vs1 vs2.
Proof.
  eapply Forall2_impl; eauto.
  eauto using V_refine_val.
Qed.

Lemma R_refine_res {i r1 r2} :
  R i r1 r2 ->
  refine_res r1 r2.
Proof.
  unfold R, R'.
  intros.
  destruct r1; destruct r2; try contradiction; eauto.
  eauto using V_refine_val.
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
  wf_cenv ρ2 /\
    refine_env Γ1 ρ1 ρ2 /\
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
  wf_cenv ρ2.
Proof. unfold G. fcrush. Qed.

Lemma G_refine_env {i Γ1 ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  refine_env Γ1 ρ1 ρ2.
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

  split.
  eapply refine_env_set; eauto.
  eapply G_refine_env; eauto.
  eapply V_refine_val; eauto.

  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss in *.
    fcrush.
  - repeat (rewrite M.gso in *; auto).
    fcrush.
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
    destruct H0 as [Hwf1 [Hwf2 [Href HV]]];
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
      eexists; repeat (split; eauto); intros.
      specialize (HV L j0 vs1 vs2 ρ3 ρ4).
      rewrite normalize_step in *; try lia.
      apply HV; eauto; lia.
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

Lemma E_mono {L c ρ1 ρ2 e} i j:
  E L c i ρ1 ρ2 e ->
  j <= i ->
  E L c j ρ1 ρ2 e.
Proof.
  unfold E, R, E', R'.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; eauto.
  apply R_mono with (i - j1); try lia; auto.
Qed.

Lemma G_mono {Γ1 ρ1 ρ2} i j:
  G i Γ1 ρ1 ρ2 ->
  j <= i ->
  G j Γ1 ρ1 ρ2.
Proof.
  unfold G.
  intros.
  destruct H as [Hwf1 [Hwf2 [Href HG]]].
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

Definition well_colored c Γ e :=
  forall L i ρ1 ρ2,
    clabel_pairs_diff L ->
    clabel_pairs_sound L c Γ ρ1 ρ2 e ->
    G i Γ ρ1 ρ2 ->
    E L c i ρ1 ρ2 e.

Lemma ret_compat c Γ x :
  (x \in Γ) ->
  well_colored c Γ (Eret x).
Proof.
  unfold well_colored, E, E', R, R', Ensembles.Included, Ensembles.In.
  intros; simpl.

  inv H4.
  - fcrush.
  - destruct r1.
    fcrush.
    inv H5.
    edestruct (G_get H2) as [v2 [Heqv2 HV]]; eauto.
    eexists; exists (CRes v2); split; eauto; simpl.
    eapply V_mono; eauto; lia.
Qed.

Lemma clabel_pairs_sound_fun_inv_k {L c Γ ρ1 ρ2 f l xs e k}:
  clabel_pairs_sound L c Γ ρ1 ρ2 (Efun f l xs e k) ->
  refine_env Γ ρ1 ρ2 ->
  clabel_pairs_sound L c (f |: Γ) (M.set f (Tag l (Vfun f ρ1 xs e)) ρ1) (M.set f (CTag c l (CVfun f ρ2 xs e)) ρ2) k.
Proof.
  unfold clabel_pairs_sound.
  intros.
  edestruct (H (S i) r1) as [r2 [Hcbstep Href]]; eauto.
  eexists; split; eauto.
  fcrush.
Qed.

Lemma clabel_pairs_sound_subset L c Γ1 Γ2 ρ1 ρ2 e :
  clabel_pairs_sound L c Γ1 ρ1 ρ2 e ->
  Γ1 \subset Γ2 ->
  clabel_pairs_sound L c Γ2 ρ1 ρ2 e.
Proof.
  unfold clabel_pairs_sound.
  intros.
  eapply H; eauto.
  eapply refine_env_subset; eauto.
Qed.

Lemma Vfun_V Γ f l c xs e  :
  occurs_free e \subset FromList xs :|: (f |: Γ) ->
  well_colored c (FromList xs :|: (f |: Γ)) e ->
  forall {i ρ1 ρ2},
    wf_val (Tag l (Vfun f ρ1 xs e)) ->
    wf_cval (CTag c l (CVfun f ρ2 xs e)) ->
    refine_val (Tag l (Vfun f ρ1 xs e)) (CTag c l (CVfun f ρ2 xs e)) ->
    G i Γ ρ1 ρ2 ->
    V i (Tag l (Vfun f ρ1 xs e)) (CTag c l (CVfun f ρ2 xs e)).
Proof.
  unfold well_colored.
  intros HS He i.
  induction i; simpl; intros; auto;
    repeat (split; auto);
    intros; (repeat split; auto).
  eapply (He L (i - (i - j)) ρ3 ρ4); eauto.

  eapply clabel_pairs_sound_subset; eauto.

  eapply G_subset; eauto.
  eapply G_set_lists; eauto.
  eapply G_set; eauto.
  + apply G_mono with (S i); eauto; lia.
  + apply V_mono with i; try lia.
    eapply IHi; eauto.
    apply G_mono with (S i); eauto; lia.
  + fcrush.
Qed.

Lemma fun_compat c Γ e k f l xs :
  occurs_free e \subset FromList xs :|: (f |: Γ) ->
  well_colored c (FromList xs :|: (f |: Γ)) e ->
  well_colored c (f |: Γ) k ->
  well_colored c Γ (Efun f l xs e k).
Proof.
  unfold well_colored, clabel_pairs_sound, E, E'.
  intross HS He Hk.

  inv H3.
  - fcrush.
  - destruct r1.
    fcrush.
    assert (Hwfρ1 : wf_env Γ ρ1) by eauto using G_wf_env_l.
    assert (Hwfρ2 : wf_cenv ρ2) by eauto using G_wf_cenv_r.
    assert (Hrefρ : refine_env Γ ρ1 ρ2) by eauto using G_refine_env.
    edestruct (H0 (S c0) (Res w)) as [cv [Hcbstep Href]]; eauto.

    inv Hcbstep; inv H4.
    inv H6; invc.
    edestruct (Hk L (i - 1) (M.set f (Tag l (Vfun f ρ1 xs e)) ρ1) (M.set f (CTag c l (CVfun f ρ2 xs e)) ρ2)) with (j1 := c0) (r1 := (Res w)) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + strivial use: @clabel_pairs_sound_fun_inv_k unfold: clabel_pairs_sound.
    + eapply G_subset.
      eapply G_set; eauto.
      eapply G_mono with i; eauto; lia.
      * eapply Vfun_V; eauto.
        apply G_mono with i; eauto; lia.
      * apply Included_refl.
    + exists (S j2), r2; split; auto.
      eapply R_mono; eauto; lia.
Qed.

Lemma app_compat Γ xs f l c :
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  well_colored c Γ (Eapp f l xs).
Proof.
  unfold well_colored, E, E'.
  intross Hf Hxs; simpl.

  inv H3.
  - fcrush.
  - destruct r1.
    fcrush.
    assert (Hrefρ : refine_env _ ρ1 ρ2) by eauto using G_refine_env.
    edestruct (H0 (S c0) (Res w)) as [cv [Hcbstep Href]]; eauto.
    inv Hcbstep; inv H4; inv Href.
    inv H6; invc.
    edestruct (G_get H1 f) as [fv2 [Heqfv2 HV]]; eauto.
    destruct i.
    inv H2.
    rename w into v.
    destruct fv2; simpl in HV; invc;
      destruct HV as [Hwf1 [Hwf2 [Hrefv [Heql [Heqf [Heqxs [Heqe HV]]]]]]]; subst; invc.

    edestruct (G_get_list H1 xs vs) as [vs2 [Heqvs2 Vvs]]; eauto; invc.

    destruct (set_lists_length3 (M.set f'0 (CTag c' l' (CVfun f'0 ρ'0 xs'0 e0)) ρ'0) xs'0 vs2) as [ρ4 Heqρ4].
    unfold clval in *.
    rewrite <- (set_lists_length_eq _ _ _ _ H14); auto.

    assert (HE : E L c' (i - (i - i)) ρ'' ρ4 e0).
    {
      eapply (HV _ i vs vs2); eauto.
      apply V_mono_Forall with (S i); auto; lia.

      unfold clabel_pairs_sound; intros.
      edestruct (H0 (S i0) r1) as [r2 [Hcbstep2 Hrefr2]]; eauto.
      inv Hrefr2.
      - inv Hcbstep2.
        inv H15.
        unfold clval in *.
        invc; eauto.
      - inv Hcbstep2.
        inv H16.
        unfold clval in *.
        invc; fcrush.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E, E' in HE.
    destruct (HE c0 (Res v)) as [j2 [r2 [He0 Rr]]]; try lia; auto.
    exists (S j2), r2; split; eauto.
Qed.

Lemma case_nil_compat Γ x l c :
  (x \in Γ) ->
  well_colored c Γ (Ecase x l []).
Proof.
  unfold well_colored, E, E'.
  intros Hx; intros.
  inv H3; fcrush.
Qed.

Lemma fundamental_property {c Γ e}:
  well_scoped Γ e ->
  well_colored c Γ e.
Proof.
  intros H.
  induction H; intros.
  - eapply ret_compat; eauto.
  - eapply fun_compat; eauto.
    eapply well_scoped_inv; eauto.
  - eapply app_compat; eauto.
  - admit.
  - admit.
  - admit.
  - eapply case_nil_compat; eauto.
  - admit.
Admitted.

(* Top Level *)

(* Top-level Compilation Unit & Linking *)
Inductive cexp : Type :=
| CEexp : exp -> cexp
| CElink : var -> cexp -> cexp -> cexp.

Hint Constructors cexp : core.

(* Linking *)
Definition clink x e1 e2 : cexp := CElink x e1 e2.

Inductive occurs_free_top : cexp -> vars :=
| Free_cexp :
  forall e x,
    occurs_free e x ->
    occurs_free_top (CEexp e) x

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

Lemma occurs_free_top_cexp e :
  (occurs_free_top (CEexp e)) <--> (occurs_free e).
Proof. split; unfold Ensembles.Included, Ensembles.In; fcrush. Qed.

(* Top-level Checking Semantics *)
Inductive cbstep_top (L : clabel_pairs) (c : color) (ρ : cenv) : cexp -> fuel -> cres -> Prop :=
| Cbstep_exp_top :
  forall {e i r},
    cbstep L c ρ e i r ->
    cbstep_top L c ρ (CEexp e) i r

| Cbstep_link_top_trivial :
  forall {x e k},
    cbstep_top L c ρ (CElink x e k) 0 COOT

| Cbstep_link_top_Res :
  forall {x e k i' i r v},
    cbstep_top_fuel L c ρ e i (CRes v) ->
    cbstep_top_fuel L (S c) (M.set x v ρ) k i' r ->
    cbstep_top L c ρ (CElink x e k) (S (i + i')) r

| Cbstep_link_top_OOT :
  forall {x e k i},
    cbstep_top_fuel L c ρ e i COOT ->
    cbstep_top L c ρ (CElink x e k) (S i) COOT

with cbstep_top_fuel (L : clabel_pairs) (c : color) (ρ : cenv) : cexp -> fuel -> cres -> Prop :=
| CbstepTF_OOT :
  forall {e},
    cbstep_top_fuel L c ρ e 0 COOT

| CbstepTF_Step :
  forall {e i r},
    cbstep_top L c ρ e i r ->
    cbstep_top_fuel L c ρ e (S i) r.

Hint Constructors cbstep_top : core.
Hint Constructors cbstep_top_fuel : core.

(* The step-index is aligned between the two semantics. *)
Lemma cbstep_fuel_cbstep_top_fuel L c ρ e j r:
  cbstep_fuel L c ρ e j r ->
  cbstep_top_fuel L c ρ (CEexp e) j r.
Proof. intros H; inv H; eauto. Qed.

Lemma cbstep_top_fuel_cbstep_fuel L c ρ e j r:
  cbstep_top_fuel L c ρ (CEexp e) j r ->
  cbstep_fuel L c ρ e j r.
Proof.
  intros H; inv H; eauto.
  inv H0.
  inv H1; eauto.
Qed.

Lemma cbstep_top_wf_res L c ρ e i r :
  wf_cenv ρ ->
  cbstep_top L c ρ e i r ->
  wf_cres r
with cbstep_top_fuel_wf_res L c ρ e i r :
  wf_cenv ρ ->
  cbstep_top_fuel L c ρ e i r ->
  wf_cres r.
Proof.
  - intros Hw H. inv H.
    + (* Cbstep_exp_top *)
      eapply cbstep_wf_res; eauto.
    + (* Cbstep_link_top_trivial *)
      constructor.
    + (* Cbstep_link_top_Res *)
      assert (Hwfv : wf_cres (CRes v))
        by (eapply cbstep_top_fuel_wf_res; eauto).
      inv Hwfv.
      assert (Hwfρx : wf_cenv (M.set x v ρ)) by (eapply wf_cenv_set; eauto).
      eapply cbstep_top_fuel_wf_res; eauto.
    + (* Cbstep_link_top_OOT *)
      constructor.
  - intros Hw H. inv H.
    + (* CbstepTF_OOT *)
      constructor.
    + (* CbstepTF_Step *)
      eapply cbstep_top_wf_res; eauto.
Qed.

(* Cross-language Logical Relations *)

Definition E_top' (P : nat -> wval -> clval -> Prop) (L : clabel_pairs) (c : color) (i : nat) (ρ1 : env) (e1 : exp) (ρ2 : cenv) (e2 : cexp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    bstep_fuel ρ1 e1 j1 r1 ->
    exists j2 r2,
      cbstep_top_fuel L c ρ2 e2 j2 r2 /\
      R' P (i - j1) r1 r2.

Definition E_top := E_top' V.

Lemma E_E_top L c i ρ1 ρ2 e :
  E L c i ρ1 ρ2 e ->
  E_top L c i ρ1 e ρ2 (CEexp e).
Proof.
  unfold E, E_top, E', E_top'.
  intros.
  edestruct H as [j2 [r2 [Hcbstep HR]]]; eauto.
  exists j2, r2; split; eauto.
  eapply cbstep_fuel_cbstep_top_fuel; eauto.
Qed.

Lemma E_top_E L c i ρ1 ρ2 e :
  E_top L c i ρ1 e ρ2 (CEexp e) ->
  E L c i ρ1 ρ2 e.
Proof.
  unfold E, E_top, E', E_top'.
  intros.
  edestruct H as [j2 [r2 [Hcbstep HR]]]; eauto.
  exists j2, r2; split; eauto.
  eapply cbstep_top_fuel_cbstep_fuel; eauto.
Qed.

Lemma E_top_mono {L c ρ1 ρ2 e1 e2} i j:
  E_top L c i ρ1 e1 ρ2 e2 ->
  j <= i ->
  E_top L c j ρ1 e1 ρ2 e2.
Proof.
  unfold E_top, E_top'.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; eauto.
  apply R_mono with (i - j1); try lia; auto.
Qed.

Definition G_top := G.

(* Soundness of Coloring *)
Definition trans_correct_top e c e' :=
  (occurs_free_top e') \subset (occurs_free e) /\
  forall L i ρ1 ρ2,
    clabel_pairs_diff L ->
    clabel_pairs_sound L c (occurs_free e) ρ1 ρ2 e ->
    G_top i (occurs_free e) ρ1 ρ2 ->
    E_top L c i ρ1 e ρ2 e'.

Lemma trans_correct_top_subset e1 c e2 :
  trans_correct_top e1 c e2 ->
  occurs_free_top e2 \subset occurs_free e1.
Proof. unfold trans_correct_top. fcrush. Qed.

Theorem top c etop:
  trans_correct_top etop c (CEexp etop).
Proof.
  unfold trans_correct_top.
  split; intros.
  eapply occurs_free_top_cexp; eauto.
  eapply E_E_top; eauto.
  eapply fundamental_property; eauto.
  eapply well_scoped_intro; eauto.
  eapply Included_refl.
Qed.

(* Soundness of Analysis *)
(* L is large enough to incorporate all program traces. *)
Definition clabel_pairs_analysis_sound L c Γ e :=
  forall i r1 ρ1 ρ2,
    bstep_fuel ρ1 e i r1 ->
    refine_env Γ ρ1 ρ2 ->
    exists r2,
      cbstep_fuel L c ρ2 e i r2 /\
      refine_res r1 r2.

Lemma clabel_pairs_analysis_sound_instantiate L c Γ ρ1 ρ2 e :
  clabel_pairs_analysis_sound L c Γ e ->
  clabel_pairs_sound L c Γ ρ1 ρ2 e.
Proof. unfold clabel_pairs_analysis_sound, clabel_pairs_sound; fcrush. Qed.

Definition analysis_correct_top L e c e' :=
  (occurs_free_top e') \subset (occurs_free e) /\
  clabel_pairs_diff L /\
  clabel_pairs_analysis_sound L c (occurs_free e) e /\
  forall i ρ1 ρ2,
    G_top i (occurs_free e) ρ1 ρ2 ->
    E_top L c i ρ1 e ρ2 e'.

Theorem analysis_top L c etop:
  clabel_pairs_diff L ->
  clabel_pairs_analysis_sound L c (occurs_free etop) etop ->
  analysis_correct_top L etop c (CEexp etop).
Proof.
  unfold analysis_correct_top.
  intros; repeat (split; eauto); intros.
  eapply occurs_free_top_cexp; eauto.
  eapply E_E_top; eauto.
  eapply fundamental_property; eauto.
  eapply well_scoped_intro; eauto.
  eapply Included_refl.
  eapply clabel_pairs_analysis_sound_instantiate; eauto.
Qed.

(* REVISIT: put cinteract into reachable? *)

(* Symmetric, undirected interaction between two colored labels in L. *)
Definition cinteract (L : clabel_pairs) (cl1 cl2 : clabel) : Prop :=
  ((cl1, cl2) \in L) \/ ((cl2, cl1) \in L).

(* Reachable label pairs *)
(* 1. `reachable L cl` is the set of colored labels connected to `cl` by a chain of
   interactions in L, in either direction (transitive closure of `cinteract`).

   2. Note this set is exclusive in that `cl` is not part of under `clabel_pairs_diff`. *)
Inductive reachable (L : clabel_pairs) (cl : clabel) : clabels :=
| Reachable_interact :
  forall cl',
    cinteract L cl cl' ->
    reachable L cl cl'

| Reachable_step :
  forall cl' cl'',
    reachable L cl cl' ->
    cinteract L cl' cl'' ->
    reachable L cl cl''.

Hint Constructors reachable : core.

(* Reachable labels of a given color *)
(* If we allow reflexivity, (c, l) \in reachable L (c, l) holds for every l,
   which would make reachable_labels L c the set of all labels regardless of L. *)
Definition reachable_labels (L : clabel_pairs) (c : color) : labels :=
  fun l => exists l' c', ((c', l) \in reachable L (c, l')).

(* Reachable colors of a given label *)
Definition reachable_colors (L : clabel_pairs) (l : label) : colors :=
  fun c => exists c' l', ((c, l') \in reachable L (c', l)).

(* `cl` has only internal interaction if the set of reachable colors is exactly the singleton set {c}. *)
Definition internal (L : clabel_pairs) (cl : clabel) : Prop :=
  match cl with
  | (c, l) => (reachable_colors L l) <--> [ set c ]
  end.

(* `cl` has external interaction if it is not internal *)
Definition external (L : clabel_pairs) (cl : clabel) : Prop :=
  ~ internal L cl.

(*

Definition web_map := M.t web.

(* Converting [clabel_pairs] to [web_map] *)

(* Labels of a given color appearing on either side of a pair in L. *)
Definition labels_of_color (L : clabel_pairs) (c : color) : labels :=
  fun l => exists cl, (((c, l), cl) \in L) \/ ((cl, (c, l)) \in L).


(* A blue label is tainted iff it can reach a red label through a chain of
   blue-blue interactions. The transitive closure is captured by the recursive
   `Tainted_blue` rule. *)
Inductive tainted (L : clabel_pairs) : label -> Prop :=
| Tainted_red :
    forall l r,
      cinteract L (Blue, l) (Red, r) ->
      tainted L l

| Tainted_blue :
    forall l l',
      cinteract L (Blue, l) (Blue, l') ->
      tainted L l' ->
      tainted L l.

Hint Constructors tainted : core.

(* Equivalence among non-tainted blue labels: the reflexive/symmetric/transitive
   closure of blue-blue interaction restricted to non-tainted labels.
   Symmetry of `BE_step` is inherited from `cinteract`. *)
Inductive blue_equiv (L : clabel_pairs) : label -> label -> Prop :=
| BE_refl :
    forall l,
      (l \in labels_of_color L Blue) ->
      ~ tainted L l ->
      blue_equiv L l l

| BE_step :
    forall l1 l2,
      cinteract L (Blue, l1) (Blue, l2) ->
      ~ tainted L l1 ->
      ~ tainted L l2 ->
      blue_equiv L l1 l2

| BE_trans :
    forall l1 l2 l3,
      blue_equiv L l1 l2 ->
      blue_equiv L l2 l3 ->
      blue_equiv L l1 l3.

Hint Constructors blue_equiv : core.

(* W is a valid web map for the colored label set L. *)
Inductive clabel_pairs_to_web_map (L : clabel_pairs) (W : web_map) : Prop :=
| LS_to_WM :
    (* (1) Totality: every blue label of L is mapped by W. *)
    (forall l,
        (l \in labels_of_color L Blue) ->
        exists w, W ! l = Some w) ->
    (* (2) Tainted blue labels map to exposed webs. *)
    (forall l w,
        tainted L l ->
        W ! l = Some w ->
        (w \in Exposed)) ->
    (* (3) Non-tainted blue labels map to non-exposed webs
       (these are the internal class representatives). *)
    (forall l w,
        (l \in labels_of_color L Blue) ->
        ~ tainted L l ->
        W ! l = Some w ->
        ~ (w \in Exposed)) ->
    (* (4) Equivalent non-tainted blue labels share the same web (the rep). *)
    (forall l1 l2 w1 w2,
        blue_equiv L l1 l2 ->
        W ! l1 = Some w1 ->
        W ! l2 = Some w2 ->
        w1 = w2) ->
    (* (5) Distinct equivalence classes get distinct reps: if two non-tainted
       blue labels share a web, they must be in the same class. *)
    (forall l1 l2 w,
        (l1 \in labels_of_color L Blue) ->
        (l2 \in labels_of_color L Blue) ->
        ~ tainted L l1 ->
        ~ tainted L l2 ->
        W ! l1 = Some w ->
        W ! l2 = Some w ->
        blue_equiv L l1 l2) ->
    clabel_pairs_to_web_map L W.

Hint Constructors clabel_pairs_to_web_map : core.
*)

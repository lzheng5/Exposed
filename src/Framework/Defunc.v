From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF Exposed.

(* Defunctionalization *)

(* Constructor Map *)
(* This map takes a data constructor tag and returns the corresponding call web id *)
Definition ctor_map := M.t web.

(* Web Map *)
(* This map takes an existing call web id and returns a constructor map that describes how to turn the call web into a data web and how to create the new call webs *)
Module LT <: Exposed.LTy. Definition t := ctor_map. End LT.
Module LM := Exposed.DefaultL LT.
Import LM.

Definition ctor_map_web_inv (C : ctor_map) :=
  forall c w,
    C ! c = Some w ->
    (~ w \in Exposed).

(* Specification *)
Definition tail_cases cases f' f w xs :=
  List.map (fun p : (ctor_tag * web) =>
              let (c, w') := p in
              (c, Eproj f' w 0 f (* project out the function to f' *)
                    (Eapp f' w' xs))) (* call f' *)
    cases.

Definition nontail_cases cases f' f w xs j x w' :=
  List.map (fun p : (ctor_tag * web) =>
              let (c, w'') := p in
              (c, Eproj f' w 0 f (* project out the function to f' *)
                    (Eletapp x f' w'' xs (* call f' and bind the result to x *)
                       (Eapp j w' [x])))) (* goto join point *)
    cases.

Inductive trans (Γ : Ensemble var) : exp -> exp -> Prop :=
| Trans_ret :
  forall {x},
    (x \in Γ) ->
    trans Γ (Eret x) (Eret x)

| Trans_fun :
  forall {f w xs e k C w' c e' k'},
    M.get w L = Some C ->
    ctor_map_web_inv C ->
    M.get c C = Some w' ->

    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->

    NoDup (f :: xs) ->
    Disjoint _ (FromList (f :: xs)) Γ ->

    (* turn the call web into data web *)
    (* use the new web w' for the function f *)
    (* make sure f is wrapped in a constructor in both the function body and the continuation *)
    trans Γ (Efun f w xs e k) (Efun f w' xs (Econstr f w c [f] e') (Econstr f w c [f] k'))

| Trans_fun_exposed :
  forall {f w xs e k e' k'},
    M.get w L = None ->
    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->
    trans Γ (Efun f w xs e k) (Efun f w xs e' k')

| Trans_app :
  forall {f f' w xs C},
    M.get w L = Some C ->
    ctor_map_web_inv C ->

    f' <> f ->
    (~ In f' xs) ->

    (f \in Γ) ->
    (FromList xs \subset Γ) ->

    trans Γ (Eapp f w xs) (Ecase f w (tail_cases (M.elements C) f' f w xs))

| Trans_app_exposed :
  forall {f w xs},
    M.get w L = None ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans Γ (Eapp f w xs) (Eapp f w xs)

| Trans_letapp :
  forall {x C f w w' xs k k' f' j},
    M.get w L = Some C ->
    ctor_map_web_inv C ->

    f' <> f ->
    (~ In f' xs) ->

    j <> x ->
    j <> f ->
    j <> f' ->
    (~ In j xs) ->
    (~ j \in (occurs_free k')) ->

    (~ w' \in Exposed) ->

    (f \in Γ) ->
    (FromList xs \subset Γ) ->

    trans (x |: Γ) k k' ->
    trans Γ (Eletapp x f w xs k) (Efun j w' [x] k' (* emit join point *)
                                    (Ecase f w
                                       (nontail_cases (M.elements C) f' f w xs j x w')))

| Trans_letapp_exposed :
  forall {x f w xs k k'},
    M.get w L = None ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (Eletapp x f w xs k) (Eletapp x f w xs k')

| Trans_constr :
  forall {x w c xs k k'},
    M.get w L = None ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (Econstr x w c xs k) (Econstr x w c xs k')

| Trans_proj :
  forall {x y w k k' n},
    M.get w L = None ->
    (y \in Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (Eproj x w n y k) (Eproj x w n y k')

| Trans_case_nil :
  forall {x w},
    (x \in Γ) ->
    trans Γ (Ecase x w []) (Ecase x w [])

| Trans_case_cons :
  forall {x w e e' t cl cl'},
    M.get w L = None ->
    (x \in Γ) ->
    trans Γ e e' ->
    trans Γ (Ecase x w cl) (Ecase x w cl') ->
    trans Γ (Ecase x w ((t, e) :: cl)) (Ecase x w ((t, e') :: cl')).

Hint Constructors trans : core.

Module VTransM <: Exposed.VTrans LM.

  Definition V_trans
    (V' : nat -> wval -> wval -> Prop)
    (E' : nat -> env -> exp -> env -> exp -> Prop)
    (i0 : nat) (C : ctor_map)
    (w1 : web) (v1 : val) (w2 : web) (v2 : val) :=
    w1 = w2 /\
    match v1, v2 with
    | Vfun f1 ρ1 xs1 e1, Vconstr c [TAG _ w' (Vfun f2 ρ2 xs2 e2)] =>
        length xs1 = length xs2 /\
        ctor_map_web_inv C /\
        C ! c = Some w' /\
        forall j vs1 vs2 ρ3 ρ4,
          j <= i0 ->
          Forall2 (V' j) vs1 vs2 ->
          set_lists xs1 vs1 (M.set f1 (Tag w1 (Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
          set_lists xs2 vs2 (M.set f2 (Tag w' (Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
          E' j ρ3 e1 ρ4 e2

    | _, _ => False
    end.

  Lemma V_trans_mono V E i j d w1 v1 w2 v2 :
    (forall k : nat,
        k < S i ->
        forall (j : nat) (v1 v2 : wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
    V_trans (fun i' => V (i - (i - i'))) (fun i' => E (i - (i - i'))) i d w1 v1 w2 v2 ->
    j <= i ->
    V_trans (fun j' => V (j - (j - j'))) (fun j' => E (j - (j - j'))) j d w1 v1 w2 v2.
  Proof.
    unfold V_trans.
    intros HI. intros.
    destruct v1; destruct v2; auto;
      simpl in *; try contradiction;
      rename l into xs1;
      rename l0 into xs2.
    destruct H as [Hw H]; subst; split; auto.
    destruct xs2; try contradiction.
    destruct t0.
    destruct v0; try contradiction.
    destruct xs2; try contradiction.
    destruct H as [Hlen [HCinv [HeqC HV]]].
    repeat (split; auto); intros.
    specialize (HV j0 vs1 vs2 ρ3 ρ4).
    rewrite normalize_step in *; try lia.
    eapply HV; eauto; try lia.
  Qed.

End VTransM.

Module EM := Exposed.Exposed LM VTransM.
Import EM.

(* Lemmas about Free Variables *)
Lemma free_defun_k_subset k f w w' xs c e :
  (occurs_free k) \subset (f |: occurs_free (Efun f w' xs (Econstr f w c [f] e) (Econstr f w c [f] k))).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (var_dec f x); subst.
  - apply Union_introl; auto.
  - apply Union_intror; auto.
Qed.

Lemma free_defun_e_subset e k xs f w w' c :
  occurs_free e \subset (FromList xs :|: (f |: occurs_free (Efun f w' xs (Econstr f w c [f] e) (Econstr f w c [f] k)))).
Proof.
  eapply Included_trans.
  apply (free_fun_e_subset k f w' e xs); auto.
  apply Included_Union_compat.
  apply Included_refl.
  apply Included_Union_compat.
  apply Included_refl.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  inv H; eauto.
Qed.

Lemma free_tail_cases_f cl f f' w xs:
  occurs_free (Ecase f w (tail_cases cl f' f w xs)) f.
Proof.
  unfold tail_cases.
  induction cl; simpl; auto.
Qed.

Lemma free_tail_cases_xs f f' w xs cl:
  (exists c w, In (c, w) cl) ->
  f <> f' ->
  ~ In f' xs ->
  FromList xs \subset occurs_free (Ecase f w (tail_cases cl f' f w xs)).
Proof.
  unfold Ensembles.Included, Ensembles.In, FromList, tail_cases.
  induction cl; simpl; intros.
  - destruct H as [c [w' H]].
    contradiction.
  - destruct a.
    eapply Free_case2; eauto.
    destruct (var_dec f x); subst; auto.
    constructor; auto.
    intros Hc; subst; contradiction.
Qed.

Lemma free_nontail_cases_xs f f' xs cl j w w' w'' k' x :
  (exists c w, In (c, w) cl) ->

  f' <> f ->
  (~ In f' xs) ->

  j <> x ->
  j <> f ->
  j <> f' ->
  (~ In j xs) ->

  FromList xs \subset (occurs_free
                         (Efun j w'' [x] k'
                            (Ecase f w (nontail_cases cl f' f w xs j x w')))).
Proof.
  unfold Ensembles.Included, Ensembles.In, FromList, nontail_cases.
  induction cl; simpl; intros.
  - destruct H as [_ [_ H]].
    contradiction.
  - destruct a.

    eapply Free_fun1; eauto.
    intros Hc; subst; contradiction.

    eapply Free_case2; eauto.
    destruct (var_dec f x); subst; auto.
    constructor; auto.
    intros Hc; subst; contradiction.

    constructor; auto.
    intros Hc; subst; contradiction.
Qed.

Lemma free_tail_cases_inv {f cl f' w xs x}:
  occurs_free (Ecase f w (tail_cases cl f' f w xs)) x ->
  (x = f \/ In x xs).
Proof.
  induction cl; simpl; intros.
  - inv H.
    left; auto.
  - destruct a.
    inv H; auto.
    inv H6.
    left; auto.
    inv H7; try contradiction.
    right; auto.
Qed.

Lemma free_nontail_cases_inv {j f f' w w' x k cl xs y} :
  occurs_free
    (Efun j w' [x] k
       (Ecase f w (nontail_cases cl f' f w xs j x w'))) y ->
  (y = f \/ In y xs \/ (x <> y /\ occurs_free k y)).
Proof.
  induction cl; simpl; intros.
  - inv H; auto.
    inv H7; auto.
    right; right.
    split; auto.
    intros Hc; subst.
    apply H7; apply in_eq.
  - inv H; auto.
    inv H7; auto.
    destruct a.
    inv H2.
    inv H4; auto.
    inv H8; try contradiction.
    + inv H9; try contradiction.
      inv H3; contradiction.
    + right; left; auto.
Qed.

(* Invariants about [trans] *)
Lemma trans_exp_inv {Γ e e'} :
  trans Γ e e' ->
  (occurs_free e') \subset (occurs_free e).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros H.
  induction H; intros; auto.
  - inv H6.
    + inv H14; eauto.
      inv H12; contradiction.
    + inv H15; eauto.
      inv H12; contradiction.
  - inv H2; eauto.
  - destruct (free_tail_cases_inv H5); subst; auto.
  - destruct (free_nontail_cases_inv H12); subst; auto.
    destruct H13; auto.
    destruct H13; auto.
  - inv H3; auto.
  - inv H2; auto.
  - inv H2; auto.
  - inv H3; auto.
Qed.

(* Environment Lemmas *)
Lemma G_set_lists_trans ρ1 {i Γ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall {xs vs1 vs2 v1 v2 v3 ρ3 ρ4 f},
    Forall2 (V i) vs1 vs2 ->
    wf_val v2 ->
    V i v1 v3 ->
    set_lists xs vs1 (M.set f v1 ρ1) = Some ρ3 ->
    set_lists xs vs2 (M.set f v2 ρ2) = Some ρ4 ->
    NoDup (f :: xs) ->
    Disjoint _ (FromList (f :: xs)) Γ1 ->
    G i (FromList xs :|: (f |: Γ1)) ρ3 (FromList xs :|: (f |: Γ2)) (M.set f v3 ρ4).
Proof.
  intros HG xs.
  induction xs; simpl; intros;
    destruct vs1; destruct vs2; try discriminate.
  - inv H2; inv H3.
    rewrite set_set_eq.
    unfold G.
    split.
    eapply wf_env_set; eauto.
    eapply G_wf_env_l; eauto.
    eapply V_wf_val_l; eauto.

    split.
    eapply wf_env_set; eauto.
    eapply G_wf_env_r; eauto.
    eapply V_wf_val_r; eauto.

    intros.
    destruct (var_dec f x); subst.
    + rewrite M.gss in *; auto.
      inv H3.
      eexists; split; eauto.
    + rewrite M.gso in *; auto.
      edestruct (G_get HG) as [v2' [Heqv2' HV]]; eauto.
      * inv H2.
        inv H7.
        inv H7; auto.
        inv H2; contradiction.
      * inv H6.
        inv H7.
        inv H7; auto.
        inv H6; contradiction.
  - destruct (set_lists xs vs1 (M.set f v1 ρ1)) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 (M.set f v2 ρ2)) eqn:Heq2; try discriminate.
    inv H; inv H2; inv H3; subst.
    unfold G.
    split.
    eapply wf_env_set; eauto.
    eapply (wf_env_set_lists (M.set f v1 ρ1)) with (xs := xs) (vs := vs1); eauto.
    eapply wf_env_set; eauto.
    eapply G_wf_env_l; eauto.
    eapply V_wf_val_l; eauto.
    eapply V_wf_val_Forall_l; eauto.
    eapply V_wf_val_l; eauto.

    split.
    eapply wf_env_set; eauto.
    eapply wf_env_set; eauto.
    eapply (wf_env_set_lists (M.set f v2 ρ2)) with (xs := xs) (vs := vs2); eauto.
    eapply wf_env_set; eauto.
    eapply G_wf_env_r; eauto.
    eapply V_wf_val_Forall_r; eauto.
    eapply V_wf_val_r; eauto.
    eapply V_wf_val_r; eauto.

    intros.
    destruct (var_dec f x); subst.
    + rewrite M.gss in *; auto.
      destruct (var_dec a x); subst.
      * exfalso.
        inv H4.
        apply H8.
        apply in_eq.
      * rewrite M.gso in *; auto.
        erewrite <- (set_lists_not_In _ _ _ _ _ Heq1) in H2; eauto.
        rewrite M.gss in *; auto.
        inv H2.
        eexists; split; eauto.
        inv H4.
        intros Hc.
        apply H8.
        apply in_cons; auto.
    + rewrite M.gso; auto.
      destruct (var_dec a x); subst.
      * rewrite M.gss in *; auto.
        inv H2.
        eexists; split; eauto.
      * rewrite M.gso in *; auto.
        assert (HG' : G i (FromList xs :|: (f |: Γ1)) t (FromList xs :|: (f |: Γ2)) (M.set f v3 t0)).
        {
          eapply (IHxs vs1 vs2 v1 v2); eauto.
          - inv H4; constructor.
            intros Hc.
            apply H8.
            apply in_cons; auto.
            inv H10; auto.
          - eapply Disjoint_Included_l; eauto.
            unfold Ensembles.Included, Ensembles.In, FromList.
            intros.
            inv H6.
            apply in_eq.
            repeat (apply in_cons); auto.
        }
        edestruct (G_get HG') with (x := x) as [v4 [Heqv4 HV]]; eauto.
        -- eapply not_In_cons_Union; eauto.
        -- eapply not_In_cons_Union; eauto.
        -- rewrite M.gso in *; auto.
           eexists; split; eauto.
Qed.

(* Compatibility Lemmas *)
Lemma Vfun_V_trans Γ2 {f xs Γ1 e e'} :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  NoDup (f :: xs) ->
  Disjoint _ (FromList (f :: xs)) Γ1 ->
  occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
  forall {i w c C w' ρ1 ρ2},
    L ! w = Some C ->
    ctor_map_web_inv C ->
    C ! c = Some w' ->

    wf_env ρ1 ->
    wf_env ρ2 ->
    G i Γ1 ρ1 Γ2 ρ2 ->

    V i (Tag w (Vfun f ρ1 xs e)) (Tag w (Vconstr c [Tag w' (Vfun f ρ2 xs (Econstr f w c [f] e'))])).
Proof.
  unfold trans_correct.
  intros He Hn Hd HFv i.
  induction i; simpl; intros; auto;
    repeat (split; auto);
    destruct (L ! w) eqn:Heq1; try discriminate; auto; intros;
    try (apply L_inv_Some in Heq1; contradiction).
  inv H.
  repeat (split; auto); intros.
  inv Hn.

  assert (Hρ4 : wf_env ρ4).
  {
    eapply (wf_env_set_lists (M.set f (Tag w' (Vfun f ρ2 xs (Econstr f w c [f] e'))) ρ2)) with (xs := xs) (vs := vs2); eauto.
    eapply wf_env_set; eauto.
    eapply V_wf_val_Forall_r; eauto.
  }

  assert (He' : E false (i - (i - j)) ρ3 e (M.set f (Tag w (Vconstr c [Tag w' (Vfun f ρ2 xs (Econstr f w c [f] e'))])) ρ4) e').
  {
    eapply He; eauto.
    - eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))); eauto.
      + eapply (G_set_lists_trans ρ1) with (vs1 := vs1) (vs2 := vs2) (v2 := (Tag w' (Vfun f ρ2 xs (Econstr f w c [f] e')))); eauto.
        eapply G_mono; eauto; lia.
        assert (HV : V i (Tag w (Vfun f ρ1 xs e)) (Tag w (Vconstr c [Tag w' (Vfun f ρ2 xs (Econstr f w c [f] e'))]))).
        {
          eapply IHi; eauto.
          eapply G_mono; eauto; lia.
        }
        eapply V_mono; eauto; lia.
        constructor; auto.
      + eapply Included_refl.
  }

  unfold E, E' in *.
  intros.
  edestruct He' as [j2 [r2 [Hev HR]]]; eauto.
  exists (S j2), r2; split; auto.
  constructor; auto.
  eapply BStep_constr with (vs := [Tag w' (Vfun f ρ2 xs (Econstr f w c [f] e'))]); eauto.
  - simpl.
    rewrite <- (set_lists_not_In _ _ _ _ _ H7 H10); eauto.
    rewrite M.gss; auto.
  - intros.
    apply L_inv_Some in Heq1; contradiction.
Qed.

Lemma fun_compat_trans {Γ1 e e' C c w' k k' f w xs} :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  trans_correct (f |: Γ1) k k' ->
  M.get w L = Some C ->
  ctor_map_web_inv C ->
  M.get c C = Some w' ->
  NoDup (f :: xs) ->
  Disjoint _ (FromList (f :: xs)) Γ1 ->
  trans_correct Γ1 (Efun f w xs e k) (Efun f w' xs (Econstr f w c [f] e') (Econstr f w c [f] k')).
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H8.
  - exists 0, OOT; split; simpl; eauto.
  - inv H9.
    edestruct (H0 ex (i - 1) (M.set f (Tag w (Vfun f ρ1 xs e)) ρ1) (M.set f (Tag w (Vconstr c [Tag w' (Vfun f ρ2 xs (Econstr f w c [f] e'))])) ρ2)) with (j1 := c0) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_subset with (Γ2 := (f |: (occurs_free (Efun f w' xs (Econstr f w c [f] e') (Econstr f w c [f] k'))))); eauto.
      * eapply G_set; eauto.
        -- eapply G_mono with i; eauto; try lia.
        -- eapply (Vfun_V_trans (occurs_free (Efun f w' xs (Econstr f w c [f] e') (Econstr f w c [f] k')))); eauto.
           ++ eapply free_defun_e_subset; eauto.
           ++ eapply G_wf_env_l; eauto.
           ++ eapply G_wf_env_r; eauto.
           ++ apply G_mono with i; eauto; try lia.
      * apply Included_refl.
      * apply free_defun_k_subset.
    + exists (S (S j2)), r2; split; auto.
      * constructor; auto.
        constructor; auto.
        constructor; auto.
        eapply BStep_constr with (vs := [(Tag w' (Vfun f ρ2 xs (Econstr f w c [f] e')))]); simpl; auto.
        -- rewrite M.gss; auto.
        -- intros.
           apply L_inv_Some in H1; contradiction.
        -- rewrite set_set_eq; auto.
        -- destruct ex; auto.
           eapply R_exposed; eauto.
        -- destruct ex; auto.
           eapply R_exposed; eauto.
      * apply R_mono with ((i - 1) - c0); try lia; auto.
Qed.

Lemma tail_cases_find_tag {c f' w' f w xs} :
  forall {cl},
    In (c, w') cl ->
    NoDup (List.map fst cl) ->
    find_tag (tail_cases cl f' f w xs) c
      (Eproj f' w 0 f (Eapp f' w' xs)).
Proof.
  intros cl.
  induction cl; simpl; intros; try contradiction.
  destruct a.
  inv H0.
  destruct (M.elt_eq c0 c); subst.
  - inv H.
    + inv H0; auto.
    + exfalso.
      assert (In (fst (c, w')) (map fst cl)) by (apply in_map; auto).
      simpl in *; contradiction.
  - inv H.
    inv H0; try contradiction.
    constructor; auto.
Qed.

Lemma app_compat_trans {xs C} Γ f f' w :
  M.get w L = Some C ->
  ctor_map_web_inv C ->

  f' <> f ->
  (~ In f' xs) ->

  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  trans_correct Γ (Eapp f w xs) (Ecase f w (tail_cases (M.elements C) f' f w xs)).
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H7.
  - exists 0, OOT; split; simpl; auto.
  - inv H8.
    unfold Ensembles.Included, Ensembles.In, Dom_map in *.
    edestruct (G_get H5) as [fv2 [Heqfv2 HV]]; eauto.
    destruct fv2.
    destruct i.
    inv H6.
    simpl in HV.
    destruct HV as [Hv1 [Hv2 HV]]; subst.
    destruct (L ! w) eqn:Heq1; try discriminate.
    inv H.
    destruct HV as [Hw HV]; subst.
    destruct v; try contradiction.
    destruct l; try contradiction.
    destruct t; try contradiction.
    destruct v; try contradiction.
    destruct l; try contradiction.
    destruct HV as [Hlen [HCinv [HeqC HV]]]; subst.
    edestruct (G_get_list H5) as [vs2 [Heqvs2 HVs]]; eauto.
    {
      apply free_tail_cases_xs; auto.
      apply M.elements_correct in HeqC; eauto.
    }

    destruct (set_lists_length3 (M.set v (Tag w (Vfun v t l0 e0)) t) l0 vs2) as [ρ4 Heqρ4].
    unfold wval in *.
    rewrite <- (get_list_length_eq _ _ _ Heqvs2).
    rewrite (get_list_length_eq _ _ _ H13).
    rewrite <- (set_lists_length_eq _ _ _ _ H14); auto.

    assert (HE : E false (i - (i - i)) ρ'' e ρ4 e0).
    {
      eapply (HV i vs vs2); eauto.
      apply V_mono_Forall with (S i); auto; lia.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E, E' in HE.
    apply L_inv_Some in Heq1.
    destruct (exposed_reflect w0); try contradiction.
    destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.

    exists (S (S (S j2))), r2; split; eauto.
    assert (if ex then exposed_res r2 else True).
    {
      destruct ex; auto.
      eapply R_exposed; eauto.
    }

    assert (wf_res r2) by (eapply R_wf_res_r; eauto).

    constructor; auto.
    eapply BStep_case with (e := Eproj f' w0 0 f (Eapp f' w xs)); eauto.
    + eapply tail_cases_find_tag; eauto.
      eapply M.elements_correct; eauto.
      apply keys_NoDup.
    + constructor; auto.
      econstructor; simpl; eauto.
      unfold ctor_map_web_inv in *.
      assert (~ w \in Exposed) by (eapply H0; eauto).
      constructor; auto.
      * econstructor; eauto.
        -- rewrite M.gss; auto.
        -- rewrite get_list_set_neq; auto.
        -- destruct (exposed_reflect w); auto; contradiction.
        -- intros; contradiction.
Qed.

Lemma nontail_cases_find_tag {c f w x xs w' f' j w''} :
  forall {cl},
    In (c, w'') cl ->
    NoDup (List.map fst cl) ->
    find_tag (nontail_cases cl f' f w xs j x w') c
      (Eproj f' w 0 f
         (Eletapp x f' w'' xs
            (Eapp j w' [x]))).
Proof.
  intros cl.
  induction cl; simpl; intros; try contradiction.
  destruct a.
  inv H0.
  destruct (M.elt_eq c0 c); subst.
  - inv H.
    + inv H0; auto.
    + exfalso.
      assert (In (fst (c, w'')) (map fst cl)) by (apply in_map; auto).
      simpl in *; contradiction.
  - inv H.
    inv H0; try contradiction.
    constructor; auto.
Qed.

Lemma V_subval_Forall_aux i vs1 vs2 vs3 :
  (forall m : nat,
      m < S i ->
      forall v1 v2 v3 : wval,
      V m v1 v2 -> wf_val v3 -> subval v2 v3 -> V m v1 v3) ->
  Forall2 (V i) vs1 vs2 ->
  Forall2 subval vs2 vs3 ->
  Forall wf_val vs3 ->
  Forall2 (V i) vs1 vs3.
Proof.
  intros IH H.
  revert vs3.
  induction H; simpl; intros.
  - inv H; auto.
  - inv H1.
    inv H2.
    constructor; auto.
    eapply IH; eauto.
Qed.

Lemma V_subval :
  forall {i v1 v2 v3},
    V i v1 v2 ->
    wf_val v3 ->
    subval v2 v3 ->
    V i v1 v3.
Proof.
  intros i.
  induction i using lt_wf_rec; intros.
  destruct i; simpl in *;
    destruct H0 as [Hv1 [Hv2 HV]];
    repeat (split; auto);
    destruct v1; destruct v2;
    destruct (L ! w) eqn:Heq1;
    try contradiction.
  - inv H2.
    inv H5; simpl; auto.

  - destruct HV as [Hw HV]; subst.
    unfold V_refl0 in *.
    destruct v; destruct v0; try contradiction.
    + inv H2.
      inv H5.
      simpl; auto.
    + destruct (subval_Vconstr_inv_l H2) as [l1 [Heql1 Hl]]; auto.
      destruct HV as [Hc Hlen]; subst; simpl in *.
      repeat (split; auto).
      erewrite <- (Forall2_length _ l0 l1); eauto.

  - destruct HV as [Hw HV]; subst.
    unfold VTransM.V_trans in *.
    apply L_inv_Some in Heq1.
    destruct v; destruct v0; try contradiction.
    destruct l0; try contradiction.
    destruct t0; try contradiction.
    destruct v0; try contradiction.
    destruct l0; try contradiction.
    destruct HV as [Hlen [HCinv [HC HV]]].
    destruct (subval_Vconstr_inv_l H2) as [vs2 [Heqvs2 Hvs]]; auto; subst; simpl.
    split; auto.
    inv Hvs.
    inv H6.
    inv H4.
    inv H6; simpl.
    repeat (split; eauto); intros.
    unfold E' in *.
    intros.
    destruct (set_lists_length3 (M.set v0 (Tag w (Vfun v0 t0 l1 e1)) t0) l1 vs2) as [ρ4' Heqρ4'].
    eapply set_lists_length_eq; eauto.

    edestruct (HV j vs1 vs2 ρ3 ρ4') as [j2 [r2 [HE HR]]]; eauto.
    edestruct (bstep_fuel_subenv false (occurs_free e1) ρ4' ρ4) as [r2' [Hr2 [Hs Hr]]]; eauto.
    + destruct (wf_val_Vconstr_inv H1) as [HF HW].
      eapply (wf_env_set_lists (M.set v0 (Tag w (Vfun v0 ρ2 l1 e1)) ρ2)) with (xs := l1) (vs := vs2); eauto.
      inv HF.
      inv H12.
      inv H15.
      eapply wf_env_set; eauto.
      eapply V_wf_val_Forall_r; eauto.
    + apply Included_refl.
    + eapply subenv_subset; eauto.
      eapply (subenv_set_lists (v0 |: Γ) (M.set v0 (Tag w (Vfun v0 t0 l1 e1)) t0) (M.set v0 (Tag w (Vfun v0 ρ2 l1 e1)) ρ2)) with (vs1 := vs2) (vs2 := vs2); eauto.
      eapply subenv_set; eauto.
      apply subval_refl_Forall; auto.
      eapply V_wf_val_Forall_r; eauto.
    + exists j2, r2'; split; auto.
      unfold R' in *.
      inv Hs; destruct r1; try contradiction; auto.
      inv Hr.
      eapply H; eauto; lia.

  - destruct HV as [Hw HV]; subst.
    unfold V_refl in *.
    destruct v; destruct v0; try contradiction.
    + destruct HV as [Hlen HV].
      inv H2.
      inv H5.
      simpl.
      repeat (split; auto); intros.
      unfold E' in *.
      intros.
      destruct (set_lists_length3 (M.set v0 (Tag w0 (Vfun v0 t0 l0 e0)) t0) l0 vs2) as [ρ4' Heqρ4'].
      eapply set_lists_length_eq; eauto.

      edestruct (HV j vs1 vs2 ρ3 ρ4') as [j2 [r2 [HE HR]]]; eauto.
      edestruct (bstep_fuel_subenv (exposedb w0) (occurs_free e0) ρ4' ρ4) as [r2' [Hr2 [Hs Hr]]]; eauto.
      * inv H1.
        inv H14.
        eapply (wf_env_set_lists (M.set v0 (Tag w0 (Vfun v0 ρ2 l0 e0)) ρ2)) with (xs := l0) (vs := vs2); eauto.
        eapply wf_env_set; eauto.
        eapply V_wf_val_Forall_r; eauto.
      * eapply Included_refl.
      * eapply subenv_subset; eauto.
        eapply (subenv_set_lists (v0 |: Γ) (M.set v0 (Tag w0 (Vfun v0 t0 l0 e0)) t0) (M.set v0 (Tag w0 (Vfun v0 ρ2 l0 e0)) ρ2)) with (vs1 := vs2) (vs2 := vs2); eauto.
        eapply subenv_set; eauto.
        apply subval_refl_Forall.
        eapply V_wf_val_Forall_r; eauto.
      * exists j2, r2'; split; auto.
        unfold R' in *.
        inv Hs; destruct r1; try contradiction; auto.
        inv Hr.
        eapply H; eauto; lia.
    + destruct HV as [Hc HV]; subst.
      destruct (subval_Vconstr_inv_l H2) as [l1 [Heql1 Hl]]; subst; simpl.
      repeat (split; auto).
      rewrite normalize_step in *; auto.
      eapply V_subval_Forall_aux; eauto.
      destruct (wf_val_Vconstr_inv H1); auto.
Qed.

Lemma R_subres i r1 r2 r3 :
  R i r1 r2 ->
  subres r2 r3 ->
  wf_res r3 ->
  R i r1 r3.
Proof.
  unfold R, R'.
  intros.
  inv H0; destruct r1; auto.
  eapply V_subval; eauto.
  inv H1; auto.
Qed.

Lemma letapp_compat_trans {xs x C k k' Γ} f w w' f' j :
  M.get w L = Some C ->
  ctor_map_web_inv C ->

  f' <> f ->
  (~ In f' xs) ->

  j <> x ->
  j <> f ->
  j <> f' ->
  (~ In j xs) ->
  (~ j \in (occurs_free k')) ->

  (~ w' \in Exposed) ->

  (f \in Γ) ->
  (FromList xs \subset Γ) ->

  trans_correct (x |: Γ) k k' ->
  trans_correct Γ (Eletapp x f w xs k) (Efun j w' [x] k'
                                          (Ecase f w
                                             (nontail_cases (M.elements C) f' f w xs j x w'))).
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H14.
  - exists 0, OOT; split; simpl; auto.
  - inv H15.
    2 : { exists 0, OOT; split; simpl; auto. }
    unfold Ensembles.Included, Ensembles.In, Dom_map in *.
    edestruct (G_get H12) as [fv2 [Heqfv2 HV]]; eauto.
    destruct fv2.
    destruct i.
    inv H13.
    simpl in HV.
    destruct HV as [Hv1 [Hv2 HV]]; subst.
    destruct (L ! w) eqn:Heq1; try discriminate.
    inv H.
    destruct HV as [Hw HV]; subst.
    destruct v0; try contradiction.
    destruct l; try contradiction.
    destruct t; try contradiction.
    destruct v0; try contradiction.
    destruct l; try contradiction.
    destruct HV as [Hlen [HCinv [HeqC HV]]]; subst.
    edestruct (G_get_list H12) as [vs2 [Heqvs2 HVs]]; eauto.
    {
      apply free_nontail_cases_xs; auto.
      apply M.elements_correct in HeqC; eauto.
    }

    destruct (set_lists_length3 (M.set v0 (Tag w (Vfun v0 t l0 e0)) t) l0 vs2) as [ρ4 Heqρ4].
    unfold wval in *.
    rewrite <- (get_list_length_eq _ _ _ Heqvs2).
    rewrite (get_list_length_eq _ _ _ H22).
    rewrite <- (set_lists_length_eq _ _ _ _ H25); auto.

    assert (HE : E false (i - (i - i)) ρ'' e ρ4 e0).
    {
      eapply (HV i vs vs2); eauto.
      apply V_mono_Forall with (S i); auto; lia.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E, E' in HE.
    apply L_inv_Some in Heq1.
    destruct (exposed_reflect w0); try contradiction.

    destruct (HE c0 (Res v)) as [j2 [r2 [He0 Rr]]]; try lia; auto.
    destruct r2; simpl in Rr; try contradiction.

    edestruct (H11 ex (i - c0) (M.set x v ρ1) (M.set x w1 ρ2)) with (j1 := c') (r1 := r1) as [j3 [r3 [Hk' Rk']]]; eauto; try lia.
    + eapply G_subset with (Γ2 := x |: (occurs_free
                                          (Efun j w' [x] k'
                                             (Ecase f w0 (nontail_cases (M.elements C) f' f w0 xs j x w'))))).
      * eapply G_set; eauto.
        eapply G_mono with (S i); eauto; try lia.

      * apply Included_refl.
      * unfold Ensembles.Included, Ensembles.In.
        intros.
        destruct (var_dec x x0); subst.
        apply Union_introl; auto.
        destruct (var_dec j x0); subst; try contradiction.
        apply Union_intror.
        apply Free_fun2; auto.
        intros Hc.
        inv Hc; contradiction.
    + assert (wf_env ρ1) by (eapply G_wf_env_l; eauto).
      assert (wf_env ρ2) by (eapply G_wf_env_r; eauto).
      edestruct (bstep_fuel_subenv ex (occurs_free k') (M.set x w1 ρ2) (M.set x w1 (M.set j (Tag w' (Vfun j ρ2 [x] k')) ρ2))) as [r3' [Hr3' [Hr Hwfr3']]]; eauto.
      * eapply wf_env_set; eauto.
        eapply wf_env_set; eauto.
        eapply V_wf_val_r; eauto.
      * apply Included_refl.
      * constructor; intros.
        destruct (var_dec x x0); subst.
        -- rewrite M.gss in *.
           inv H17.
           eexists; split; auto.
           apply subval_refl.
           eapply V_wf_val_r; eauto.
        -- rewrite M.gso in *; auto.
           destruct (var_dec j x0); subst; try contradiction.
           rewrite M.gso; auto.
           eexists; split; eauto.
           apply subval_refl.
           eapply wf_env_get; eauto.
      * exists (S (S (S (S (S (j2 + j3)))))), r3'; split; eauto.
        2 : { eapply R_subres; eauto.
              eapply R_mono; eauto; lia. }

        assert (if ex then exposed_res r3' else True).
        {
          destruct ex; auto.
          eapply subres_exposed; eauto.
          eapply R_exposed; eauto.
        }

        assert (Hρj : wf_env (M.set j (Tag w' (Vfun j ρ2 [x] k')) ρ2)) by (eapply wf_env_set; eauto).
        constructor; auto.
        constructor; auto.
        constructor; auto.
        eapply BStep_case with (e := (Eproj f' w0 0 f
                                        (Eletapp x f' w xs
                                           (Eapp j w' [x])))); eauto.
        -- rewrite M.gso; eauto.
        -- eapply nontail_cases_find_tag; eauto.
           eapply M.elements_correct; eauto.
           apply keys_NoDup.
        -- constructor; auto.
           econstructor; simpl; eauto.
           rewrite M.gso; eauto.
           simpl; eauto.
           unfold ctor_map_web_inv in *.
           assert (Hw : ~ w \in Exposed) by (eapply H0; eauto).
           assert (Hρf_elim : wf_env
                                (M.set f' (TAG val w (Vfun v0 t l0 e0))
                                   (M.set j (Tag w' (Vfun j ρ2 [x] k')) ρ2))).
           {
             eapply wf_env_set; eauto.
             destruct (wf_val_Vconstr_inv Hv2) as [HF HW].
             inv HF; auto.
           }
           constructor; auto.

           assert (Hj : (S (j2 + j3)) = j2 + (S j3)) by lia.
           rewrite Hj.
           econstructor; eauto.
           rewrite M.gss; auto.
           rewrite get_list_set_neq; auto.
           rewrite get_list_set_neq; auto.
           destruct (exposed_reflect w); eauto; try contradiction.
           intros; contradiction.

           assert (Hρx : wf_env
                           (M.set x w1
                              (M.set f' (TAG val w (Vfun v0 t l0 e0))
                                 (M.set j (Tag w' (Vfun j ρ2 [x] k')) ρ2)))).
           {
             eapply wf_env_set; eauto.
             eapply V_wf_val_r; eauto.
           }

           constructor; auto.
           econstructor; eauto.
           ++ rewrite M.gso; auto.
              rewrite M.gso; auto.
              rewrite M.gss; eauto.
           ++ simpl.
              rewrite M.gss; auto.
           ++ simpl; eauto.
           ++ destruct (exposed_reflect w'); auto; try contradiction.
              destruct ex; auto.
              eapply bstep_fuel_exposed; eauto.
           ++ intros; contradiction.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {Γ e e'} :
  trans Γ e e' -> trans_correct Γ e e'.
Proof.
  intro H.
  induction H.
  - eapply ret_compat; eauto.
  - eapply fun_compat_trans; eauto.
  - eapply fun_compat; eauto.
  - eapply app_compat_trans; eauto.
  - eapply app_compat; eauto.
  - eapply letapp_compat_trans; eauto.
  - eapply letapp_compat; eauto.
  - eapply constr_compat; eauto.
  - eapply proj_compat; eauto.
  - eapply case_nil_compat; eauto.
  - eapply case_cons_compat; eauto.
Qed.

(* Top Level *)
Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  wf_env ρ1 /\
  wf_env ρ2 /\
  forall x,
    (x \in Γ1) ->
    exists v1,
      M.get x ρ1 = Some v1 /\
      exposed v1 /\
      ((x \in Γ2) ->
       exists v2,
         M.get x ρ2 = Some v2 /\
         V i v1 v2).

Lemma G_top_G : forall {i Γ1 ρ1 Γ2 ρ2},
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    G i Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G_top, G.
  intros.
  destruct H as [Hr1 [Hr2 HG]].
  repeat (split; auto); intros.
  edestruct HG as [v1' [Heqv1' [Hexv1' Hv2]]]; eauto.
  rewrite Heqv1' in H0; inv H0.
  destruct Hv2 as [v2 [Heqv2 HV]]; eauto.
Qed.

Definition trans_correct_top etop etop' :=
  forall i ρ1 ρ2,
    G_top i (occurs_free etop) ρ1 (occurs_free etop') ρ2 ->
    E true i ρ1 etop ρ2 etop'.

Theorem top etop etop' :
  trans (occurs_free etop) etop etop' ->
  trans_correct_top etop etop'.
Proof.
  unfold trans_correct_top.
  intros.
  specialize (fundamental_property H);
    unfold trans_correct; intros.
  eapply H1; auto.
  eapply G_top_G; eauto.
Qed.

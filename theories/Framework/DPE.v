From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF Exposed.

(* Dead Parameter Elimination *)

(* Map from web identifier to the live parameter list *)
Module LT <: Exposed.LTy. Definition t := (list bool). End LT.
Module LM := Exposed.DefaultL LT.
Import LM.

(* Apply bit mask to argument list *)
Fixpoint live_args {A} (ys : list A) (bs : list bool) : list A :=
  match bs, ys with
  | [], [] => ys
  | b :: bs', y :: ys' =>
    if b then y :: (live_args ys' bs')
    else live_args ys' bs'
  | _, _ => ys
  end.

Fixpoint dead_args {A} (ys : list A) (bs : list bool) : list A :=
  match bs, ys with
  | [], [] => ys
  | b :: bs', y :: ys' =>
    if b then (dead_args ys' bs')
    else y :: dead_args ys' bs'
  | _, _ => ys
  end.

(* Specification *)
Inductive trans (Γ : Ensemble var) : exp -> exp -> Prop :=
| Trans_ret :
  forall {x},
    (x \in Γ) ->
    trans Γ (Eret x) (Eret x)

| Trans_fun :
  forall {f w xs e k bs e' k'},
    M.get w L = Some bs ->
    length xs = length bs ->

    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->

    NoDup (f :: xs) ->
    Disjoint _ (FromList xs) Γ ->

    Disjoint _ (FromList (dead_args xs bs)) (occurs_free e) ->
    trans Γ (Efun f w xs e k) (Efun f w (live_args xs bs) e' k')

| Trans_fun_exposed :
  forall {f w xs e k e' k'},
    M.get w L = None ->
    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->
    trans Γ (Efun f w xs e k) (Efun f w xs e' k')

| Trans_app :
  forall {f w xs bs},
    M.get w L = Some bs ->
    length xs = length bs ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans Γ (Eapp f w xs) (Eapp f w (live_args xs bs))

| Trans_app_exposed :
  forall {f w xs},
    M.get w L = None ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans Γ (Eapp f w xs) (Eapp f w xs)

| Trans_letapp :
  forall {x f w xs k bs k'},
    M.get w L = Some bs ->
    length xs = length bs ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (Eletapp x f w xs k) (Eletapp x f w (live_args xs bs) k')

| Trans_letapp_exposed :
  forall {x f w xs k k'},
    M.get w L = None ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (Eletapp x f w xs k) (Eletapp x f w xs k')

| Trans_constr :
  forall {x w t xs k k'},
    M.get w L = None ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (Econstr x w t xs k) (Econstr x w t xs k')

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

(* Logical Relations *)
Module VTransM <: Exposed.VTrans LM.

  Definition V_trans
    (V' : nat -> wval -> wval -> Prop)
    (E' : nat -> env -> exp -> env -> exp -> Prop)
    (i0 : nat) (bs : list bool)
    (w1 : web) (v1 : val) (w2 : web) (v2 : val) :=
    w1 = w2 /\
    match v1, v2 with
    | Vfun f1 ρ1 xs1 e1, Vfun f2 ρ2 xs2 e2 =>
        length xs1 = length bs /\
        xs2 = live_args xs1 bs /\

        forall j vs1 vs2 ρ3 ρ4,
          j <= i0 ->
          Forall wf_val vs1 ->
          Forall2 (V' j) (live_args vs1 bs) vs2 ->
          set_lists xs1 vs1 (M.set f1 (Tag w1 (Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
          set_lists xs2 vs2 (M.set f2 (Tag w2 (Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
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
    intros HI. intros.
    destruct v1; destruct v2; auto;
      simpl in *; try contradiction;
      rename l into xs1;
      rename l0 into xs2.
    destruct H as [Hw [Hlen [Heq HV]]].
    repeat split; eauto; intros.
    specialize (HV j0 vs1 vs2 ρ3 ρ4).
    rewrite normalize_step in *; try lia.
    eapply HV; eauto; try lia.
  Qed.

End VTransM.

Module EM := Exposed.Exposed LM VTransM.
Import EM.

(* Lemmas about [live_args] and [dead_args] *)
Lemma live_args_incl {A xs bs} :
  incl (@live_args A xs bs) xs.
Proof.
  revert bs.
  induction xs; intros.
  - destruct bs; simpl; apply incl_nil_l.
  - destruct bs; simpl.
    + apply incl_refl.
    + destruct b.
      * apply incl_cons.
        apply in_eq; auto.
        apply incl_tl; auto.
      * apply incl_tl; auto.
Qed.

Lemma live_args_In : forall {A xs bs a}, In a (@live_args A xs bs) -> In a xs.
Proof.
  intros; eapply live_args_incl; eauto.
Qed.

Lemma live_args_not_In : forall {A xs a} bs, ~ In a xs -> ~ In a (@live_args A xs bs).
Proof.
  intros.
  intro Hc.
  apply H.
  eapply live_args_In; eauto.
Qed.

Lemma live_args_length {A B} xs ys bs :
  length xs = length ys ->
  length (@live_args A xs bs) = length (@live_args B ys bs).
Proof.
  revert ys bs. induction xs; intros; eauto.
  - destruct ys; try (simpl in * ; congruence).
    destruct bs; reflexivity.
  - simpl.
    destruct ys; try (simpl in * ; congruence). inv H.
    destruct bs. simpl. congruence.
    destruct b0; simpl; eauto.
Qed.

Lemma not_live_dead_args {A} : forall {xs bs x},
    length xs = length bs ->
    ~ In x (@live_args A xs bs) ->
    In x xs ->
    In x (@dead_args A xs bs).
Proof.
  intros xs.
  induction xs; simpl; intros.
  - contradiction.
  - destruct bs; inv H.
    destruct b.
    + inv H1.
      * exfalso.
        apply H0; apply in_eq.
      * apply IHxs; auto.
        intro Hc.
        apply H0; apply in_cons; auto.
    + inv H1.
      * apply in_eq.
      * apply in_cons; apply IHxs; auto.
Qed.

(* Invariants of [trans] *)
Lemma trans_env_inv {Γ e e'} :
  trans Γ e e' ->
  (occurs_free e) \subset Γ.
Proof.
  intros H.
  induction H; unfold Ensembles.Included, Ensembles.In, FromList in *; intros.
  - inv H0; auto.
  - inv H6; auto.
    + specialize (IHtrans2 _ H14).
      inv IHtrans2; auto.
      inv H6; contradiction.
    + specialize (IHtrans1 _ H15).
      inv IHtrans1; try contradiction.
      inv H6; auto.
      inv H7; contradiction.
  - inv H2.
    + specialize (IHtrans2 _ H10).
      inv IHtrans2; auto.
      inv H2; contradiction.
    + specialize (IHtrans1 _ H11).
      inv IHtrans1; try contradiction.
      inv H2; auto.
      inv H3; contradiction.
  - inv H3; auto.
  - inv H2; auto.
  - inv H4; auto.
    specialize (IHtrans _ H12).
    inv IHtrans; auto.
    inv H4; contradiction.
  - inv H3; auto.
    specialize (IHtrans _ H11).
    inv IHtrans; auto.
    inv H3; contradiction.
  - inv H2; auto.
    specialize (IHtrans _ H10).
    inv IHtrans; auto.
    inv H2; contradiction.
  - inv H2; auto.
    specialize (IHtrans _ H10).
    inv IHtrans; auto.
    inv H2; contradiction.
  - inv H0; auto.
  - inv H3; auto.
Qed.

Lemma trans_fun_inv {f w xs bs e' k' e k }:
  (occurs_free e') \subset (occurs_free e) ->
  (occurs_free k') \subset (occurs_free k) ->
  Disjoint var (FromList (dead_args xs bs)) (occurs_free e) ->
  length xs = length bs ->
  (occurs_free (Efun f w (live_args xs bs) e' k')) \subset (occurs_free (Efun f w xs e k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  inv H3; auto.
  destruct (in_dec M.elt_eq x xs); auto.
  specialize (H _ H12).
  apply not_live_dead_args in H11; auto.
  exfalso.
  inv H1.
  apply (H3 x); auto.
Qed.

Lemma trans_exp_inv {Γ e e'} :
  trans Γ e e' ->
  (occurs_free e') \subset (occurs_free e).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros H.
  induction H; intros; auto.
  - eapply trans_fun_inv; eauto.
  - inv H2; auto.
  - inv H3; auto.
    apply live_args_In in H8; auto.
  - inv H4; auto.
    apply live_args_In in H11; auto.
  - inv H3; auto.
  - inv H2; auto.
  - inv H2; auto.
  - inv H3; auto.
Qed.

(* Environment Lemmas *)
Lemma G_set_lists_trans {i Γ1 ρ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  Γ2 \subset Γ1 ->
  forall {xs vs1 vs2 ρ3 ρ4 bs},
    length xs = length bs ->
    Forall wf_val vs1 ->
    Forall wf_val vs2 ->
    Forall2 (V i) (live_args vs1 bs) vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists (live_args xs bs) vs2 ρ2 = Some ρ4 ->
    NoDup xs ->
    Disjoint _ (FromList xs) Γ1 ->
    G i (FromList xs :|: Γ1) ρ3 (FromList (live_args xs bs) :|: Γ2) ρ4.
Proof.
  intros HG HS xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct bs; try discriminate.
    simpl in *.
    destruct vs2; try discriminate.
    inv H3; inv H4.
    eapply G_subset; eauto;
      rewrite FromList_nil;
      apply Union_Empty_set_neut_l.
  - destruct vs1; try discriminate.
    destruct bs; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    inv H; inv H0; inv H3.

    assert (Hwt : wf_env (map_util.M.set a w t)).
    {
      eapply wf_env_set; eauto.
      eapply (wf_env_set_lists ρ1) with (xs := xs) (vs := vs1); eauto.
      eapply G_wf_env_l; eauto.
    }

    destruct b; simpl in *.
    + destruct vs2; try discriminate.
      destruct (set_lists (live_args xs bs) vs2 ρ2) eqn:Heq2; try discriminate.
      inv H1; inv H2; inv H4; inv H5.
      unfold G.
      split; auto.
      split.
      eapply wf_env_set; eauto.
      eapply (wf_env_set_lists ρ2) with (xs := live_args xs bs) (vs := vs2); eauto.
      eapply G_wf_env_r; eauto.

      intros.
      destruct (M.elt_eq x a); subst.
      * repeat rewrite M.gss in *; eauto.
        inv H0.
        eexists; split; eauto.
      * rewrite M.gso in *; auto.
        assert (HG' : G i (FromList xs :|: Γ1) t (FromList (live_args xs bs) :|: Γ2) t0).
        {
          eapply (IHxs vs1); eauto.
          eapply Disjoint_FromList_cons_l; eauto.
        }
        eapply (G_get HG'); eauto.
        eapply not_In_cons_Union; eauto.
        eapply not_In_cons_Union; eauto.
    + unfold G.
      split; auto.
      split.
      eapply (wf_env_set_lists ρ2) with (xs := (live_args xs bs)) (vs := vs2); eauto.
      eapply G_wf_env_r; eauto.

      intros.
      inv H5.
      destruct (M.elt_eq x a); subst.
      * inv H6.
        exfalso.
        unfold Ensembles.Included, Ensembles.In, FromList in *.
        inv H3.
        -- apply H12.
           eapply live_args_In; eauto.
        -- apply (H5 a).
           constructor; auto.
           apply in_eq.
      * rewrite M.gso in *; auto.
        assert (HG' : G i (FromList xs :|: Γ1) t (FromList (live_args xs bs) :|: Γ2) ρ4).
        {
          eapply (IHxs vs1 vs2); eauto.
          eapply Disjoint_FromList_cons_l; eauto.
        }
        eapply (G_get HG'); eauto.
        eapply not_In_cons_Union; eauto.
Qed.

Lemma G_get_list_trans {i Γ1 Γ2 ρ1 ρ2} :
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall xs bs vs1,
    (FromList xs) \subset Γ1 ->
    (FromList (live_args xs bs)) \subset Γ2 ->
    length xs = length bs ->
    get_list xs ρ1 = Some vs1 ->
    exists vs2,
      get_list (live_args xs bs) ρ2 = Some vs2 /\
      Forall2 (V i) (live_args vs1 bs) vs2.
Proof.
  intros HG xs.
  induction xs; simpl; intros.
  - inv H2.
    destruct bs; simpl in *; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H2.
    destruct bs; inv H1.
    destruct b; simpl in *.
    + unfold Ensembles.Included, Ensembles.In, Dom_map, FromList in *.
      edestruct (G_get HG) as [v2 [Heqv2 HV]]; eauto.
      apply H; apply in_eq.
      apply H0; apply in_eq.
      rewrite Heqv2.
      edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
      intros; apply H; apply in_cons; auto.
      intros; apply H0; apply in_cons; auto.
      exists (v2 :: vs2); split; auto.
      rewrite Heqvs2; auto.
    + edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
      unfold Ensembles.Included, Ensembles.In, FromList in *.
      intros.
      apply H; apply in_cons; auto.
Qed.

(* Compatibility Lemmas *)
Lemma Vfun_V_trans {Γ2 f xs Γ1 e e'} :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  Γ2 \subset Γ1 ->
  NoDup (f :: xs) ->
  Disjoint _ (FromList xs) Γ1 ->
  forall {i ρ1 ρ2 bs} w,
    L ! w = Some bs ->
    length xs = length bs ->
    G i Γ1 ρ1 Γ2 ρ2 ->
    occurs_free e' \subset (FromList (live_args xs bs) :|: (f |: Γ2)) ->
    V i (Tag w (Vfun f ρ1 xs e)) (Tag w (Vfun f ρ2 (live_args xs bs) e')).
Proof.
  unfold trans_correct.
  intros He HS Hn Hd i.
  induction i; simpl; intros;
    assert (wf_env ρ1) by (eapply G_wf_env_l; eauto);
    assert (wf_env ρ2) by (eapply G_wf_env_r; eauto);
    repeat (split; auto);
    destruct (L ! w) eqn:Heq1; try discriminate; auto.
  inv H.
  repeat split; auto; intros.
  inv Hn.
  apply (He false (i - (i - j)) ρ3 ρ4); auto.
  - eapply G_subset with (Γ1 := (FromList xs :|: (f |: Γ1))) (Γ2 := (FromList (live_args xs bs) :|: (f |: Γ2))); eauto.
    + eapply G_set_lists_trans with (vs1 := vs1) (vs2 := vs2); eauto.
      * eapply G_set; eauto.
        eapply G_mono with (S i); eauto; try lia.
        eapply V_mono with i; try lia.
        eapply IHi; eauto.
        eapply G_mono; eauto; lia.
      * apply Included_Union_compat; auto.
        apply Included_refl.
      * eapply V_wf_val_Forall_r; eauto.
      * apply Disjoint_FromList_cons_r; auto.
    + apply Included_refl.
Qed.

Lemma fun_compat_trans {Γ1 e e' bs k k'} f w xs :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  trans_correct (f |: Γ1) k k' ->
  M.get w L = Some bs ->
  length xs = length bs ->
  NoDup (f :: xs) ->
  Disjoint _ (FromList xs) Γ1 ->
  (occurs_free (Efun f w (live_args xs bs) e' k')) \subset Γ1 ->
  trans_correct Γ1 (Efun f w xs e k) (Efun f w (live_args xs bs) e' k').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H8.
  - exists 0, OOT; split; simpl; eauto.
  - inv H9.
    edestruct (H0 ex (i - 1) (M.set f (Tag w (Vfun f ρ1 xs e)) ρ1) (M.set f (Tag w (Vfun f ρ2 (live_args xs bs) e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_subset with (Γ2 := (f |: (occurs_free (Efun f w (live_args xs bs) e' k')))); eauto.
      * eapply G_set; eauto.
        -- eapply G_mono with i; eauto; try lia.
        -- eapply Vfun_V_trans; eauto.
           ++ apply G_mono with i; eauto; try lia.
           ++ eapply free_fun_e_subset; eauto.
      * apply Included_refl.
      * apply free_fun_k_subset.
    + exists (S j2), r2; split; auto.
      * constructor; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma app_compat_trans {xs bs} Γ f w :
  M.get w L = Some bs ->
  length xs = length bs ->
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  trans_correct Γ (Eapp f w xs) (Eapp f w (live_args xs bs)).
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H5.
  - exists 0, OOT; split; simpl; auto.
  - inv H6.
    unfold Ensembles.Included, Ensembles.In, Dom_map in *.
    edestruct (G_get H3) as [fv2 [Heqfv2 HV]]; eauto.
    destruct fv2.
    destruct i.
    inv H4.
    simpl in HV.
    destruct HV as [Hv1 [Hv2 HV]]; subst.
    destruct (L ! w) eqn:Heq1; try discriminate.
    destruct v;
      destruct HV as [Hw HV]; subst;
      try contradiction.
    destruct HV as [Hlen [Hl HV]].
    inv H.
    edestruct (G_get_list_trans H3 xs bs) as [vs2 [Heqvs2 Vvs]]; eauto.
    {
      unfold Ensembles.Included, Ensembles.In, FromList, Dom_map.
      intros; auto.
    }

    destruct (set_lists_length3 (M.set v (Tag w0 (Vfun v t (live_args xs' bs) e1)) t) (live_args xs' bs) vs2) as [ρ4 Heqρ4].
    unfold wval in *.
    rewrite <- (Forall2_length _ _ _ Vvs).
    apply live_args_length.
    rewrite <- (set_lists_length_eq _ _ _ _ H12); auto.

    assert (HE : E false (i - (i - i)) ρ'' e ρ4 e1).
    {
      eapply (HV i vs vs2); eauto.
      eapply wf_env_get_list; eauto.
      eapply G_wf_env_l; eauto.
      apply V_mono_Forall with (S i); auto; lia.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E, E' in HE.
    apply L_inv_Some in Heq1.
    destruct (exposed_reflect w0); try contradiction.
    destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.

    exists (S j2), r2; split; eauto.
    constructor; auto.
    + eapply BStep_app; eauto.
      destruct (exposed_reflect w0); try contradiction; eauto.
      intros.
      contradiction.
    + destruct ex; auto.
      eapply R_exposed; eauto.
Qed.

Lemma letapp_compat_trans {Γ k k' w bs xs} x f :
  trans_correct (x |: Γ) k k' ->
  M.get w L = Some bs ->
  length xs = length bs ->
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  trans_correct Γ (Eletapp x f w xs k) (Eletapp x f w (live_args xs bs) k').
Proof.
  intros.
  specialize (app_compat_trans Γ f w H0 H1 H2); intros Ha.
  unfold trans_correct, E, E' in *.
  intros.

  assert (HGa : G i Γ ρ1 (occurs_free (Eapp f w (live_args xs bs))) ρ2).
  {
    eapply G_subset; eauto.
    apply Included_refl.
    apply free_app_letapp.
  }

  specialize (Ha H3 (exposedb w) _ _ _ HGa).
  inv H6.
  - exists 0, OOT; split; simpl; auto.
  - inv H7.
    + destruct (Ha (S c0) (Res v)) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      * constructor; auto.
        -- eapply BStep_app; eauto.
           intros.
           destruct H19; auto.
        -- destruct (exposed_reflect w); auto.
           destruct H19; auto.
      * simpl in Rra.
        destruct ra; try contradiction.
        rename w0 into v0.
        edestruct (H ex (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
        -- eapply G_subset with (Γ2 := (x |: (occurs_free (Eletapp x f w (live_args xs bs) k')))).
           eapply G_set; eauto.
           apply G_mono with i; try lia; eauto.
           apply Included_refl.
           apply free_letapp_k_subset.
        -- exists (j1 + j2), r2; split.
           ++ inv Hap.
              inv H6.
              rewrite_math ((S c + j2) = S (c + j2)).
              constructor; auto.
              ** eapply BStep_letapp_Res; eauto.
                 intros.
                 destruct H24; auto.
                 inv H10.
                 split; auto.
              ** destruct ex; auto.
                 eapply R_exposed; eauto.
           ++ apply R_mono with (i - S c0 - c'); try lia; auto.
    + destruct (Ha (S c) OOT) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      constructor; eauto.
      destruct (exposed_reflect w); auto.
      exists j1, ra.
      destruct ra; try contradiction.
      split; auto.
      inv Hap; eauto.
      inv H6; eauto.
      constructor; auto.
      eapply BStep_letapp_OOT; eauto.
      intros.
      destruct H23; auto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {Γ e e'} :
  trans Γ e e' -> trans_correct Γ e e'.
Proof.
  intro H.
  induction H.
  - apply ret_compat; auto.
  - eapply fun_compat_trans; eauto.
    apply Included_trans with (occurs_free (Efun f w xs e k)).
    + eapply trans_fun_inv; eauto.
      eapply trans_exp_inv; eauto.
      eapply trans_exp_inv; eauto.
    + eapply trans_env_inv; eauto.
  - eapply fun_compat; eauto.
  - eapply app_compat_trans; eauto.
  - eapply app_compat; eauto.
  - eapply letapp_compat_trans; eauto.
  - eapply letapp_compat; eauto.
  - eapply constr_compat; eauto.
  - apply proj_compat; auto.
  - apply case_nil_compat; auto.
  - apply case_cons_compat; auto.
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

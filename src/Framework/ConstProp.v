From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF Exposed.

(* Constant Propagation *)

(* Constant Map *)
Definition info_t : Type := ctor_tag * web.
Parameter C : M.t info_t.

(* Web Map *)
Module LT <: Exposed.LTy. Definition t := list (option info_t). End LT.
Module LM := Exposed.DefaultL LT.
Import LM.

(* Apply bit mask to argument list *)
Fixpoint const_args {A} (ys : list A) (cs : list (option info_t)) : list A :=
  match ys, cs with
  | [], [] => ys
  | y :: ys', c :: cs' =>
      match c with
      | Some _ => y :: (const_args ys' cs')
      | None => const_args ys' cs'
      end
  | _, _ => ys
  end.

Fixpoint nonconst_args {A} (ys : list A) (cs : list (option info_t)) : list A :=
  match ys, cs with
  | [], [] => ys
  | y :: ys', c :: cs' =>
      match c with
      | Some _ => (nonconst_args ys' cs')
      | None => y :: (nonconst_args ys' cs')
      end
  | _, _ => ys
  end.

(* Make sure the corresponding vars and vals are literal constants *)
Fixpoint correct_const_vars (xs : list var) (cs : list (option info_t)) : Prop :=
  match xs, cs with
  | [], [] => True
  | x :: xs', c :: cs' =>
      (match c with
       | Some info => M.get x C = Some info
       | None => True
       end) /\
      (correct_const_vars xs' cs')
  | _, _ => False
  end.

Fixpoint correct_const_vals (vs : list wval) (cs : list (option info_t)) : Prop :=
  match vs, cs with
  | [], [] => True
  | v :: vs', c :: cs' =>
      (match c with
      | Some (c, w) => v = (Tag w (Vconstr c []))
      | None => True
      end) /\
      (correct_const_vals vs' cs')
  | _, _ => False
  end.

(* Bind variables to their literal constant values *)
Fixpoint bind_consts (xs : list var) (cs : list (option info_t)) (e : exp) : exp :=
  match xs, cs with
  | x :: xs', c :: cs' =>
      match c with
      | Some (c, w) => Econstr x w c [] (bind_consts xs' cs' e)
      | None => bind_consts xs' cs' e
      end
  | _, _ => e
  end.

(* Specification *)
Inductive trans (Γ : Ensemble var) : exp -> exp -> Prop :=
| Trans_ret :
  forall {x},
    (x \in Γ) ->
    trans Γ (Eret x) (Eret x)

| Trans_fun :
  forall {f w xs e k cs e' k'},
    M.get w L = Some cs ->
    length xs = length cs ->

    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->

    NoDup (f :: xs) ->
    Disjoint _ (FromList (f :: xs)) Γ ->

    M.get f C = None ->
    Forall (fun x => M.get x C = None) xs ->

    trans Γ (Efun f w xs e k) (Efun f w (nonconst_args xs cs) (bind_consts xs cs e') k')

| Trans_fun_exposed :
  forall {f w xs e k e' k'},
    M.get w L = None ->
    M.get f C = None ->
    Forall (fun x => M.get x C = None) xs ->
    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->
    trans Γ (Efun f w xs e k) (Efun f w xs e' k')

| Trans_app :
  forall {f w xs cs},
    M.get w L = Some cs ->
    length xs = length cs ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    correct_const_vars xs cs ->
    trans Γ (Eapp f w xs) (Eapp f w (nonconst_args xs cs))

| Trans_app_exposed :
  forall {f w xs},
    M.get w L = None ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans Γ (Eapp f w xs) (Eapp f w xs)

| Trans_letapp :
  forall {x f w xs k cs k'},
    M.get w L = Some cs ->
    length xs = length cs ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    M.get x C = None ->
    correct_const_vars xs cs ->
    trans Γ (Eletapp x f w xs k) (Eletapp x f w (nonconst_args xs cs) k')

| Trans_letapp_exposed :
  forall {x f w xs k k'},
    M.get w L = None ->
    M.get x C = None ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k k' ->
    trans Γ (Eletapp x f w xs k) (Eletapp x f w xs k')

| Trans_constr :
  forall {x w c xs k k'},
    M.get w L = None ->
    (FromList xs \subset Γ) ->
    (match xs with
     | [] => M.get x C = Some (c, w)
     | _ => M.get x C = None
     end) ->
    trans (x |: Γ) k k' ->
    trans Γ (Econstr x w c xs k) (Econstr x w c xs k')

| Trans_proj :
  forall {x y w k k' n},
    M.get w L = None ->
    M.get x C = None ->
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
    (i0 : nat) (cs : list (option info_t))
    (w1 : web) (v1 : val) (w2 : web) (v2 : val) :=
    w1 = w2 /\
    match v1, v2 with
    | Vconstr t1 vs1, Vconstr t2 vs2 => (* TODO: REMOVE? *)
        t1 = t2 /\
        Forall2 (V' i0) vs1 vs2

    | Vfun f1 ρ1 xs1 e1, Vfun f2 ρ2 xs2 e2 =>
        length xs1 = length cs /\
        xs2 = nonconst_args xs1 cs /\

        forall j vs1 vs2 ρ3 ρ4,
          j <= i0 ->
          Forall wf_val vs1 ->
          Forall2 (V' j) (nonconst_args vs1 cs) vs2 ->
          correct_const_vals vs1 cs ->
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
    - destruct H as [Hw [Hlen [Heq HV]]].
      repeat (split; auto); intros.
      specialize (HV j0 vs1 vs2 ρ3 ρ4).
      rewrite normalize_step in *; try lia.
      eapply HV; eauto; try lia.
    - destruct H as [Hw [Hc HFV]]; subst.
      repeat (split; auto).
      rewrite normalize_step in *; try lia.
      eapply ExposedUtil.V_mono_Forall; eauto.
  Qed.

End VTransM.
Import VTransM.

Module EG := Exposed.ExposedVG LM VTransM.
Import EG.

(* Invariant of [C] *)
Definition C_inv Γ ρ :=
  forall x c w,
    M.get x C = Some (c, w) ->
    (x \in Γ) ->
    forall v,
      M.get x ρ = Some v ->
      v = (Tag w (Vconstr c [])).

Definition trans_correct Γ e1 e2 :=
  forall ex i ρ1 ρ2,
    C_inv Γ ρ1 ->
    G i Γ ρ1 (occurs_free e2) ρ2 ->
    E ex i ρ1 e1 ρ2 e2.

(* Lemmas about [const_args] and [nonconst_args] *)
Lemma const_args_length {A B}:
  forall (xs : list A) (vs : list B) cs,
    length xs = length vs ->
    length (const_args xs cs) = length (const_args vs cs).
Proof.
  intros xs.
  induction xs; simpl; intros;
    destruct vs; inv H;
    destruct cs; simpl; auto.
  destruct o; simpl; auto.
Qed.

Lemma nonconst_args_length {A B} :
  forall (xs : list A) (vs : list B) cs,
    length xs = length vs ->
    length (nonconst_args xs cs) = length (nonconst_args vs cs).
Proof.
  intros xs.
  induction xs; simpl; intros;
    destruct vs; inv H;
    destruct cs; simpl; auto.
  destruct o; simpl; auto.
Qed.

Lemma const_args_In {A} :
  forall {xs cs x},
    In x (@const_args A xs cs) ->
    In x xs.
Proof.
  intros xs.
  induction xs; simpl; intros.
  - destruct cs; auto.
  - destruct cs.
    + inv H.
      left; auto.
      right; auto.
    + destruct o.
      * inv H.
        left; auto.
        right; eauto.
      * right; eauto.
Qed.

Lemma nonconst_args_In {A} :
  forall {xs cs x},
    In x (@nonconst_args A xs cs) ->
    In x xs.
Proof.
  intros xs.
  induction xs; simpl; intros.
  - destruct cs; auto.
  - destruct cs.
    + inv H.
      left; auto.
      right; auto.
    + destruct o.
      * right; eauto.
      * inv H.
        left; auto.
        right; eauto.
Qed.

(* Invariants of [trans] *)
Lemma trans_env_inv {Γ e e'} :
  trans Γ e e' ->
  (occurs_free e) \subset Γ.
Proof.
  intros H.
  induction H; unfold Ensembles.Included, Ensembles.In, FromList in *; intros.
  - inv H0; auto.
  - inv H7.
    + specialize (IHtrans2 _ H15).
      inv IHtrans2; auto.
      inv H7; contradiction.
    + specialize (IHtrans1 _ H16).
      inv IHtrans1; try contradiction.
      inv H7; auto.
      inv H8; contradiction.
  - inv H4.
    + specialize (IHtrans2 _ H12).
      inv IHtrans2; auto.
      inv H4; contradiction.
    + specialize (IHtrans1 _ H13).
      inv IHtrans1; try contradiction.
      inv H4; auto.
      inv H5; contradiction.
  - inv H4; auto.
  - inv H2; auto.
  - inv H6; auto.
    specialize (IHtrans _ H14).
    inv IHtrans; auto.
    inv H6; contradiction.
  - inv H4; auto.
    specialize (IHtrans _ H12).
    inv IHtrans; auto.
    inv H4; contradiction.
  - inv H3; auto.
    specialize (IHtrans _ H11).
    inv IHtrans; auto.
    inv H3; contradiction.
  - inv H3; auto.
    specialize (IHtrans _ H11).
    inv IHtrans; auto.
    inv H3; contradiction.
  - inv H0; auto.
  - inv H3; auto.
Qed.

Lemma trans_fun_inv {f w e' k' e k }:
  (occurs_free e') \subset (occurs_free e) ->
  (occurs_free k') \subset (occurs_free k) ->
  forall {xs cs},
    length xs = length cs ->
    (occurs_free (Efun f w (nonconst_args xs cs) (bind_consts xs cs e') k')) \subset (occurs_free (Efun f w xs e k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros He Hk xs.
  induction xs; simpl; intros;
    destruct cs; inv H.
  - inv H0; auto.
  - destruct o.
    + destruct i.
      inv H0; auto.
      inv H9.
      inv H6.
      assert (occurs_free (Efun f w xs e k) x) by eauto.
      inv H; auto.
      apply Free_fun2; auto.
      intros Hc.
      apply H12.
      inv Hc; auto; contradiction.
    + inv H0; auto.
      assert (Ha : x <> a) by (intros Hc; subst; apply H8; apply in_eq).
      assert (Hcs : ~ In x (nonconst_args xs cs)) by (intros Hc; apply H8; apply in_cons; auto).
      assert (occurs_free (Efun f w xs e k) x) by eauto.
      inv H; auto.
      apply Free_fun2; auto.
      intros Hc.
      inv Hc; contradiction.
Qed.

Lemma trans_exp_inv {Γ e e'} :
  trans Γ e e' ->
  (occurs_free e') \subset (occurs_free e).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros H.
  induction H; intros; auto.
  - eapply trans_fun_inv; eauto.
  - inv H4; auto.
  - inv H4; auto.
    apply nonconst_args_In in H9; auto.
  - inv H6; auto.
    apply nonconst_args_In in H13; auto.
  - inv H4; auto.
  - inv H3; auto.
  - inv H3; auto.
  - inv H3; auto.
Qed.

(* Lemmas about [C_inv] *)
Lemma C_inv_set_None {x v Γ ρ} :
  C ! x = None ->
  C_inv Γ ρ ->
  C_inv (x |: Γ) (M.set x v ρ).
Proof.
  unfold C_inv.
  intros.
  destruct (M.elt_eq x x0); subst.
  - rewrite H1 in H; inv H.
  - rewrite M.gso in *; auto.
    erewrite <- H0; eauto.
    inv H2; auto.
    inv H4; contradiction.
Qed.

Lemma C_inv_set_Some {x c w Γ ρ} :
  C ! x = Some (c, w) ->
  C_inv Γ ρ ->
  C_inv (x |: Γ) (M.set x (Tag w (Vconstr c [])) ρ).
Proof.
  unfold C_inv.
  intros.
  destruct (M.elt_eq x x0); subst.
  - rewrite M.gss in *; auto.
    rewrite H1 in H; inv H; auto.
    inv H3; auto.
  - rewrite M.gso in *; auto.
    erewrite <- H0; eauto.
    inv H2; auto.
    inv H4; contradiction.
Qed.

Lemma C_inv_subset Γ1 Γ2 ρ :
  C_inv Γ1 ρ ->
  Γ2 \subset Γ1 ->
  C_inv Γ2 ρ.
Proof.
  unfold C_inv.
  intros.
  eapply H; eauto.
Qed.

Lemma C_inv_set_lists_None {xs vs Γ ρ1 ρ2} :
  Forall (fun x : positive => C ! x = None) xs ->
  set_lists xs vs ρ1 = Some ρ2 ->
  C_inv Γ ρ1 ->
  C_inv (FromList xs :|: Γ) ρ2.
Proof.
  intros H.
  revert vs ρ1 ρ2.
  induction H; simpl; intros.
  - destruct vs; try discriminate.
    inv H; auto.
    eapply C_inv_subset; eauto.
    eapply Union_Included; eauto.
    + eapply Included_trans.
      apply FromList_nil.
      apply Included_Empty_set; auto.
    + apply Included_refl.
  - destruct vs; try discriminate.
    destruct (set_lists l vs ρ1) eqn:Heq1; try discriminate.
    inv H1.
    apply C_inv_subset with (x |: (FromList l :|: Γ)); auto.
    apply C_inv_set_None; auto.
    eapply IHForall; eauto.
    apply FromList_cons_assoc.
Qed.

(* Environment Lemmas *)
Lemma G_get_list_trans {i Γ1 Γ2 ρ1 ρ2} :
  C_inv Γ1 ρ1 ->
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall xs cs vs1,
    (FromList xs) \subset Γ1 ->
    (FromList (nonconst_args xs cs)) \subset Γ2 ->
    length xs = length cs ->
    get_list xs ρ1 = Some vs1 ->
    correct_const_vars xs cs ->
    exists vs2,
      get_list (nonconst_args xs cs) ρ2 = Some vs2 /\
      Forall2 (V i) (nonconst_args vs1 cs) vs2 /\
      correct_const_vals vs1 cs.
Proof.
  unfold G.
  intros HC HG xs.
  induction xs; simpl; intros.
  - inv H2.
    destruct cs; simpl in *; try discriminate; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H2.
    destruct cs; inv H1.
    destruct o; simpl in *.
    + unfold Ensembles.Included, Ensembles.In, Dom_map, FromList, C_inv in *.
      destruct H3.
      destruct i0.
      edestruct IHxs as [vs2 [Heqvs2 [HVs HCs]]]; eauto.
      intros; apply H; apply in_cons; auto.
      eexists; repeat (split; eauto).
      eapply HC; eauto.
      apply H.
      apply in_eq.
    + edestruct (G_get HG) as [v2 [Heqv2 HV]]; eauto.
      apply H; apply in_eq.
      apply H0; apply in_eq.
      destruct H3.
      unfold Ensembles.Included, Ensembles.In, FromList in *.
      edestruct IHxs as [vs2 [Heqvs2 [HVs HCs]]]; eauto.
      intros.
      apply H; apply in_cons; auto.
      intros.
      apply H0; apply in_cons; auto.
      exists (v2 :: vs2); repeat split; auto.
      rewrite Heqv2; auto.
      rewrite Heqvs2; auto.
Qed.

Lemma G_set_lists_trans ρ1 {i Γ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  Γ2 \subset Γ1 ->
  forall {xs vs1 vs2 ρ3 ρ4 ρ5 cs},
    length xs = length cs ->
    Forall2 (V i) (nonconst_args vs1 cs) vs2 ->
    correct_const_vals vs1 cs ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists (nonconst_args xs cs) vs2 ρ2 = Some ρ4 ->
    set_lists (const_args xs cs) (const_args vs1 cs) ρ4 = Some ρ5 ->
    NoDup xs ->
    Disjoint _ (FromList xs) Γ1 ->
    G i (FromList xs :|: Γ1) ρ3 (FromList (const_args xs cs) :|: (FromList (nonconst_args xs cs) :|: Γ2)) ρ5.
Proof.
  intros HG HS xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct cs; try discriminate.
    simpl in *.
    destruct vs2; try discriminate.
    inv H0; inv H2; inv H3; inv H4.
    eapply G_subset; eauto.
    + rewrite FromList_nil.
      apply Union_Empty_set_neut_l.
    + apply Union_Included.
      rewrite FromList_nil.
      apply Included_Empty_set.
      rewrite FromList_nil.
      apply Union_Empty_set_neut_l.
  - destruct vs1; try discriminate.
    destruct cs; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    inv H; inv H2; inv H5.
    destruct o; simpl in *; try discriminate.
    + destruct (set_lists (const_args xs cs) (const_args vs1 cs) ρ4) eqn:Heq2; try discriminate.
      inv H4.
      destruct i0.
      destruct H1; subst.
      eapply G_subset with (Γ1 := (a |: (FromList xs :|: Γ1))) (Γ2 := a |: (FromList (const_args xs cs) :|: (FromList (nonconst_args xs cs) :|: Γ2))); eauto.
      eapply G_set; eauto.
      eapply IHxs; eauto.
      eapply Disjoint_FromList_cons_l; eauto.
      destruct i; simpl; repeat (split; auto);
        destruct (L ! w0); auto.
      unfold V_trans.
      repeat (split; auto).

      rewrite FromList_cons.
      rewrite Union_assoc.
      apply Included_refl.
      rewrite FromList_cons.
      rewrite Union_assoc with (s1 := [set a]).
      apply Included_refl.
    + destruct vs2; try discriminate.
      destruct (set_lists (nonconst_args xs cs) vs2 ρ2) eqn:Heq2; try discriminate.
      inv H0; inv H1; inv H3.
      edestruct (set_lists_set_inv H4) as [ρ5' [Heqr5' Heqr5]]; eauto; subst.
      intros Hc.
      apply H7.
      eapply const_args_In; eauto.
      eapply G_subset with (Γ1 := (a |: (FromList xs :|: Γ1))) (Γ2 := a |: (FromList (const_args xs cs) :|: (FromList (nonconst_args xs cs) :|: Γ2))); eauto.
      eapply G_set; eauto.
      eapply IHxs; eauto.
      eapply Disjoint_FromList_cons_l; eauto.
      rewrite FromList_cons.
      rewrite Union_assoc.
      apply Included_refl.
      rewrite FromList_cons.
      rewrite Union_assoc with (s1 := FromList (const_args xs cs)).
      rewrite Union_assoc with (s2 := [set a]).
      rewrite (Union_commut (FromList (const_args xs cs)) [set a]).
      rewrite Union_assoc with (s1 := [set a]).
      rewrite Union_assoc.
      apply Included_refl.
Qed.

(* Compatibility Lemmas *)
Lemma ret_compat Γ x :
  (x \in Γ) ->
  trans_correct Γ (Eret x) (Eret x).
Proof.
  unfold trans_correct, E, E', Ensembles.Included, Ensembles.In, Dom_map.
  intros.
  inv H3.
  - exists 0, OOT; split; simpl; eauto.
  - inv H4.
    edestruct (G_get H1) as [v2 [Heqv2 HV]]; eauto.
    exists 1, (Res v2); split; auto.
    + constructor; auto.
      destruct ex; auto.
      eapply V_exposed_res; eauto.
    + apply V_mono with i; try lia; auto.
Qed.

Lemma constr_compat Γ x w t xs k k' :
  L ! w = None ->
  (FromList xs \subset Γ) ->
  (match xs with
   | [] => M.get x C = Some (t, w)
   | _ => M.get x C = None
   end) ->
  trans_correct (x |: Γ) k k' ->
  trans_correct Γ (Econstr x w t xs k) (Econstr x w t xs k').
Proof.
  unfold trans_correct, E, E', Ensembles.Included, Ensembles.In, FromList.
  intros.
  inv H6.
  - exists 0, OOT; split; simpl; auto.
  - inv H7.
    destruct (G_get_list H4 xs vs) as [vs' [Heqvs' Hvs]]; auto.
    + unfold Ensembles.Included, Ensembles.In, FromList in *.
      intros; auto.
    + assert (wf_val (Tag w (Vconstr t vs))).
      {
        apply wf_val_Vconstr; auto.
        eapply V_wf_val_Forall_l; eauto.
      }

      assert (wf_val (Tag w (Vconstr t vs'))).
      {
        apply wf_val_Vconstr; auto.
        eapply V_wf_val_Forall_r; eauto.
        intros.
        eapply V_exposed_Forall; eauto.
      }

      assert (length vs = length vs').
      {
        unfold wval in *.
        rewrite <- (get_list_length_eq _ _ _ H15).
        rewrite <- (get_list_length_eq _ _ _ Heqvs'); auto.
      }

      edestruct (H2 ex i (M.set x (Tag w (Vconstr t vs)) ρ1) (M.set x (Tag w (Vconstr t vs')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk' Rr]]]; eauto; try lia.
      * destruct xs.
        -- simpl in H15.
           inv H15.
           apply C_inv_set_Some; auto.
        -- apply C_inv_set_None; auto.
      * eapply G_subset with (Γ2 := (x |: (occurs_free (Econstr x w t xs k')))).
        eapply G_set; eauto.
        -- destruct i; simpl; repeat (split; eauto);
             destruct (L ! w) eqn:Heq1; try discriminate;
             repeat split; auto.
           eapply V_mono_Forall; eauto; lia.
        -- apply Included_refl.
        -- apply free_constr_k_subset.
      * exists (S j2), r2; split; eauto.
        -- constructor; auto.
           econstructor; eauto.
           intros.
           eapply V_exposed_Forall; eauto.
           destruct ex; auto.
           eapply R_exposed; eauto.
        -- apply R_mono with (i - c); try lia; auto.
Qed.

Lemma proj_compat Γ x w i y e e' :
  L ! w = None ->
  C ! x = None ->
  (y \in Γ) ->
  trans_correct (x |: Γ) e e' ->
  trans_correct Γ (Eproj x w i y e) (Eproj x w i y e').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H6.
  - exists 0, OOT; split; simpl; auto.
  - inv H7.
    edestruct (G_get H4) as [v2 [Heqv2 HV]]; eauto.
    destruct v2.
    destruct v0; destruct i0;
      simpl in HV;
      destruct HV as [Hv1 [Hv2 HV]]; subst;
      destruct (L ! w) eqn:Heq1; try discriminate;
      destruct HV as [Hw HV]; subst; try contradiction.
    inv H5.
    rename l into vs'.
    rename c0 into t'.
    destruct HV as [Heqt HFvs]; subst.
    destruct (Forall2_nth_error H16 HFvs) as [v' [Heqv' HFv]].
    edestruct (H2 ex i0 (M.set x v ρ1) (M.set x v' ρ2)) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
    + apply C_inv_set_None; auto.
    + eapply G_subset with (Γ2 := (x |: (occurs_free (Eproj x w0 i y e')))).
      eapply G_set.
      eapply G_mono with (S i0); eauto; try lia.
      rewrite normalize_step in *; try lia; auto.
      apply Included_refl.
      apply free_proj_k_subset.
    + exists (S j2), r2; split.
      * constructor; eauto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * eapply R_mono; eauto; lia.
Qed.

Lemma app_compat Γ xs f w :
  L ! w = None ->
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  trans_correct Γ (Eapp f w xs) (Eapp f w xs).
Proof.
  unfold trans_correct, G, E, E'.
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
    destruct HV as [Hv1 [Hv2 HVv]]; subst.
    destruct (L ! w); try discriminate.
    destruct HVv as [Hw HVv]; subst.
    destruct v; try contradiction.
    destruct HVv as [Hlen HVv].

    edestruct (G_get_list H3 xs vs) as [vs2 [Heqvs2 Vvs]]; eauto.
    {
      unfold Ensembles.Included, Ensembles.In, FromList, Dom_map.
      intros; auto.
    }

    destruct (set_lists_length3 (M.set v (Tag w0 (Vfun v t l e0)) t) l vs2) as [ρ4 Heqρ4].
    unfold wval in *.
    rewrite <- (Forall2_length _ _ _ Vvs).
    rewrite <- (set_lists_length_eq _ _ _ _ H12); auto.

    assert (HE : E (exposedb w0) (i - (i - i)) ρ'' e ρ4 e0).
    {
      eapply (HVv i vs vs2); eauto.
      - intros.
        destruct H16; auto.
      - intros.
        destruct H16; auto.
        eapply V_exposed_Forall; eauto.
      - apply V_mono_Forall with (S i); auto; lia.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E in HE.
    destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
    exists (S j2), r2; split; eauto.
    constructor; auto.
    + eapply BStep_app; eauto.
      intros.
      destruct H16; auto.
      split.
      eapply V_exposed_Forall; eauto.
      eapply R_exposed; eauto.
    + destruct ex; auto.
      eapply R_exposed; eauto.
Qed.

Lemma app_compat_trans {xs cs} Γ f w :
  M.get w L = Some cs ->
  length xs = length cs ->
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  correct_const_vars xs cs ->
  trans_correct Γ (Eapp f w xs) (Eapp f w (nonconst_args xs cs)).
Proof.
  unfold trans_correct, G, E, E'.
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
    destruct HV as [Hw HV]; subst.
    destruct v; try contradiction.
    destruct HV as [Hlen [Hl HV]]; subst.
    inv H.
    edestruct (G_get_list_trans H4 H5 xs cs) as [vs2 [Heqvs2 [HVs HCs]]]; eauto.
    {
      unfold Ensembles.Included, Ensembles.In, FromList, Dom_map.
      intros; auto.
    }

    destruct (set_lists_length3 (M.set v (Tag w0 (Vfun v t (nonconst_args xs' cs) e1)) t) (nonconst_args xs' cs) vs2) as [ρ4 Heqρ4].
    unfold wval in *.
    rewrite <- (get_list_length_eq _ _ _ Heqvs2).
    apply nonconst_args_length; auto.
    rewrite (get_list_length_eq _ _ _ H13).
    rewrite (set_lists_length_eq _ _ _ _ H14); auto.

    assert (HE : E false (i - (i - i)) ρ'' e ρ4 e1).
    {
      eapply (HV i vs vs2); eauto.
      eapply (wf_env_get_list ρ1); eauto.
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

Lemma case_nil_compat Γ x w:
  (x \in Γ) ->
  trans_correct Γ (Ecase x w []) (Ecase x w []).
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H3.
  - exists 0, OOT; split; simpl; auto.
  - inv H4.
    inv H11.
Qed.

Lemma case_cons_compat Γ x w t e e' cl cl':
  L ! w = None ->
  (x \in Γ) ->
  trans_correct Γ e e' ->
  trans_correct Γ (Ecase x w cl) (Ecase x w cl') ->
  trans_correct Γ (Ecase x w ((t, e) :: cl)) (Ecase x w ((t, e') :: cl')).
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H6.
  - exists 0, OOT; split; simpl; eauto.
  - inv H7.
    edestruct (G_get H4) as [v2 [Heqv2 HV]]; eauto.
    destruct v2.
    destruct i.
    inv H5.
    destruct v; simpl in HV;
      destruct HV as [Hv1 [Hv2 HV]]; subst;
      destruct (L ! w) eqn:Heq1; try discriminate;
      destruct HV as [Hw HV]; subst; try contradiction.
    destruct HV as [Heqt HFvs]; subst.
    inv H14.
    + edestruct (H1 ex i ρ1 ρ2) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
      eapply G_subset with (Γ2 := (occurs_free (Ecase x w0 ((c0, e') :: cl')))); eauto.
      eapply G_mono; eauto.
      apply Included_refl.
      apply free_case_hd_subset.
      exists (S j2), r2; split.
      * constructor; eauto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * eapply R_mono; eauto; lia.
    + edestruct (H2 ex (S i) ρ1 ρ2) with (j1 := S c) (r1 := r1) as [j2 [r2 [He' HR]]]; eauto; try lia.
      eapply G_subset; eauto.
      apply Included_refl.
      apply free_case_tl_subset; auto.
      exists j2, r2; split; eauto.
      inv He'; auto.
      inv H6.
      rewrite Heqv2 in H14; inv H14; eauto.
Qed.

Lemma bstep_fuel_bind_consts :
  forall {xs vs cs ρ1 ρ2 ex e j r},
    NoDup xs ->
    length xs = length cs ->
    length vs = length cs ->
    wf_env ρ1 ->
    correct_const_vals vs cs ->
    set_lists (const_args xs cs) (const_args vs cs) ρ1 = Some ρ2 ->
    bstep_fuel ex ρ2 e j r ->
    bstep_fuel ex ρ1 (bind_consts xs cs e) (length (const_args xs cs) + j) r.
Proof.
  intro xs.
  induction xs; simpl; intros;
    destruct vs;
    destruct cs;
    simpl in *;
    inv H; inv H0; inv H1; inv H4; auto.
  destruct o; simpl in *; try discriminate.
  - destruct (set_lists (const_args xs cs) (const_args vs cs) ρ1) eqn:Heq1; try discriminate.
    inv H1.
    destruct i.
    destruct H3; subst.
    econstructor; simpl; eauto.
    econstructor; simpl; eauto.
    + eapply IHxs; eauto.
      eapply wf_env_set; eauto.
      eapply set_lists_set; eauto.
      intros Hc.
      apply H8.
      eapply const_args_In; eauto.
    + destruct ex; auto.
      inv H5; auto.
  - destruct H3.
    eapply IHxs; eauto.
Qed.

Lemma Vfun_V_trans Γ2 {f xs Γ1 e e'} :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  Γ2 \subset Γ1 ->
  NoDup (f :: xs) ->
  Disjoint _ (FromList (f :: xs)) Γ1 ->
  forall {i w cs ρ1 ρ2},
    L ! w = Some cs ->
    length xs = length cs ->

    wf_env ρ1 ->
    wf_env ρ2 ->

    C ! f = None ->
    Forall (fun x => C ! x = None) xs ->

    C_inv Γ1 ρ1 ->
    G i Γ1 ρ1 Γ2 ρ2 ->

    occurs_free e' \subset (FromList (const_args xs cs) :|: (FromList (nonconst_args xs cs) :|: (f |: Γ2))) ->
    V i (Tag w (Vfun f ρ1 xs e)) (Tag w (Vfun f ρ2 (nonconst_args xs cs) (bind_consts xs cs e'))).
Proof.
  unfold trans_correct.
  intros He HS Hn Hd i.
  induction i; simpl; intros; auto;
    repeat (split; auto);
    destruct (L ! w) eqn:Heq1; try discriminate; auto.
  inv H.
  repeat split; auto; intros.
  inv Hn.
  assert (Hlen : length xs = length vs1) by (eapply set_lists_length_eq; eauto).
  specialize (const_args_length xs vs1 cs Hlen); intros HClen.
  destruct (set_lists_length3 ρ4 _ _ HClen) as [ρ5 Heqρ5].

  assert (He' : E false (i - (i - j)) ρ3 e ρ5 e').
  {
    eapply He; eauto.
    - eapply C_inv_set_lists_None; eauto.
      eapply C_inv_set_None; eauto.
    - eapply G_subset with (Γ2 := (FromList (const_args xs cs) :|: (FromList (nonconst_args xs cs) :|: (f |: Γ2)))); eauto.
      + eapply G_set_lists_trans with (ρ1 := (M.set f (Tag w (Vfun f ρ1 xs e)) ρ1)); eauto.
        * eapply G_set; eauto.
          apply G_mono with (S i); eauto; try lia.
          apply V_mono with i; try lia.
          apply IHi; auto.
          eapply G_mono; eauto; lia.
        * apply Included_Union_compat; auto.
          apply Included_refl.
        * apply Disjoint_FromList_cons_r; auto.
          eapply Disjoint_FromList_cons_l; eauto.
      + apply Included_refl.
  }

  unfold E, E' in *.
  intros.
  edestruct He' as [j2 [r2 [Hev HR]]]; eauto.

  exists (length (const_args xs cs) + j2), r2; split; auto.
  eapply bstep_fuel_bind_consts; eauto.
  rewrite <- Hlen; auto.
  eapply wf_env_set_lists with (xs := (nonconst_args xs cs)) (vs := vs2)
                               (ρ := (M.set f (Tag w (Vfun f ρ2 (nonconst_args xs cs) (bind_consts xs cs e'))) ρ2)); eauto.
  eapply wf_env_set; eauto.
  eapply V_wf_val_Forall_r; eauto.
Qed.

Lemma free_fun_bind_consts_e_subset {e f w k} :
  forall {xs cs},
    length xs = length cs ->
    occurs_free e \subset
      (FromList (const_args xs cs)
         :|: (FromList (nonconst_args xs cs)
                :|: (f |: occurs_free
                       (Efun f w (nonconst_args xs cs) (bind_consts xs cs e) k)))).
Proof.
  unfold Ensembles.Included, Ensembles.In, FromList.
  intros xs.
  induction xs; simpl; intros cs Hlen; intros.
  - destruct cs; simpl; inv Hlen;
      apply Union_intror;
      apply Union_intror;
      unfold Ensembles.In;
      destruct (var_dec f x); subst;
      solve [ apply Union_introl; auto |
              apply Union_intror; auto ].
  - destruct cs; simpl; inv Hlen.
    destruct o.
    + destruct i.
      destruct (var_dec x a); subst.
      apply Union_introl; auto.
      apply in_eq.

      specialize (IHxs _ H1 _ H).
      inv IHxs.
      apply Union_introl.
      apply in_cons; auto.

      apply Union_intror.
      inv H0.
      apply Union_introl; auto.

      apply Union_intror.
      inv H2.
      apply Union_introl; auto.

      apply Union_intror.
      inv H0; auto.
    + specialize (IHxs _ H1 _ H).
      inv IHxs.
      apply Union_introl; auto.

      apply Union_intror.
      destruct (var_dec x a); subst.
      apply Union_introl.
      apply in_eq.

      inv H0.
      apply Union_introl; auto.
      apply in_cons; auto.

      apply Union_intror.
      inv H2.
      apply Union_introl; auto.

      apply Union_intror; auto.
      inv H0; auto.
      apply Free_fun2; auto.
      intros Hc.
      apply H9.
      inv Hc; auto; contradiction.
Qed.

Lemma fun_compat_trans {Γ1 e e' cs k k'} f w xs :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  trans_correct (f |: Γ1) k k' ->

  M.get w L = Some cs ->
  length xs = length cs ->

  NoDup (f :: xs) ->
  Disjoint _ (FromList (f :: xs)) Γ1 ->

  M.get f C = None ->
  Forall (fun x => M.get x C = None) xs ->

  (occurs_free (Efun f w (nonconst_args xs cs) (bind_consts xs cs e') k')) \subset Γ1 ->

  trans_correct Γ1 (Efun f w xs e k) (Efun f w (nonconst_args xs cs) (bind_consts xs cs e') k').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H11.
  - exists 0, OOT; split; simpl; eauto.
  - inv H12.
    edestruct (H0 ex (i - 1) (M.set f (Tag w (Vfun f ρ1 xs e)) ρ1) (M.set f (Tag w (Vfun f ρ2 (nonconst_args xs cs) (bind_consts xs cs e'))) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + apply C_inv_set_None; auto.
    + eapply G_subset with (Γ2 := (f |: (occurs_free (Efun f w (nonconst_args xs cs) (bind_consts xs cs e') k')))); eauto.
      * eapply G_set; eauto.
        -- eapply G_mono with i; eauto; try lia.
        -- eapply Vfun_V_trans; eauto.
           ++ eapply G_wf_env_l; eauto.
           ++ eapply G_wf_env_r; eauto.
           ++ apply G_mono with i; eauto; try lia.
           ++ apply free_fun_bind_consts_e_subset; eauto.
      * apply Included_refl.
      * apply free_fun_k_subset.
    + exists (S j2), r2; split; auto.
      * constructor; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma Vfun_V Γ1 f xs e e' :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  forall {i Γ2 ρ1 ρ2 w},
    L ! w = None ->

    wf_env ρ1 ->
    wf_env ρ2 ->

    C ! f = None ->
    Forall (fun x => C ! x = None) xs ->

    C_inv Γ1 ρ1 ->
    G i Γ1 ρ1 Γ2 ρ2 ->
    occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
    V i (Tag w (Vfun f ρ1 xs e)) (Tag w (Vfun f ρ2 xs e')).
Proof.
  unfold trans_correct.
  intros He i.
  induction i; simpl; intros; auto;
    repeat (split; auto); intros;
    destruct (L ! w) eqn:Heq1; try discriminate; auto.
  repeat (split; auto); intros.
  apply (He (exposedb w) (i - (i - j)) ρ3 ρ4); auto.
  - eapply C_inv_set_lists_None; eauto.
    eapply C_inv_set_None; eauto.
  - eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))).
    eapply G_set_lists; eauto.
    eapply G_set; eauto.
    + apply G_mono with (S i); eauto; lia.
    + apply V_mono with i; try lia.
      eapply IHi with (Γ2 := Γ2); eauto.
      apply G_mono with (S i); eauto; lia.
    + apply Included_refl.
    + auto.
Qed.

Lemma fun_compat Γ e e' k k' f w xs :
  L ! w = None ->
  C ! f = None ->
  Forall (fun x => M.get x C = None) xs ->
  trans_correct (FromList xs :|: (f |: Γ)) e e' ->
  trans_correct (f |: Γ) k k' ->
  trans_correct Γ (Efun f w xs e k) (Efun f w xs e' k').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H7.
  - exists 0, OOT; split; simpl; eauto.
  - inv H8.
    edestruct (H3 ex (i - 1) (M.set f (Tag w (Vfun f ρ1 xs e)) ρ1) (M.set f (Tag w (Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply C_inv_set_None; eauto.
    + eapply G_subset with (Γ2 := (f |: occurs_free (Efun f w xs e' k'))).
      eapply G_set; eauto.
      apply G_mono with i; eauto; lia.
      * eapply Vfun_V; eauto.
        -- eapply G_wf_env_l; eauto.
        -- eapply G_wf_env_r; eauto.
        -- apply G_mono with i; eauto; lia.
        -- apply free_fun_e_subset.
      * apply Included_refl.
      * apply free_fun_k_subset.
    + exists (S j2), r2; split; auto.
      * constructor; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      * apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma letapp_compat_trans {xs cs} Γ f x w k k' :
  M.get w L = Some cs ->
  length xs = length cs ->
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  trans_correct (x |: Γ) k k' ->
  C ! x = None ->
  correct_const_vars xs cs ->
  trans_correct Γ (Eletapp x f w xs k) (Eletapp x f w (nonconst_args xs cs) k').
Proof.
  intros.
  specialize (app_compat_trans Γ f w H H0 H1 H2 H5); intros Ha.
  unfold trans_correct, E, E' in *.
  intros.

  assert (HGa : G i Γ ρ1 (occurs_free (Eapp f w (nonconst_args xs cs))) ρ2).
  {
    eapply G_subset; eauto.
    apply Included_refl.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H10; auto.
  }

  specialize (Ha (exposedb w) _ _ _ H6 HGa).
  inv H9.
  - exists 0, OOT; split; simpl; auto.
  - inv H10.
    + destruct (Ha (S c0) (Res v)) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      * constructor; auto.
        -- eapply BStep_app; eauto.
           intros.
           destruct H22; auto.
        -- destruct (exposed_reflect w); auto.
           destruct H22; auto.
      * simpl in Rra.
        destruct ra; try contradiction.
        rename w0 into v0.
        edestruct (H3 ex (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
        -- eapply C_inv_set_None; eauto.
        -- eapply G_subset with (Γ2 := (x |: (occurs_free (Eletapp x f w (nonconst_args xs cs) k')))).
           eapply G_set; eauto.
           apply G_mono with i; try lia; eauto.
           apply Included_refl.
           apply free_letapp_k_subset.
        -- exists (j1 + j2), r2; split.
           ++ inv Hap.
              inv H9.
              assert ((S c + j2) = S (c + j2)) by lia.
              rewrite H9.
              constructor; auto.
              ** eapply BStep_letapp_Res; eauto.
                 intros.
                 destruct H27; auto.
                 inv H14.
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
      inv H9; eauto.
      constructor; auto.
      eapply BStep_letapp_OOT; eauto.
      intros.
      destruct H26; auto.
Qed.

Lemma letapp_compat Γ k k' w xs x f :
  L ! w = None ->
  C ! x = None ->
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  trans_correct (x |: Γ) k k' ->
  trans_correct Γ (Eletapp x f w xs k) (Eletapp x f w xs k').
Proof.
  intros.
  specialize (app_compat Γ xs f w H H1 H2); intros Ha.
  unfold trans_correct, E, E' in *.
  intros.

  assert (HG' : G i Γ ρ1 (occurs_free (Eapp f w xs)) ρ2).
  {
    eapply G_subset with (Γ2 := (occurs_free (Eletapp x f w xs k'))); eauto.
    apply Included_refl.
    apply free_app_letapp.
  }

  inv H7.
  - exists 0, OOT; split; simpl; auto.
  - inv H8.
    + destruct (Ha (exposedb w) i ρ1 ρ2) with (j1 := (S c0)) (r1 := (Res v)) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
      * constructor; auto.
        eapply BStep_app; eauto.
        intros.
        destruct H20; auto.
        destruct (exposed_reflect w); try contradiction; auto.
        destruct H20; auto.
      * simpl in HR.
        destruct r2; try contradiction.
        rename w0 into v0.
        inv Hr1.
        edestruct (H3 ex (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
        -- eapply C_inv_set_None; eauto.
        -- eapply G_subset with (Γ2 := (x |: (occurs_free (Eletapp x f w xs k')))).
           eapply G_set; eauto.
           apply G_mono with i; try lia; eauto.
           apply Included_refl.
           apply free_letapp_k_subset.
        -- exists ((S c) + j2), r2; split.
           ++ inv H7.
              assert (Hc : (S c + j2) = S (c + j2)) by lia.
              rewrite Hc.
              constructor; auto.
              ** eapply BStep_letapp_Res; eauto.
                 intros.
                 destruct H25; auto.
                 inv H11.
                 split; auto.
              ** destruct ex; auto.
                 eapply R_exposed; eauto.
           ++ apply R_mono with (i - S c0 - c'); try lia; auto.
    + destruct (Ha (exposedb w) i ρ1 ρ2) with (j1 := (S c)) (r1 := OOT) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
      constructor; eauto.
      destruct (exposed_reflect w); try contradiction; auto.
      exists j2, r2.
      destruct r2; try contradiction.
      split; auto.
      inv Hr1; eauto.
      inv H7; eauto.
      constructor; auto.
      eapply BStep_letapp_OOT; eauto.
      * intros.
        destruct H24; auto.
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

Definition C_inv_top Γ :=
  forall x,
    (x \in Γ) ->
    M.get x C = None.

Lemma C_inv_top_C_inv Γ ρ :
  C_inv_top Γ ->
  C_inv Γ ρ.
Proof.
  unfold C_inv_top, C_inv.
  intros.
  rewrite (H _ H1) in H0; inv H0.
Qed.

Definition trans_correct_top etop etop' :=
  forall i ρ1 ρ2,
    G_top i (occurs_free etop) ρ1 (occurs_free etop') ρ2 ->
    E true i ρ1 etop ρ2 etop'.

Theorem top etop etop' :
  C_inv_top (occurs_free etop) ->
  trans (occurs_free etop) etop etop' ->
  trans_correct_top etop etop'.
Proof.
  unfold trans_correct_top.
  intros.
  specialize (fundamental_property H0);
    unfold trans_correct; intros.
  eapply H2; auto.
  - eapply C_inv_top_C_inv; eauto.
  - eapply G_top_G; eauto.
Qed.

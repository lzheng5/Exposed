From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Util W0 ANF1 ANF Checking.

Module AS := ANF1.
Module AT := ANF.

(* Checking Semantics -> Web Semantics *)

(* Specification *)
Inductive trans (W : web_map) (Γ : vars) : AS.exp -> AT.exp -> Prop :=
| Trans_ret :
  forall {x},
    (x \in Γ) ->
    trans W Γ (AS.Eret x) (AT.Eret x)

| Trans_fun :
  forall {l w f xs e0 k0 e1 k1 },
    W ! l = Some w ->
    trans W (FromList xs :|: (f |: Γ)) e0 e1 ->
    trans W (f |: Γ) k0 k1 ->
    trans W Γ (AS.Efun f l xs e0 k0) (AT.Efun f w xs e1 k1)

| Trans_app :
  forall {f xs l w},
    W ! l = Some w ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans W Γ (AS.Eapp f l xs) (AT.Eapp f w xs)

| Trans_letapp :
  forall {x f xs k0 k1 l w},
    W ! l = Some w ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans W (x |: Γ) k0 k1 ->
    trans W Γ (AS.Eletapp x f l xs k0) (AT.Eletapp x f w xs k1)

| Trans_constr :
  forall {x t xs k0 k1 l w},
    W ! l = Some w ->
    (FromList xs \subset Γ) ->
    trans W (x |: Γ) k0 k1 ->
    trans W Γ (AS.Econstr x l t xs k0) (AT.Econstr x w t xs k1)

| Trans_proj :
  forall {x y k0 k1 n l w},
    W ! l = Some w ->
    (y \in Γ) ->
    trans W (x |: Γ) k0 k1 ->
    trans W Γ (AS.Eproj x l n y k0) (AT.Eproj x w n y k1)

| Trans_case_nil :
  forall {l w x},
    W ! l = Some w ->
    (x \in Γ) ->
    trans W Γ (AS.Ecase x l []) (AT.Ecase x w [])

| Trans_case_cons :
  forall {x l w e0 e1 t cl0 cl1},
    W ! l = Some w ->
    (x \in Γ) ->
    trans W Γ e0 e1 ->
    trans W Γ (AS.Ecase x l cl0) (AT.Ecase x w cl1) ->
    trans W Γ (AS.Ecase x l ((t, e0) :: cl0)) (AT.Ecase x w ((t, e1) :: cl1)).

Hint Constructors trans : core.

Lemma trans_exp_inv {W Γ e e'} :
  trans W Γ e e' ->
  (AT.occurs_free e') \subset (AS.occurs_free e).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros H.
  induction H; simpl; intros; auto.
  - inv H0; auto.
  - inv H2; auto.
  - inv H2; auto.
  - inv H3; auto.
  - inv H2; auto.
  - inv H2; auto.
  - inv H1; auto.
  - inv H3; auto.
Qed.

(* Cross-language Logical Relations *)
Definition R' (P : nat -> clval -> AT.wval -> Prop) (i : nat) (r1 : cres) (r2 : AT.res) :=
  match r1, r2 with
  | COOT, AT.OOT => True
  | CRes v1, AT.Res v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> clval -> AT.wval -> Prop) (W : web_map) (ex : bool) (i : nat) (ρ1 : cenv) (e1 : AS.exp) (ρ2 : AT.env) (e2 : AT.exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    cbstep_fuel W ex ρ1 e1 j1 r1 ->
    exists j2 r2,
      AT.bstep_fuel ex ρ2 e2 j2 r2 /\
        R' P (i - j1) r1 r2.

(*
  (* W is sound for a particular program trace of e *)
  Definition web_map_sound W ex ρ1 ρ2 e :=
    forall i r1,
      AS.bstep_fuel ρ1 e i r1 ->
      refine_env ρ1 ρ2 ->
      exists r2,
        cbstep_fuel W ex ρ2 e i r2 /\
        refine_res r1 r2.
 *)

Fixpoint V (i : nat) (cv : clval) (wv : AT.wval) {struct i} : Prop :=
  wf_cval cv /\
    wf_val wv /\
    match cv, wv with
    | CTAG _ l1 W v1, AT.TAG _ w2 v2 =>
        W ! l1 = Some w2 /\
          (w2 \in Exposed -> exposed wv) /\
          match v1, v2 with
          | CVconstr c1 vs1, AT.Vconstr c2 vs2 =>
              c1 = c2 /\
                length vs1 = length vs2 /\
                match i with
                | 0 => True
                | S i0 => Forall2 (V i0) vs1 vs2
                end

          | CVfun f1 ρ1 xs1 e1, AT.Vfun f2 ρ2 xs2 e2 =>
              length xs1 = length xs2 /\
                match i with
                | 0 => True
                | S i0 =>
                    forall j vs1 vs2 ρ3 ρ4,
                      j <= i0 ->
                      (w2 \in Exposed -> Forall exposed vs2) ->
                      Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                      set_lists xs1 vs1 (M.set f1 (CTag l1 W (CVfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                      set_lists xs2 vs2 (M.set f2 (AT.Tag w2 (AT.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                      E' V W (exposedb w2) (i0 - (i0 - j)) ρ3 e1 ρ4 e2
                end

          | _, _ => False
          end
    end.

Definition R := (R' V).

Definition E := (E' V).

(* Lemmas about [wf_cval], [wf_cres], and [wf_cenv] *)
Lemma V_wf_cval_l {i v1 v2}:
  V i v1 v2 ->
  wf_cval v1.
Proof. intros; destruct i; simpl in *; fcrush. Qed.

Lemma V_wf_cval_Forall_l {i vs1 vs2} :
  Forall2 (V i) vs1 vs2 ->
  Forall wf_cval vs1.
Proof. intros H. induction H; eauto using V_wf_cval_l. Qed.

Lemma V_wf_cres_l {i v1 v2}:
  V i v1 v2 ->
  wf_cres (CRes v1).
Proof. intros; eauto using V_wf_cval_l. Qed.

Lemma R_wf_cres_l {i r1 r2} :
  R i r1 r2 ->
  wf_cres r1.
Proof.
  unfold R, R'.
  intros.
  destruct r1; destruct r2; try contradiction;
    eauto using V_wf_cval_l.
Qed.

Lemma V_wf_val_r {i v1 v2}:
  V i v1 v2 ->
  wf_val v2.
Proof. intros; destruct i; simpl in *; fcrush. Qed.

Lemma V_wf_val_Forall_r {i vs1 vs2} :
  Forall2 (V i) vs1 vs2 ->
  Forall wf_val vs2.
Proof. intros H. induction H; eauto using V_wf_val_r. Qed.

Lemma V_wf_res_r {i v1 v2}:
  V i v1 v2 ->
  wf_res (AT.Res v2).
Proof. intros; eauto using V_wf_val_r; eauto. Qed.

Lemma R_wf_res_r {i r1 r2} :
  R i r1 r2 ->
  wf_res r2.
Proof.
  unfold R.
  intros.
  destruct r1; destruct r2; try contradiction;
    eauto using V_wf_val_r.
Qed.

(* Inversion Lemmas *)
Lemma R_res_inv_l i v1 r2 :
  R i (CRes v1) r2 ->
  exists v2, r2 = AT.Res v2 /\ V i v1 v2.
Proof. intros. fcrush. Qed.

(* Exposed Lemmas *)
Lemma V_exposed v1 {i v2} :
  V i v1 v2 ->
  to_exposed v1 ->
  exposed v2.
Proof.
  intros.
  destruct v1; destruct v2;
    destruct i; try contradiction; auto;
    simpl in *;
    rename w into W;
    destruct H as [Hv1 [Hv2 [HW [Hex _]]]]; subst;
    inv H0; invc; eauto.
Qed.

Lemma V_exposed_Forall : forall {i vs1 vs2},
    Forall2 (V i) vs1 vs2 ->
    Forall to_exposed vs1 ->
    Forall exposed vs2.
Proof.
  intros.
  induction H; intros; auto.
  inv H0.
  eauto using V_exposed.
Qed.

Lemma V_exposed_res : forall {i v1 v2},
    V i v1 v2 ->
    to_exposed_cres (CRes v1) ->
    exposed_res (AT.Res v2).
Proof.
  intros.
  inv H0.
  constructor.
  eapply V_exposed; eauto.
Qed.

Lemma R_exposed : forall {i r1 r2},
    R i r1 r2 ->
    to_exposed_cres r1 ->
    exposed_res r2.
Proof.
  unfold R.
  intros.
  destruct r1;
    destruct r2;
    try contradiction; auto.
  eapply V_exposed_res; eauto.
Qed.

(* Environment Relation *)
Definition G i Γ1 ρ1 Γ2 ρ2 :=
  wf_cenv ρ1 /\
  wf_env ρ2 /\
    forall x,
      (x \in Γ1) ->
      forall v1,
        M.get x ρ1 = Some v1 ->
        ((x \in Γ2) ->
         exists v2,
           M.get x ρ2 = Some v2 /\
             V i v1 v2).

(* Environment Lemmas *)
Lemma G_subset Γ1 Γ2 {i ρ1 Γ3 ρ2 Γ4}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  Γ3 \subset Γ1 ->
  Γ4 \subset Γ2 ->
  G i Γ3 ρ1 Γ4 ρ2.
Proof. unfold G. fcrush. Qed.

Lemma G_wf_cenv_l {i Γ1 ρ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  wf_cenv ρ1.
Proof. unfold G. fcrush. Qed.

Lemma G_wf_env_r {i Γ1 ρ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  wf_env ρ2.
Proof. unfold G. fcrush. Qed.

Lemma G_get {Γ1 Γ2 i ρ1 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall x v1,
    (x \in Γ1) ->
    (x \in Γ2) ->
    M.get x ρ1 = Some v1 ->
    exists v2,
      M.get x ρ2 = Some v2 /\
        V i v1 v2.
Proof. unfold G. fcrush. Qed.

Lemma G_get_list {i Γ1 ρ1 Γ2 ρ2} :
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall xs vs1,
    (FromList xs) \subset Γ1 ->
    (FromList xs) \subset Γ2 ->
    get_list xs ρ1 = Some vs1 ->
    exists vs2,
      get_list xs ρ2 = Some vs2 /\
        Forall2 (V i) vs1 vs2.
Proof.
  intros HG xs.
  induction xs; simpl; intros.
  - inv H1; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H1.
    unfold Ensembles.Included, Ensembles.In in *.
    edestruct (G_get HG) as [v2 [Heqv2 HV]]; eauto.
    eapply (H a).
    apply in_eq.
    apply H0.
    apply in_eq.
    edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
    + intros.
      apply H.
      apply in_cons; auto.
    + intros.
      apply H0.
      apply in_cons; auto.
    + rewrite Heqvs2.
      exists (v2 :: vs2); split; auto.
      rewrite Heqv2; auto.
Qed.

Lemma G_set {i Γ1 ρ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall {x v1 v2},
    V i v1 v2 ->
    G i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
Proof.
  unfold G.
  intro HG.
  pose proof HG as HG'.
  intros.

  destruct HG as [Hwf [Hwfv HG]].
  split.
  eapply wf_cenv_set; eauto.
  eapply V_wf_cval_l; eauto.

  split.
  eapply wf_env_set; eauto.
  eapply V_wf_val_r; eauto.

  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss in *.
    fcrush.
  - rewrite M.gso in *; auto.
    eapply G_get; eauto; fcrush.
Qed.

Lemma G_set_lists {i Γ1 ρ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 (V i) vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    G i (FromList xs :|: Γ1) ρ3 (FromList xs :|: Γ2) ρ4.
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
    eapply G_subset with (Γ1 := (a |: (FromList xs :|: Γ1))) (Γ2 := (a |: (FromList xs :|: Γ2))); eauto;
      try (normalize_sets;
           rewrite Union_assoc;
           apply Included_refl).
    eapply G_set; eauto.
Qed.

(* Monotonicity Lemmas *)
Lemma V_mono_Forall_aux :
  forall i j (V : nat -> clval -> AT.wval -> Prop) vs1 vs2,
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
    rename w into W;
    destruct H0 as [Hwf [Hwfv [Heql [Hex HV]]]]; subst.
  - destruct v; destruct c; fcrush.
  - fcrush.
  - repeat (split; auto).
    destruct c; destruct v; try contradiction.
    + destruct HV.
      fcrush.
    + destruct HV as [Hc [Hlen HV]]; subst.
      fcrush.
  - repeat (split; auto).
    destruct c; destruct v; try contradiction.
    + destruct HV as [Hlen HV]; subst.
      repeat (split; eauto); intros.
      specialize (HV j0 vs1 vs2 ρ3 ρ4).
      rewrite normalize_step in *; try lia.
      apply HV; eauto; lia.
    + destruct HV as [Heqc [Hlen HV]]; subst.
      repeat (split; eauto).
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

Lemma E_mono {W ex ρ1 ρ2 e1 e2} i j:
  E W ex i ρ1 e1 ρ2 e2 ->
  j <= i ->
  E W ex j ρ1 e1 ρ2 e2.
Proof.
  unfold E, R, E', R'.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; eauto.
  apply R_mono with (i - j1); try lia; auto.
Qed.

Lemma G_mono {Γ1 Γ2 ρ1 ρ2} i j:
  G i Γ1 ρ1 Γ2 ρ2 ->
  j <= i ->
  G j Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G.
  intros.
  destruct H as [Hwf [Hwf2 HG]].
  repeat (split; auto); intros.
  edestruct HG as [v2 [Heqv2 HV]]; eauto.
  eexists; repeat (split; eauto).
  eauto using V_mono.
Qed.

(* Compatibility Lemmas *)
Definition trans_correct W Γ e1 e2 :=
  forall ex i ρ1 ρ2,
    G i Γ ρ1 (AT.occurs_free e2) ρ2 ->
    E W ex i ρ1 e1 ρ2 e2.

Lemma ret_compat W Γ x :
  (x \in Γ) ->
  trans_correct W Γ (AS.Eret x) (AT.Eret x).
Proof.
  unfold trans_correct, E, E', R, R', Ensembles.Included, Ensembles.In.
  intros; simpl.

  inv H2.
  - exists 0, AT.OOT; split; auto.
  - inv H3.
    edestruct (G_get H0) as [v2 [Heqv2 HV]]; eauto.
    exists (S 0), (AT.Res v2); split; eauto.
    econstructor; eauto.
    destruct ex; auto.
    eapply V_exposed_res; eauto.
    eapply V_mono; eauto; lia.
Qed.

Lemma Vfun_V W Γ1 f l w xs e1 e2  :
  W ! l = Some w ->
  trans_correct W (FromList xs :|: (f |: Γ1)) e1 e2 ->
  forall {i Γ2 ρ1 ρ2},
    wf_cval (CTag l W (CVfun f ρ1 xs e1)) ->
    wf_val (AT.Tag w (AT.Vfun f ρ2 xs e2)) ->
    G i Γ1 ρ1 Γ2 ρ2 ->
    AT.occurs_free e2 \subset (FromList xs :|: (f |: Γ2)) ->
    V i (CTag l W (CVfun f ρ1 xs e1)) (AT.Tag w (AT.Vfun f ρ2 xs e2)).
Proof.
  unfold well_annotated.
  intros HW He i.
  induction i; simpl; intros; auto;
    repeat (split; auto);
    intros; (repeat split; auto).
  apply (He _ (i - (i - j)) ρ3 ρ4); auto.
  eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))); eauto.
  eapply G_set_lists; eauto.
  eapply G_set; eauto.
  + eapply G_mono with (S i); eauto; lia.
  + apply V_mono with i; try lia.
    eapply IHi with (Γ2 := Γ2); eauto.
    apply G_mono with (S i); eauto; lia.
  + apply Included_refl.
Qed.

Lemma fun_compat W Γ e1 e2 k1 k2 f l w xs :
  W ! l = Some w ->
  trans_correct W (FromList xs :|: (f |: Γ)) e1 e2 ->
  trans_correct W (f |: Γ) k1 k2 ->
  trans_correct W Γ (AS.Efun f l xs e1 k1) (AT.Efun f w xs e2 k2).
Proof.
  unfold trans_correct, E, E'.
  intros HWl He Hk.
  intros.
  assert (Hcwf : wf_cenv ρ1) by eauto using G_wf_cenv_l.
  assert (Hwf : wf_env ρ2) by eauto using G_wf_env_r.

  inv H1.
  - exists 0, AT.OOT; split; simpl; eauto.
  - inv H2; invc.
    edestruct (Hk ex (i - 1) (M.set f (CTag l W (CVfun f ρ1 xs e1)) ρ1) (M.set f (AT.Tag w0 (AT.Vfun f ρ2 xs e2)) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_subset with (Γ2 := (f |: AT.occurs_free (AT.Efun f w0 xs e2 k2))).
      eapply G_set; eauto.
      eapply G_mono with i; eauto; lia.
      * eapply Vfun_V; eauto.
        -- apply G_mono with i; eauto; lia.
        -- apply AT.free_fun_e_subset.
      * apply Included_refl.
      * apply AT.free_fun_k_subset.
    + exists (S j2), r2; split; auto.
      * econstructor; simpl; eauto.
        destruct ex; simpl in *; auto.
        destruct r2; fcrush.
      * eapply R_mono; eauto; lia.
Qed.

Lemma app_compat W Γ xs f l w :
  (W ! l = Some w) ->
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  trans_correct W Γ (AS.Eapp f l xs) (AT.Eapp f w xs).
Proof.
  unfold trans_correct, E, E'.
  intros HW Hf Hxs.
  intros; simpl.
  assert (Hcwfρ : wf_cenv ρ1) by eauto using G_wf_cenv_l.
  assert (Hwfρ : wf_env ρ2) by eauto using G_wf_env_r.

  inv H1.
  - exists 0, AT.OOT; split; simpl; auto.
  - inv H2; invc.
    edestruct (G_get H f) as [fv2 [Heqfv2 HV]]; eauto.
    destruct i.
    inv H0.
    destruct fv2; simpl in HV; invc;
      destruct HV as [Hcwf [Hwf [Hw [Hex HV]]]]; subst; invc;
      destruct v; try contradiction.
    destruct HV as [Hlen HV].

    edestruct (G_get_list H xs vs) as [vs2 [Heqvs2 Vvs]]; eauto; invc.
    eapply AT.free_app_xs_subset; eauto.

    destruct (set_lists_length3 (M.set v (AT.Tag w (AT.Vfun v t l0 e0)) t) l0 vs2) as [ρ4 Heqρ4].
    unfold clval in *.
    unfold wval in *.
    rewrite <- (Forall2_length _ _ _ Vvs).
    rewrite <- (set_lists_length_eq _ _ _ _ H8); auto.

    assert (HE : E W' (exposedb w) (i - (i - i)) ρ'' e ρ4 e0).
    {
      eapply (HV i vs vs2); eauto.
      intros.
      destruct H13; auto.
      eapply V_exposed_Forall; eauto.
      apply V_mono_Forall with (S i); auto; lia.
    }
    apply (E_mono _ i) in HE; try lia.
    unfold E, E' in HE.
    destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
    exists (S j2), r2; split; eauto.
    econstructor; eauto.
    econstructor; eauto.
    intros.
    destruct H13; auto.
    split.
    eapply V_exposed_Forall; eauto.
    eapply R_exposed; eauto.
    destruct ex; auto.
    eapply R_exposed; eauto.
Qed.

Lemma case_nil_compat W Γ x l w :
  W ! l = Some w ->
  (x \in Γ) ->
  trans_correct W Γ (AS.Ecase x l []) (AT.Ecase x w []).
Proof.
  unfold trans_correct, E, E'.
  intros HWl Hx.
  intros; simpl.
  inv H1; fcrush.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {W Γ e1 e2}:
  trans W Γ e1 e2 -> trans_correct W Γ e1 e2.
Proof.
  intros.
  induction H; intros.
  - eapply ret_compat; eauto.
  - eapply fun_compat; eauto.
  - eapply app_compat; eauto.
  - admit.  (* eapply letapp_compat; eauto.*)
  - admit. (* eapply constr_compat; eauto. *)
  - admit. (* eapply proj_compat; eauto. *)
  - eapply case_nil_compat; eauto.
  - admit. (* eapply case_cons_compat; eauto.*)
Admitted.

(* Top Level *)

Module AC := Checking.

Definition E_top' (P : nat -> clval -> AT.wval -> Prop) (i : nat) (ρ1 : cenv) (e1 : AC.cexp) (ρ2 : AT.env) (e2 : AT.exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    cbstep_top_fuel ρ1 e1 j1 r1 ->
    exists j2 r2,
      AT.bstep_fuel true ρ2 e2 j2 r2 /\
        R' P (i - j1) r1 r2.

Fixpoint V_top (i : nat) (cv : clval) (wv : AT.wval) {struct i} : Prop :=
  wf_cval cv /\
    wf_val wv /\
    exposed wv /\
    match cv, wv with
    | CTAG _ l1 W v1, AT.TAG _ w v2 =>
          W ! l1 = Some w /\
          match v1, v2 with
          | CVconstr c1 vs1, AT.Vconstr c2 vs2 =>
              c1 = c2 /\
                length vs1 = length vs2 /\
                match i with
                | 0 => True
                | S i0 => Forall2 (V_top i0) vs1 vs2
                end

          | CVfun f1 ρ1 xs1 e1, AT.Vfun f2 ρ2 xs2 e2 =>
              length xs1 = length xs2 /\
                match i with
                | 0 => True
                | S i0 =>
                    forall j vs1 vs2 ρ3 ρ4,
                      j <= i0 ->
                      Forall exposed vs2 ->
                      Forall2 (V_top (i0 - (i0 - j))) vs1 vs2 ->
                      set_lists xs1 vs1 (M.set f1 (CTag l1 W (CVfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                      set_lists xs2 vs2 (M.set f2 (AT.Tag w (AT.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                      E_top' V_top (i0 - (i0 - j)) ρ3 (CEexp W e1) ρ4 e2
                end

          | _, _ => False
          end
    end.

Lemma V_V_top_Forall :
  forall i,
    (forall m : nat,
        m < S i ->
        forall v1 v2,
          exposed v2 ->
          V m v1 v2 <-> V_top m v1 v2) ->
    forall j vs1 vs2,
      j <= i ->
      Forall exposed vs2 ->
      Forall2 (V j) vs1 vs2 <-> Forall2 (V_top j) vs1 vs2.
Proof.
  intros.
  revert vs1 j H0.
  induction H1; simpl; intros.
  - split; intros; inv H1; auto.
  - split; intros; inv H3; constructor; auto;
      solve [ eapply H; try lia; eauto |
              eapply IHForall; eauto ].
Qed.

Lemma V_V_top :
  forall i v1 v2,
    exposed v2 ->
    (V i v1 v2 <-> V_top i v1 v2).
Proof.
  intro i.
  induction i using lt_wf_rec; intros.
  split; intros.
  - destruct i; simpl in *.
    + destruct v1; destruct v2.
      destruct v; destruct c; try firstorder.
    + destruct v1; destruct v2.
      destruct v; destruct c; try firstorder;
        rename w into W.
      * destruct H1 as [Hwf [Hwf2 [HW [Hex [Hlen HV]]]]]; subst.
        repeat (split; eauto); intros.

        assert (HEV : E' V W (exposedb w0) (i - (i - j)) ρ3 e0 ρ4 e).
        {
          eapply HV; eauto.
          eapply V_V_top_Forall; eauto; try lia.
        }
        unfold E_top', E' in *; intros.
        inv H0; invc.
        destruct (exposed_reflect w0); try contradiction.
        edestruct HEV as [j2 [r2 [Hstep HR]]]; eauto.
        eapply AC.cbstep_top_fuel_cbstep_fuel; eauto.

        eexists; eexists; split; eauto.
        unfold R' in *.
        destruct r1; destruct r2; auto.
        eapply H; eauto; try lia.
        eapply AT.bstep_fuel_exposed_inv in Hstep; eauto; fcrush.
      * eapply V_V_top_Forall; fcrush.
  - destruct i; simpl in *;
      destruct H1 as [Hwf [Hwf2 [Hex HV]]].
    + destruct v1; destruct v2.
      destruct v; destruct c; try firstorder; subst; invc.
    + destruct v1; destruct v2.
      destruct v; destruct c; try firstorder; subst; invc.
      * inv Hex.
        rename w into W.
        destruct HV as [HW [Hlen HV]].
        repeat (split; eauto); intros.

        inv H0; invc.
        assert (HEV : E_top' V_top (i - (i - j)) ρ3 (CEexp W e0) ρ4 e).
        {
          eapply (HV _ vs1 vs2); eauto.
          eapply V_V_top_Forall; eauto; try lia.
        }
        unfold E_top', E' in *; intros.
        destruct (exposed_reflect w0); try contradiction.
        edestruct HEV as [j2 [r2 [Hstep HR]]]; eauto.
        eapply AC.cbstep_fuel_cbstep_top_fuel; eauto.

        eexists; eexists; split; eauto.
        unfold R' in *.
        destruct r1; destruct r2; auto.
        eapply H; eauto; try lia.
        eapply AT.bstep_fuel_exposed_inv in Hstep; eauto; fcrush.
      * inv Hex.
        eapply V_V_top_Forall; eauto.
Qed.

Definition R_top := (R' V_top).

Lemma R_R_top :
  forall i r1 r2,
    exposed_res r2 ->
    (R i r1 r2 <-> R_top i r1 r2).
Proof.
  unfold R, R_top, R'.
  intros.
  split; destruct r1; destruct r2; try contradiction;
    inv H; intros; eauto;
    eapply V_V_top; eauto.
Qed.

Definition E_top := (E_top' V_top).

Lemma E_E_top W i ρ1 ρ2 e1 e2 :
  E W true i ρ1 e1 ρ2 e2 ->
  E_top i ρ1 (CEexp W e1) ρ2 e2.
Proof.
  unfold E, E_top, E', E_top'.
  intros.
  edestruct H as [j2 [r2 [Hcbstep HR]]]; eauto.
  eapply AC.cbstep_top_fuel_cbstep_fuel; eauto.
  eexists; eexists; split; eauto.
  eapply R_R_top; eauto.
  eapply AT.bstep_fuel_exposed_inv; eauto.
Qed.

Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  wf_cenv ρ1 /\
    wf_env ρ2 /\
    Γ2 \subset Γ1 /\
    forall x,
      (x \in Γ1) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
          M.get x ρ2 = Some v2 /\
          exposed v2 /\
          V i v1 v2.

Lemma G_top_wf_cenv_l i Γ1 ρ1 Γ2 ρ2 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  wf_env ρ2.
Proof. unfold G_top. intros; tauto. Qed.

Lemma G_top_wf_env_r i Γ1 ρ1 Γ2 ρ2 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  wf_env ρ2.
Proof. unfold G_top. intros; tauto. Qed.

Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  Γ3 \subset Γ1 ->
  Γ4 \subset Γ3 ->
  G_top i Γ3 ρ1 Γ4 ρ2.
Proof.
  unfold G_top.
  intros.
  destruct H as [Hwf [Href [Hs HG]]].
  repeat (split; auto).
Qed.

Lemma G_top_G :
  forall {i Γ1 ρ1 Γ2 ρ2},
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    G i Γ1 ρ1 Γ2 ρ2.
Proof.
  unfold G_top, G.
  intros.
  destruct H as [Hwf [Href [Hs HG]]].
  unfold Ensembles.Included, Ensembles.In, Dom_map in *.
  repeat (split; auto); intros.
  edestruct HG as [v1' [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto.
  rewrite Heqv1 in H0; inv H0; eauto.
Qed.

Definition trans_correct_top etop etop' :=
  AT.occurs_free etop' \subset AC.occurs_free_top etop /\
  forall i ρ1 ρ2,
    G_top i (AC.occurs_free_top etop) ρ1 (AT.occurs_free etop') ρ2 ->
    E_top i ρ1 etop ρ2 etop'.

Lemma trans_correct_trans_correct_top W e1 e2 :
  AT.occurs_free e2 \subset AS.occurs_free e1 ->
  trans_correct W (AS.occurs_free e1) e1 e2 ->
  trans_correct_top (AC.CEexp W e1) e2.
Proof.
  unfold trans_correct, trans_correct_top.
  intros.
  split.
  - eapply Included_trans; eauto.
    eapply AC.occurs_free_top_cexp; eauto.
  - intros.
    eapply E_E_top; eauto.
    eapply H0; eauto.
    eapply G_top_G; eauto.
    eapply G_top_subset; eauto.
    eapply AC.occurs_free_top_cexp; eauto.
Qed.

Theorem top W etop etop':
  trans W (AS.occurs_free etop) etop etop' ->
  trans_correct_top (AC.CEexp W etop) etop'.
Proof.
  intros H; intros.
  eauto using fundamental_property, trans_correct_trans_correct_top, trans_exp_inv.
Qed.

(* Linking Preservation *)

Lemma preserves_linking f w l1 W1 W2 x e1 e2 e1' e2' :
  W1 ! l1 = Some w ->
  (w \in Exposed) ->
  trans_correct_top (AC.CEexp W1 e1) e1' ->
  trans_correct_top (AC.CEexp W2 e2) e2' ->
  trans_correct_top (AC.link f x l1 W1 e1 W2 e2) (AT.link f w x e1' e2').
Proof.
  unfold AC.link, AT.link.
  intros.
Admitted.

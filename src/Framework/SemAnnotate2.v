From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Util W0 ANF0 ANF1 ANF Label Checking Reify Annotate Erase RelComp.

Module AS := ANF0.
Module AI := ANF1.
Module AT := ANF.

Module L := Label.
Module C := Checking.
Module R := Reify.

(* Combined Logical Relations *)
Definition R' (P : nat -> AS.val -> AT.wval -> Prop) (i : nat) (r1 : AS.res) (r2 : AT.res) :=
  match r1, r2 with
  | AS.OOT, AT.OOT => True
  | AS.Res v1, AT.Res v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> AS.val -> AT.wval -> Prop) (ex : bool) (i : nat) (ρ1 : AS.env) (e1 :AS.exp) (ρ2 : AT.env) (e2 : AT.exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    AS.bstep_fuel ρ1 e1 j1 r1 ->
    exists j2 r2,
      AT.bstep_fuel ex ρ2 e2 j2 r2 /\
        R' P (i - j1) r1 r2.

Fixpoint V (i : nat) (v1 : AS.val) (wv2 : AT.wval) {struct i} : Prop :=
  wf_val wv2 /\
    match wv2 with
    | AT.TAG _ w2 v2 =>
        (w2 \in Exposed -> exposed wv2) /\
        match v1, v2 with
        | AS.Vconstr c1 vs1, AT.Vconstr c2 vs2 =>
            c1 = c2 /\
              match i with
              | 0 => length vs1 = length vs2
              | S i0 => Forall2 (V i0) vs1 vs2
              end

        | AS.Vfun f1 ρ1 xs1 e1, AT.Vfun f2 ρ2 xs2 e2 =>
            length xs1 = length xs2 /\
              match i with
              | 0 => True
              | S i0 =>
                  forall j vs1 vs2 ρ3 ρ4,
                    j <= i0 ->
                    (w2 \in Exposed -> Forall exposed vs2) ->
                    Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                    set_lists xs1 vs1 (M.set f1 (AS.Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
                    set_lists xs2 vs2 (M.set f2 (AT.Tag w2 (AT.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                    E' V (exposedb w2) (i0 - (i0 - j)) ρ3 e1 ρ4 e2
              end

        | _, _ => False
        end
    end.

Definition R := (R' V).

Definition E := (E' V).

(* Lemmas about [wf_val], [wf_res], and [wf_env] *)
Lemma V_wf_val_r {i v1 v2}:
  V i v1 v2 ->
  wf_val v2.
Proof.
  intros HV.
  destruct i; simpl in *;
    destruct HV as [Hv2 _]; auto.
Qed.

Lemma V_wf_val_Forall_r {i vs1 vs2} :
  Forall2 (V i) vs1 vs2 ->
  Forall wf_val vs2.
Proof.
  intros.
  induction H; auto.
  constructor; auto.
  eapply V_wf_val_r; eauto.
Qed.

Lemma V_wf_res_r {i v1 v2}:
  V i v1 v2 ->
  wf_res (Res v2).
Proof.
  intros HV.
  constructor.
  eapply V_wf_val_r; eauto.
Qed.

Lemma R_wf_res_l {i r1 r2} :
  R i r1 r2 ->
  wf_res r2.
Proof.
  unfold R.
  intros.
  destruct r1; destruct r2; try contradiction; auto.
  constructor.
  eapply V_wf_val_r; eauto.
Qed.

(* Inversion Lemmas *)
Lemma R_res_inv_l i v1 r2 :
  R i (A0.Res v1) r2 ->
  exists v2, r2 = A1.Res v2 /\ V i v1 v2.
Proof.
  intros.
  destruct r2; simpl in *; try contradiction.
  eexists; split; eauto.
Qed.


Definition G i Γ1 ρ1 Γ2 ρ2 :=
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
Proof.
  unfold G.
  intros.
  inv H; split; auto.
Qed.

Lemma G_wf_env_r {i Γ1 ρ1 Γ2 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  wf_env ρ2.
Proof.
  unfold G.
  intros H; destruct H; auto.
Qed.

Lemma G_get {Γ1 Γ2 i ρ1 ρ2}:
  G i Γ1 ρ1 Γ2 ρ2 ->
  forall x v1,
    (x \in Γ1) ->
    (x \in Γ2) ->
    M.get x ρ1 = Some v1 ->
    exists v2,
      M.get x ρ2 = Some v2 /\
        V i v1 v2.
Proof.
  unfold G.
  intros; fcrush.
Qed.

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
  - fcrush.
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
  intro HG.
  pose proof HG as HG'.
  unfold G in HG.
  intros.

  inv HG.
  split.
  eapply wf_env_set; eauto.
  eapply V_wf_val_r; eauto.

  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss in *.
    invc.
    eexists; repeat (split; intros; eauto).
  - rewrite M.gso in *; auto.
    eapply G_get; eauto.
    fcrush.
    fcrush.
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
(* TODO: refactor *)
Lemma V_mono_Forall_aux {A B}:
  forall i j (V : nat -> A -> B -> Prop) vs1 vs2,
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
  destruct v2.
  destruct i; simpl in H0;
    destruct j; simpl; intros;
    destruct H0 as [Hwf [Hex HV]].
  - destruct v1; destruct v; fcrush.
  - fcrush.
  - repeat (split; auto).
    destruct v1; destruct v; try contradiction.
    + destruct HV.
      destruct (exposed_reflect w); fcrush.
    + destruct HV as [Hc HV]; subst.
      split; eauto using Forall2_length.
  - repeat (split; auto).
    destruct v1; destruct v; try contradiction.
    + destruct HV as [Hlen HV]; subst.
      repeat (split; eauto); intros.
      specialize (HV j0 vs1 vs2 ρ3 ρ4).
      rewrite normalize_step in *; try lia.
      apply HV; eauto; lia.
    + destruct HV as [Heqc HV]; subst.
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

Lemma E_mono {ex ρ1 e1 ρ2 e2} i j:
  E ex i ρ1 e1 ρ2 e2 ->
  j <= i ->
  E ex j ρ1 e1 ρ2 e2.
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
  destruct H as [Hwf HG].
  repeat (split; auto); intros.
  edestruct HG as [v2 [Heqv2 HV]]; eauto.
  eexists; repeat (split; eauto).
  eauto using V_mono.
Qed.

Definition trans_correct Γ e1 e2 :=
  forall ex i ρ1 ρ2,
    G i Γ ρ1 (AT.occurs_free e2) ρ2 ->
    E ex i ρ1 e1 ρ2 e2.

Definition trans Γ1 e1 e2 :=
  exists l l' e3 W,
    L.trans Γ1 l e1 l' e3 /\
    C.web_map_spec W Γ1 e3 /\
    R.trans W Γ1 e3 e2.

Lemma ret_compat_top Γ x :
  (x \in Γ) ->
  trans_correct Γ (AS.Eret x) (AT.Eret x).
Proof.
  unfold trans_correct, E, E', R'.
  intros.
  inv H2.
  + eexists; eexists; split; simpl; fcrush.
  + inv H3.
    edestruct (G_get H0) as [v2 [Heqv2 HV]]; eauto; invc.
    exists 1, (AT.Res v2); split; eauto; simpl.
    econstructor; eauto.
    destruct ex; auto.
    constructor.
    (* stuck *)
Abort.

Lemma Vfun_V Γ1 f w xs e e' :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  forall {i Γ2 ρ1 ρ2},
    G i Γ1 ρ1 Γ2 ρ2 ->
    A1.occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
    V i (AS.Vfun f ρ1 xs e) (Tag w (AT.Vfun f ρ2 xs e')).
Proof.
  unfold trans_correct.
  intros He i.
  induction i; simpl; intros; auto;
    assert (wf_env ρ2) by eauto using G_wf_env_r;
    repeat (split; auto); intros.

  apply (He (exposedb w) (i - (i - j)) ρ3 ρ4); auto.
  - eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))); eauto.
    eapply G_set_lists; eauto.
    eapply G_set; eauto.
    + apply G_mono with (S i); eauto; lia.
    + apply V_mono with i; try lia.
      eapply IHi with (Γ2 := Γ2); eauto.
      apply G_mono with (S i); eauto; lia.
    + apply Included_refl.
Qed.

Lemma fun_compat Γ e e' k k' f w xs :
  trans_correct (FromList xs :|: (f |: Γ)) e e' ->
  trans_correct (f |: Γ) k k' ->
  trans_correct Γ (AS.Efun f xs e k) (AT.Efun f w xs e' k').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H3.
  - exists 0, OOT; split; simpl; eauto.
  - inv H4.
    edestruct (H0 ex (i - 1) (M.set f (AS.Vfun f ρ1 xs e) ρ1) (M.set f (Tag w (AT.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_subset with (Γ2 := (f |: (AT.occurs_free (AT.Efun f w xs e' k')))); eauto.
      * eapply G_set; eauto.
        eapply G_mono; eauto; try lia.

        eapply Vfun_V with (Γ2 := (AT.occurs_free (AT.Efun f w xs e' k'))); eauto.
        -- eapply G_mono; eauto; try lia.
        -- eapply AT.free_fun_e_subset; eauto.
      * fcrush.
      * eapply AT.free_fun_k_subset; eauto.
    + exists (S j2), r2; split; auto.
      * constructor; auto.
        destruct ex; auto.
        eapply bstep_fuel_exposed_inv; eauto.
      * apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma fp Γ1 e1 e2 :
  trans Γ1 e1 e2 ->
  trans_correct Γ1 e1 e2.
Proof.
  unfold trans.
  intros.
  destruct H as [l [l' [e3 [W [LT [CT RT]]]]]].

  generalize dependent W.
  generalize dependent e2.
  induction LT; intros e2 W CT RT; inv CT; inv RT; invc.
  - admit.
  - assert (Hk1 : trans_correct (f |: Γ) k0 k3) by eauto.
    rename e4 into e3.
    assert (He1 : trans_correct (FromList xs :|: (f |: Γ)) e0 e3) by eauto.
    eauto using fun_compat; eauto.
  -
Abort.

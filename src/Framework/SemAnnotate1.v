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

(* Top-level Logical Relations *)
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

Fixpoint V_top (i : nat) (v1 : AS.val) (wv2 : AT.wval) {struct i} : Prop :=
  wf_val wv2 /\
    exposed wv2 /\
    match wv2 with
    | AT.TAG _ w2 v2 =>
        match v1, v2 with
        | AS.Vconstr c1 vs1, AT.Vconstr c2 vs2 =>
            c1 = c2 /\
              match i with
              | 0 => length vs1 = length vs2
              | S i0 => Forall2 (V_top i0) vs1 vs2
              end

        | AS.Vfun f1 ρ1 xs1 e1, AT.Vfun f2 ρ2 xs2 e2 =>
            (* note function arguments and result are always exposed regardless of whether a function is known or unknown *)
            length xs1 = length xs2 /\
              match i with
              | 0 => True
              | S i0 =>
                  forall j vs1 vs2 ρ3 ρ4,
                    j <= i0 ->
                    Forall exposed vs2 ->
                    Forall2 (V_top (i0 - (i0 - j))) vs1 vs2 ->
                    set_lists xs1 vs1 (M.set f1 (AS.Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
                    set_lists xs2 vs2 (M.set f2 (Tag w2 (AT.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                    E' V_top true (i0 - (i0 - j)) ρ3 e1 ρ4 e2
              end

        | _, _ => False
        end
    end.

Definition V i := Cross (fun v1 v2 => L.V i v1 v2)
                    (Cross (fun v1 v2 => C.V_top i v1 v2)
                       (fun v1 v2 => R.V_top i v1 v2)).

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

(* This is not provable.
   The top-level environment will get into the way. *)
Parameter l0 : label.
Lemma V_V_top :
  forall i v1 v2,
    exposed v2 ->
    (V i v1 v2 <-> V_top i v1 v2).
Proof.
  intro i.
  induction i using lt_wf_rec; intros.
  unfold V, Cross.
  split; intros.
  - admit.
  - destruct i; simpl in *;
      destruct H1 as [Hwf [Hex HV]].
    + destruct v2; destruct v1;
        destruct v; try firstorder.
      * (* exists (AI.Tag l0 (AI.Vfun v t l1 e)). (* ? env? *) *)
Abort.

Definition R_top := (R' V_top).

Definition E_top := (E' V_top).

Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  wf_env ρ2 /\
    Γ2 \subset Γ1 /\
    forall x,
      (x \in Γ1) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
          M.get x ρ2 = Some v2 /\
          V_top i v1 v2.

Definition trans_correct_top etop etop' :=
  AT.occurs_free etop' \subset AS.occurs_free etop /\
    forall i ρ1 ρ2,
      G_top i (AS.occurs_free etop) ρ1 (AT.occurs_free etop') ρ2 ->
      E_top true i ρ1 etop ρ2 etop'.

Definition T_top e1 e2 :=
  exists e3,
    L.trans_correct_top e1 e3 /\
      exists W,
        well_annotated_top W e3 /\
        R.trans_correct_top W e3 e2.

Lemma T_top_trans_correct_top e1 e2 :
  T_top e1 e2 ->
  trans_correct_top e1 e2.
Proof.
  unfold T_top, trans_correct_top, L.trans_correct_top, C.well_annotated_top, R.trans_correct_top.
  intros.
  destruct H as [e3 [HL [W [HC HR]]]].
  destruct HL as [HS1 HL].
  destruct HC as [HW HC].
  destruct HR as [HS2 HR].

  split; intros.
  eapply Included_trans; eauto.

  unfold E_top, E'; intros.
  unfold web_map_sound_top in HW.

  (* Still the top-level environments will get into the way *)
Abort.

  (* Top-level Lemmas about [wf_val], [wf_res], and [wf_env] *)
  Lemma V_top_wf_val_r {i v1 v2}:
    V_top i v1 v2 ->
    wf_val v2.
  Proof.
    intros HV.
    destruct i; simpl in *;
      destruct HV as [Hv2 _]; auto.
  Qed.

  Lemma V_top_wf_val_Forall_r {i vs1 vs2} :
    Forall2 (V_top i) vs1 vs2 ->
    Forall wf_val vs2.
  Proof.
    intros.
    induction H; auto.
    constructor; auto.
    eapply V_top_wf_val_r; eauto.
  Qed.

  Lemma V_top_wf_res_r {i v1 v2}:
    V_top i v1 v2 ->
    wf_res (Res v2).
  Proof.
    intros HV.
    constructor.
    eapply V_top_wf_val_r; eauto.
  Qed.

  Lemma V_top_exposed_r {i v1 v2}:
    V_top i v1 v2 ->
    exposed v2.
  Proof.
    intros.
    destruct i; destruct v2;
      simpl in *; fcrush.
  Qed.

  Lemma V_top_exposed_Forall_r {i vs1 vs2} :
    Forall2 (V_top i) vs1 vs2 ->
    Forall exposed vs2.
  Proof.
    intros.
    induction H; auto.
    constructor; auto.
    eapply V_top_exposed_r; eauto.
  Qed.

  Lemma R_top_wf_res_l {i r1 r2} :
    R_top i r1 r2 ->
    wf_res r2.
  Proof.
    unfold R.
    intros.
    destruct r1; destruct r2; try contradiction; auto.
    constructor.
    eapply V_top_wf_val_r; eauto.
  Qed.

  (* Top-level Inversion Lemmas *)
  Lemma R_top_res_inv_l i v1 r2 :
    R_top i (A0.Res v1) r2 ->
    exists v2, r2 = A1.Res v2 /\ V_top i v1 v2.
  Proof.
    intros.
    destruct r2; simpl in *; try contradiction.
    eexists; split; eauto.
  Qed.

  (* Top-level Monotonicity Lemmas *)
    Lemma V_mono_Forall_aux :
    forall i j (V : nat -> A0.val -> A1.wval -> Prop) vs1 vs2,
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

  Lemma V_top_mono i :
    forall {j v1 v2},
      V_top i v1 v2 ->
      j <= i ->
      V_top j v1 v2.
  Proof.
    induction i using lt_wf_rec; intros.
    destruct v2.
    destruct i; simpl in H0;
      destruct j; simpl; intros;
      destruct H0 as [Hv1 [Hex HV]]; subst.
    - repeat (split; auto).
    - inv H1.
    - repeat (split; auto).
      destruct v1; destruct v; try contradiction.
      + destruct HV.
        destruct (exposed_reflect w); fcrush.
      + destruct HV as [Hc HV]; subst.
        repeat split; auto.
        eapply Forall2_length; eauto.
    - repeat (split; auto).
      destruct v1; destruct v; try contradiction.
      + destruct HV as [Hlen HV]; subst.
        repeat split; auto; intros.
        inv Hex.
        destruct (exposed_reflect w); try contradiction.
        specialize (HV j0 vs1 vs2 ρ3 ρ4).
        rewrite normalize_step in *; try lia.
        apply HV; eauto; lia.
      + destruct HV as [Heqc HV]; subst.
        repeat split; auto.
        eapply V_mono_Forall_aux; eauto; lia.
  Qed.

  Lemma V_top_mono_Forall {vs1 vs2} i j :
    Forall2 (V_top i) vs1 vs2 ->
    j <= i ->
    Forall2 (V_top j) vs1 vs2.
  Proof.
    intros H.
    revert j.
    induction H; simpl; intros; auto.
    constructor; eauto.
    eapply V_top_mono; eauto.
  Qed.

  Lemma R_top_mono {r1 r2} i j :
    R_top i r1 r2 ->
    j <= i ->
    R_top j r1 r2.
  Proof.
    unfold R.
    intros.
    destruct r1; auto.
    destruct r2; auto.
    eapply V_top_mono; eauto.
  Qed.

  Lemma E_top_mono {ex ρ1 ρ2 e1 e2} i j:
    E_top ex i ρ1 e1 ρ2 e2 ->
    j <= i ->
    E_top ex j ρ1 e1 ρ2 e2.
  Proof.
    unfold E_top, E'.
    intros.
    destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
    exists j2, r2; split; eauto.
    apply R_top_mono with (i - j1); try lia; auto.
  Qed.

  Lemma G_top_mono {Γ1 Γ2 ρ1 ρ2} i j:
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    j <= i ->
    G_top j Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold G_top.
    intros.
    destruct H as [Hwf [HS HG]].
    split; auto.
    split; auto; intros.
    edestruct HG as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto.
    eexists; eexists; repeat (split; eauto).
    apply V_top_mono with i; eauto.
  Qed.


Lemma G_top_wf_env_r i Γ1 ρ1 Γ2 ρ2 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  wf_env ρ2.
Proof. unfold G_top. intros; tauto. Qed.

Lemma G_top_subset_inv i Γ1 ρ1 Γ2 ρ2 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  Γ2 \subset Γ1.
Proof. unfold G_top; intros; tauto. Qed.

Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  Γ3 \subset Γ1 ->
  Γ4 \subset Γ3 ->
  G_top i Γ3 ρ1 Γ4 ρ2.
Proof.
  unfold G_top.
  intros.
  destruct H as [Hr [Hs HG]].
  repeat (split; auto).
Qed.


  (* Top-level Environment Lemmas *)
  Lemma G_top_get {Γ1 Γ2 i ρ1 ρ2}:
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    forall x,
      (x \in Γ1) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
          M.get x ρ2 = Some v2 /\
          V_top i v1 v2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hr1 [HΓ HG]].
    eapply (HG x); eauto.
  Qed.

  Lemma G_top_get_list {i Γ1 ρ1 Γ2 ρ2} :
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    forall xs,
      (FromList xs) \subset Γ1 ->
      exists vs1 vs2,
        get_list xs ρ1 = Some vs1 /\
          get_list xs ρ2 = Some vs2 /\
          Forall2 (V_top i) vs1 vs2.
  Proof.
    intros HG xs.
    intros.
    induction xs; simpl; intros.
    - eexists; eexists; repeat split; eauto.
    - rewrite FromList_cons in H.
      edestruct (G_top_get HG) as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto.

      edestruct IHxs as [vs1 [vs2 [Heqvs1 [Heqvs2 HVs]]]]; eauto.
      eapply Included_trans; eauto.
      apply Included_Union_r.

      rewrite Heqv1.
      rewrite Heqvs1.
      rewrite Heqv2.
      rewrite Heqvs2.
      exists (v1 :: vs1), (v2 :: vs2); repeat (split; auto).
  Qed.

  Lemma G_top_set {i Γ1 ρ1 Γ2 ρ2}:
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    forall {x v1 v2},
      V_top i v1 v2 ->
      G_top i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
  Proof.
    intros.
    unfold G_top; intros.

    split.
    eapply wf_env_set; eauto.
    eapply G_top_wf_env_r; eauto.
    eapply V_top_wf_val_r; eauto.

    split.
    apply Included_Union_compat; auto.
    apply Included_refl.
    eapply G_top_subset_inv; eauto.

    intros.
    destruct (M.elt_eq x0 x); subst.
    - repeat rewrite M.gss.
      eexists; eexists; repeat split; eauto.
    - repeat (rewrite M.gso; auto).
      assert (x0 \in Γ1) by fcrush.
      eapply G_top_get; eauto.
  Qed.

  Lemma G_top_set_lists {i Γ1 ρ1 Γ2 ρ2}:
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    forall {xs vs1 vs2 ρ3 ρ4},
      Forall2 (V_top i) vs1 vs2 ->
      set_lists xs vs1 ρ1 = Some ρ3 ->
      set_lists xs vs2 ρ2 = Some ρ4 ->
      G_top i (FromList xs :|: Γ1) ρ3 (FromList xs :|: Γ2) ρ4.
  Proof.
    intros HG xs.
    assert (HΓ : Γ2 \subset Γ1) by (eapply G_top_subset_inv; eauto).
    induction xs; simpl; intros.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      inv H0; inv H1.
      eapply G_top_subset; eauto.
      normalize_sets.
      rewrite Union_Empty_set_neut_l; eauto.
      apply Included_refl.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
      destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
      inv H; inv H0; inv H1.
      eapply G_top_subset with (Γ1 := (a |: (FromList xs :|: Γ1))) (Γ2 := (a |: (FromList xs :|: Γ2))); eauto.
      eapply G_top_set; eauto.
      normalize_sets.
      rewrite Union_assoc.
      apply Included_refl.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
  Qed.


Definition trans_top Γ1 e1 e2 :=
  exists l l' e3 W,
    L.trans Γ1 l e1 l' e3 /\
    C.web_map_spec W Γ1 e3 /\
    R.trans W Γ1 e3 e2.

Lemma ret_compat_top Γ x :
  (x \in Γ) ->
  trans_correct_top (AS.Eret x) (AT.Eret x).
Proof.
  unfold trans_correct_top.
  intros.
  split.
  unfold Ensembles.Included, Ensembles.In; intros; fcrush.

  unfold E_top, E', R'.
  intros.

  inv H2.
  + eexists; eexists; split; simpl; fcrush.
  + inv H3.
    edestruct (G_top_get H0) as [v1 [v2 [Heqv1 [Heqv2 HV]]]]; eauto; invc.
    exists 1, (AT.Res v2); split; eauto; simpl.
    econstructor; eauto.
    constructor.
    eapply V_top_exposed_r; eauto.
    eapply V_top_mono; eauto; lia.
Qed.

Lemma fp_top Γ1 e1 e2 :
  trans_top Γ1 e1 e2 ->
  trans_correct_top e1 e2.
Proof.
  unfold trans_top.
  intros.
  destruct H as [l [l' [e3 [W [LT [CT RT]]]]]].

  generalize dependent W.
  generalize dependent e2.
  induction LT; intros e2 W CT RT; inv CT; inv RT; invc.
  - eauto using ret_compat_top.
  - assert (Hk1 : trans_correct_top k0 k3) by eauto.
    rename e4 into e3.
    assert (He1 : trans_correct_top e0 e3) by eauto.
    (* the web isn't exposed *)
Abort.

(*
  Lemma Vfun_V_top e e' :
    trans_correct_top e e' ->
    forall i f xs Γ1 Γ2 ρ1 ρ2,
      G_top i Γ1 ρ1 Γ2 ρ2 ->
      A0.occurs_free e \subset (FromList xs :|: (f |: Γ1)) ->
      A1.occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
      V_top i (AS.Vfun f ρ1 xs e) (AT.Tag w0 (AT.Vfun f ρ2 xs e')).
*)

Lemma fun_compat_top e e' k k' f w xs :
  trans_correct_top e e' ->
  trans_correct_top k k' ->
  trans_correct_top (AS.Efun f xs e k) (AT.Efun f w xs e' k').
Proof.
  unfold trans_correct_top, E_top, E'.
  intros.
  destruct H as [HSe He].
  destruct H0 as [HSk Hk].

  split.
  unfold Ensembles.Included, Ensembles.In in *.
  admit.

  intros.
  inv H1.
  - exists 0, OOT; split; simpl; eauto.
  - inv H2.
    edestruct (Hk (i - 1) (M.set f (AS.Vfun f ρ1 xs e) ρ1) (M.set f (Tag w (AT.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_top_subset with (Γ1 := (f |: (AS.occurs_free (A0.Efun f xs e k)))) (Γ2 := (f |: (AT.occurs_free (A1.Efun f w xs e' k')))); eauto.
      * eapply G_top_set; eauto.
        eapply G_top_mono; eauto; try lia.

        (*
        eapply Vfun_V_top with (Γ1 := (AS.occurs_free (AS.Efun f xs e k))) (Γ2 := (AT.occurs_free (AT.Efun f w xs e' k'))); eauto.
        -- unfold trans_correct_top.
           split; auto.
        -- eapply G_top_mono; eauto; try lia.
        -- eapply A0.free_fun_e_subset; eauto.
        -- eapply A1.free_fun_e_subset; eauto.
         *)
        admit.
      * eapply A0.free_fun_k_subset; eauto.
    + exists (S j2), r2; split; auto.
      * constructor; auto.
        eapply bstep_fuel_exposed_inv; eauto.
      * apply R_top_mono with ((i - 1) - c); try lia; auto.
Abort.

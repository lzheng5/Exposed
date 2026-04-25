From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Util W0 ANF1 ANF Annotate Erase.

Module AS := ANF1.
Module AT := ANF.

Definition web_map := M.t web.

Section Collecting.

  (* The analysis result mapping labels to the actual webs. *)
  Variable W : web_map.

  Definition to_exposed (tv : AS.wval) : Prop :=
    match tv with
    | AS.TAG _ l v => exists w, W ! l = Some w /\ (w \in Exposed)
    end.

  Definition to_exposed_res (r : AS.res) : Prop :=
    match r with
    | AS.OOT => True
    | AS.Res v => to_exposed v
    end.

  (* `W` is a valid perfect analysis result with respect to the collecting big-step semantics *)
  Inductive cbstep (ex : bool) (ρ : AS.env) : AS.exp -> fuel -> AS.res -> Prop :=
  | Cbstep_ret :
    forall {x l w v},
      M.get x ρ = Some (AS.Tag l v) ->
      W ! l = Some w ->
      cbstep ex ρ (AS.Eret x) 0 (AS.Res (AS.Tag l v))

  | Cbstep_fun :
    forall {f l w xs e k c r},
      W ! l = Some w ->
      cbstep_fuel ex (M.set f (AS.Tag l (AS.Vfun f ρ xs e)) ρ) k c r ->
      cbstep ex ρ (AS.Efun f l xs e k) c r

  | Cbstep_app :
    forall {f f' l l' w xs ρ' xs' e vs ρ'' c r},
      M.get f ρ = Some (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      W ! l = Some w ->
      W ! l' = Some w ->
      (w \in Exposed -> Forall to_exposed vs /\ to_exposed_res r) ->
      cbstep_fuel (exposedb w) ρ'' e c r ->
      cbstep ex ρ (AS.Eapp f l xs) c r

  | Cbstep_letapp_Res :
    forall {x f f' l l' w xs k ρ' xs' e vs ρ'' c c' v r},
      M.get f ρ = Some (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      cbstep_fuel (exposedb w) ρ'' e c (AS.Res v) ->
      cbstep_fuel ex (M.set x v ρ) k c' r ->
      W ! l = Some w ->
      W ! l' = Some w ->
      (w \in Exposed -> Forall to_exposed vs /\ to_exposed v) ->
      cbstep ex ρ (AS.Eletapp x f l xs k) (c + c') r

  | Cbstep_letapp_OOT :
    forall {x f f' l l' w xs k ρ' xs' e vs ρ'' c},
      M.get f ρ = Some (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      cbstep_fuel (exposedb w) ρ'' e c AS.OOT ->
      W ! l = Some w ->
      W ! l' = Some w ->
      (w \in Exposed -> Forall to_exposed vs) ->
      cbstep ex ρ (AS.Eletapp x f l xs k) c AS.OOT

  | Cbstep_constr :
    forall {x l w t xs e r vs c},
      get_list xs ρ = Some vs ->
      W ! l = Some w ->
      (w \in Exposed -> Forall to_exposed vs) ->
      cbstep_fuel ex (M.set x (AS.Tag l (AS.Vconstr t vs)) ρ) e c r ->
      cbstep ex ρ (AS.Econstr x l t xs e) c r

  | Cbstep_proj :
    forall {x l l' w t i y e c r v vs},
      M.get y ρ = Some (AS.Tag l' (AS.Vconstr t vs)) ->
      nth_error vs i = Some v ->
      W ! l = Some w ->
      W ! l' = Some w ->
      cbstep_fuel ex (M.set x v ρ) e c r ->
      cbstep ex ρ (AS.Eproj x l i y e) c r

  | Cbstep_case :
    forall {x l l' w cl t e r c vs},
      M.get x ρ = Some (AS.Tag l' (AS.Vconstr t vs)) ->
      find_tag cl t e ->
      W ! l = Some w ->
      W ! l' = Some w ->
      cbstep_fuel ex ρ e c r ->
      cbstep ex ρ (AS.Ecase x l cl) c r

  with cbstep_fuel (ex : bool) (ρ : AS.env) : AS.exp -> fuel -> AS.res -> Prop :=
  | CbstepF_OOT :
    forall {e},
      cbstep_fuel ex ρ e 0 AS.OOT

  | CbstepF_Step :
    forall {e c r},
      cbstep ex ρ e c r ->
      (if ex then to_exposed_res r else True) ->
      cbstep_fuel ex ρ e (S c) r.

  Hint Constructors cbstep : core.
  Hint Constructors cbstep_fuel : core.

  Scheme cbstep_ind' := Minimality for cbstep Sort Prop
  with cbstep_fuel_ind' := Minimality for cbstep_fuel Sort Prop.

  Theorem cbstep_deterministic v v' {ex ρ e c c' r r'}:
    cbstep ex ρ e c r ->
    cbstep ex ρ e c' r' ->
    r = AS.Res v ->
    r' = AS.Res v' ->
    (v = v' /\ c = c').
  Proof.
    intros H.
    generalize dependent v'.
    generalize dependent r'.
    generalize dependent c'.
    generalize dependent v.
    induction H using cbstep_ind' with (P := fun ex ρ e c r =>
                                              forall v c' r' v',
                                                cbstep ex ρ e c' r' ->
                                                r = AS.Res v -> r' = AS.Res v' ->
                                                v = v' /\ c = c')
                                      (P0 := fun ex ρ e c r =>
                                               forall v c' r' v',
                                                 cbstep_fuel ex ρ e c' r' ->
                                                 r = AS.Res v -> r' = AS.Res v' ->
                                                 v = v' /\ c = c');
      intros; subst.
    - inv H1; inv H2; invc; auto.
    - inv H1.
      edestruct IHcbstep; eauto.
    - inv H6; invc.
      edestruct IHcbstep; eauto.
    - inv H7; invc.
      edestruct IHcbstep; eauto.
      subst.
      edestruct IHcbstep0; eauto.
    - inv H7.
    - inv H3; invc.
      edestruct IHcbstep; eauto.
    - inv H4; invc.
      edestruct IHcbstep; eauto.
    - inv H4; invc.
      destruct (find_tag_deterministic H0 H9); subst.
      edestruct IHcbstep; eauto.
    - inv H0.
    - destruct ex; inv H1.
      + unfold to_exposed_res, to_exposed in *.
        destruct v; destruct v'.
        edestruct IHcbstep; eauto.
      + edestruct IHcbstep; eauto.
  Qed.

  Theorem cbstep_fuel_deterministic v v' {ex ρ e c c' r r'}:
    cbstep_fuel ex ρ e c r ->
    cbstep_fuel ex ρ e c' r' ->
    r = AS.Res v ->
    r' = AS.Res v' ->
    (v = v' /\ c = c').
  Proof.
    intros.
    inv H; inv H0; try discriminate.
    edestruct (cbstep_deterministic v v' H3 H); eauto.
  Qed.

  (* Collecting steps refine labeled steps: cbstep adds W-consistency side-conditions,
     so every cbstep derivation projects down to a bstep derivation on the same
     expression with the same fuel and result. *)
  Lemma cbstep_to_bstep ex ρ e c r :
    cbstep ex ρ e c r ->
    AS.bstep ρ e c r.
  Proof.
    intros H.
    induction H using cbstep_ind' with
      (P := fun ex ρ e c r => AS.bstep ρ e c r)
      (P0 := fun ex ρ e c r => AS.bstep_fuel ρ e c r);
      intros; econstructor; eauto.
  Qed.

  Lemma cbstep_fuel_to_bstep_fuel ex ρ e c r :
    cbstep_fuel ex ρ e c r ->
    AS.bstep_fuel ρ e c r.
  Proof.
    intros H.
    inv H.
    - apply AS.BStepF_OOT.
    - eapply AS.BStepF_Step; eauto.
      eapply cbstep_to_bstep; eauto.
  Qed.

  (* Correlation lemmas: bstep and cbstep that both terminate on the same expression
     agree on fuel and value. Follows from cbstep's refinement of bstep plus
     AS.bstep_deterministic. *)
  Lemma cbstep_bstep ex ρ e c1 c2 v1 v2 :
    AS.bstep ρ e c1 (AS.Res v1) ->
    cbstep ex ρ e c2 (AS.Res v2) ->
    c1 = c2 /\ v1 = v2.
  Proof.
    intros Hb Hc.
    apply cbstep_to_bstep in Hc.
    destruct (AS.bstep_deterministic v1 v2 Hb Hc eq_refl eq_refl) as [Hv Hceq].
    split; auto.
  Qed.

  Lemma cbstep_fuel_bstep_fuel ex ρ e c1 c2 v1 v2 :
    AS.bstep_fuel ρ e c1 (AS.Res v1) ->
    cbstep_fuel ex ρ e c2 (AS.Res v2) ->
    c1 = c2 /\ v1 = v2.
  Proof.
    intros Hb Hc.
    apply cbstep_fuel_to_bstep_fuel in Hc.
    destruct (AS.bstep_fuel_deterministic v1 v2 Hb Hc eq_refl eq_refl) as [Hv Hceq].
    split; auto.
  Qed.

  (* Transformation Specification *)
  Inductive trans (Γ : vars) : AS.exp -> AT.exp -> Prop :=
  | Trans_ret :
    forall x,
      (x \in Γ) ->
      trans Γ (AS.Eret x) (AT.Eret x)

  | Trans_fun :
    forall {f l w xs e k e' k'},
      W ! l = Some w ->
      trans (FromList xs :|: (f |: Γ)) e e' ->
      trans (f |: Γ) k k' ->
      trans Γ (AS.Efun f l xs e k) (AT.Efun f w xs e' k')

  | Trans_app :
    forall {f l w xs},
      W ! l = Some w ->
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans Γ (AS.Eapp f l xs) (AT.Eapp f w xs)

  | Trans_letapp :
    forall {x f l w xs k k'},
      W ! l = Some w ->
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (AS.Eletapp x f l xs k) (AT.Eletapp x f w xs k')

  | Trans_constr :
    forall {x l w t xs k k'},
      W ! l = Some w ->
      (FromList xs \subset Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (AS.Econstr x l t xs k) (AT.Econstr x w t xs k')

  | Trans_proj :
    forall {l w x y k k' n},
      W ! l = Some w ->
      (y \in Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (AS.Eproj x l n y k) (AT.Eproj x w n y k')

  | Trans_case_nil :
    forall {l w x},
      W ! l = Some w ->
      (x \in Γ) ->
      trans Γ (AS.Ecase x l []) (AT.Ecase x w [])

  | Trans_case_cons :
    forall {x l w e e' t cl cl'},
      W ! l = Some w ->
      (x \in Γ) ->
      trans Γ e e' ->
      trans Γ (AS.Ecase x l cl) (AT.Ecase x w cl') ->
      trans Γ (AS.Ecase x l ((t, e) :: cl)) (AT.Ecase x w ((t, e') :: cl')).

  Hint Constructors trans : core.

  Lemma trans_exp_inv {Γ e e'} :
    trans Γ e e' ->
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
  (* Note these are parameterized by the web_map, `W` *)
  Definition R' (P : nat -> AS.wval -> AT.wval -> Prop) (i : nat) (r1 : AS.res) (r2 : AT.res) :=
    match r1, r2 with
    | AS.OOT, AT.OOT => True
    | AS.Res v1, AT.Res v2 => P i v1 v2
    | _, _ => False
    end.

  Definition E' (P : nat -> AS.wval -> AT.wval -> Prop) (ex : bool) (i : nat) (ρ1 : AS.env) (e1 :AS.exp) (ρ2 : AT.env) (e2 : AT.exp) : Prop :=
    forall j1 r1,
      j1 <= i ->
      AS.bstep_fuel ρ1 e1 j1 r1 ->
      exists j2 r2,
        AT.bstep_fuel ex ρ2 e2 j2 r2 /\
        R' P (i - j1) r1 r2.

  Definition web_map_inv ex ρ e :=
    forall i r,
      AS.bstep_fuel ρ e i r ->
      cbstep_fuel ex ρ e i r.

  Fixpoint V (i : nat) (wv1 : AS.wval) (wv2 : AT.wval) {struct i} : Prop :=
    wf_val wv2 /\
    match wv1, wv2 with
    | AS.TAG _ l1 v1, AT.TAG _ w2 v2 =>
        W ! l1 = Some w2 /\
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
                  set_lists xs1 vs1 (M.set f1 (AS.Tag l1 (AS.Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                  set_lists xs2 vs2 (M.set f2 (AT.Tag w2 (AT.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                  web_map_inv (exposedb w2) ρ3 e1 ->
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

  Lemma R_wf_res_r {i r1 r2} :
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
    R i (AS.Res v1) r2 ->
    exists v2, r2 = AT.Res v2 /\ V i v1 v2.
  Proof.
    intros.
    destruct r2; simpl in *; try contradiction.
    eexists; split; eauto.
  Qed.

  (* Exposed Lemmas *)
  Lemma V_exposed {i v1 v2} :
    V i v1 v2 ->
    to_exposed v1 ->
    exposed v2.
  Proof.
    unfold to_exposed.
    intros.
    destruct v1; destruct v2;
      destruct i; try contradiction; auto;
      simpl in H;
      destruct H as [Hv1 [Hv2 [Hw HV]]]; subst;
      destruct v; destruct v0; try contradiction;
      simpl in *;
      invc; hauto b: on.
  Qed.

  Lemma V_exposed_Forall : forall {i vs1 vs2},
      Forall2 (V i) vs1 vs2 ->
      Forall to_exposed vs1 ->
      Forall exposed vs2.
  Proof.
    intros.
    induction H; intros; auto.
    inv H0.
    constructor; auto.
    eapply V_exposed; eauto.
  Qed.

  Lemma V_exposed_res {i v1 v2} :
      V i v1 v2 ->
      to_exposed v1 ->
      exposed_res (Res v2).
  Proof. strivial use: Exp_Res, @V_exposed. Qed.

  (* Environment Relation *)
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
    intros.
    destruct H as [Hr1 HG].
    eapply HG; eauto.
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
      inv H3.
      eexists; repeat (split; intros; eauto).
    - rewrite M.gso in *; auto.
      eapply G_get; eauto.

      inv H2; auto.
      inv H5; try contradiction; auto.
      inv H4; auto.
      inv H5; try contradiction; auto.
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
    forall i j (V : nat -> AS.wval -> AT.wval -> Prop) vs1 vs2,
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
      destruct H0 as [Hv1 [Hl [Hex HV]]]; subst.
    - repeat (split; auto).
    - inv H1.
    - repeat (split; auto).
      destruct v; destruct v0; try contradiction.
      + destruct HV.
        destruct (exposed_reflect w); fcrush.
      + destruct HV as [Hc HV]; subst.
        repeat split; auto.
        eapply Forall2_length; eauto.
    - repeat (split; auto).
      destruct v; destruct v0; try contradiction.
      + destruct HV as [Hlen HV]; subst.
        repeat split; auto; intros.
        destruct (exposed_reflect w).
        * specialize (HV j0 vs1 vs2 ρ3 ρ4).
          rewrite normalize_step in *; try lia.
          apply HV; eauto; lia.
        * specialize (HV j0 vs1 vs2 ρ3 ρ4).
          rewrite normalize_step in *; try lia.
          eapply HV; eauto; lia.
      + destruct HV as [Heqc HV]; subst.
        repeat split; auto.
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

  Lemma E_mono {ex ρ1 ρ2 e1 e2} i j:
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
    inv H.
    split; auto; intros.
    edestruct H2 as [v2 [Heqv2 HV]]; eauto.
    eexists; eexists; repeat split; eauto.
    apply V_mono with i; eauto.
  Qed.

  (* Compatibility Lemmas *)
  Definition trans_correct Γ e1 e2 :=
    forall ex i ρ1 ρ2,
      web_map_inv ex ρ1 e1 ->
      G i Γ ρ1 (AT.occurs_free e2) ρ2 ->
      E ex i ρ1 e1 ρ2 e2.

  Lemma ret_compat Γ x :
    (x \in Γ) ->
    trans_correct Γ (AS.Eret x) (AT.Eret x).
  Proof.
    unfold trans_correct, web_map_inv, E, E', R, R', Ensembles.Included, Ensembles.In.
    intros; simpl.
    assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Eret x) j1 r1) by (eapply H0; eauto; try lia).
    inv H3.
    - exists 0, AT.OOT; split; auto.
    - inv H4; inv Hcbstep.
      edestruct (G_get H1) as [v2 [Heqv2 HV]]; eauto.
      exists 1, (AT.Res v2); split; simpl; eauto.
      econstructor; eauto.
      destruct ex; simpl in *; auto.
      + invc.
        eapply V_exposed_res; eauto.
      + eapply V_mono; eauto; lia.
  Qed.

  Lemma Vfun_V Γ1 f l w xs e e' :
    W ! l = Some w ->
    trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
    forall {i Γ2 ρ1 ρ2},
      wf_env ρ2 ->
      G i Γ1 ρ1 Γ2 ρ2 ->
      A1.occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
      V i (AS.Tag l (AS.Vfun f ρ1 xs e)) (AT.Tag w (AT.Vfun f ρ2 xs e')).
  Proof.
    unfold trans_correct.
    intros HW He i.
    induction i; simpl; intros; auto;
      repeat (split; auto);
      intros; (repeat split; auto);
      intros.

    apply (He _ (i - (i - j)) ρ3 ρ4); auto.
    - eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))); eauto.
      eapply G_set_lists; eauto.
      eapply G_set; eauto.
      + apply G_mono with (S i); eauto; lia.
      + apply V_mono with i; try lia.
        eapply IHi with (Γ2 := Γ2); eauto.
        apply G_mono with (S i); eauto; lia.
      + apply Included_refl.
  Qed.

  Lemma fun_compat Γ e e' k k' f l w xs :
    W ! l = Some w ->
    trans_correct (FromList xs :|: (f |: Γ)) e e' ->
    trans_correct (f |: Γ) k k' ->
    trans_correct Γ (AS.Efun f l xs e k) (AT.Efun f w xs e' k').
  Proof.
    unfold trans_correct, E, E'.
    intros HWl He Hk.
    intros.
    unfold web_map_inv in H.
    assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Efun f l xs e k) j1 r1) by (eapply H; eauto; lia).
    inv H2.
    - exists 0, A1.OOT; split; simpl; eauto.
    - inv Hcbstep; inv H3.
      inv H4; invc.
      edestruct (Hk ex (i - 1) (M.set f (AS.Tag l (AS.Vfun f ρ1 xs e)) ρ1) (M.set f (AT.Tag w0 (AT.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + unfold web_map_inv.
        intros.
        assert (Hcbstep_k : cbstep_fuel ex ρ1 (AS.Efun f l xs e k) (S i0) r).
        {
          eapply H; eauto; try lia.
        }
        inv H2; eauto.
        inv Hcbstep_k; auto.
        econstructor; eauto.
        inv H4.
        inv H16; auto.
      + eapply G_subset with (Γ2 := (f |: AT.occurs_free (AT.Efun f w0 xs e' k'))).
        eapply G_set; eauto.
        eapply G_mono with i; eauto; lia.
        * eapply Vfun_V; eauto.
          -- eapply G_wf_env_r; eauto.
          -- apply G_mono with i; eauto; lia.
          -- apply A1.free_fun_e_subset.
        * apply Included_refl.
        * apply A1.free_fun_k_subset.
      + exists (S j2), r2; split; auto.
        * constructor; simpl; auto.
          destruct ex; simpl in *; auto.
          eapply bstep_fuel_exposed_inv; eauto.
        * eapply R_mono; eauto; lia.
  Qed.

  Lemma app_compat Γ xs f l w :
    (W ! l = Some w) ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct Γ (AS.Eapp f l xs) (AT.Eapp f w xs).
  Proof.
    unfold trans_correct, web_map_inv, E, E'.
    intros HW Hf Hxs.
    intros; simpl.

    assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Eapp f l xs) j1 r1).
    {
      eapply H; eauto; lia.
    }

    inv H2.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv Hcbstep; inv H3.
      inv H4; invc.
      edestruct (G_get H0 f) as [fv2 [Heqfv2 HV]]; eauto.
      destruct i.
      inv H1.
      destruct fv2; simpl in HV;
        destruct HV as [Hv1 HV];
        destruct v.
      2 : { destruct HV as [_ [_ Hc]]; contradiction. }

      destruct HV as [HWl' [Hex [Hlen HV]]]; invc.

      edestruct (G_get_list H0 xs vs0) as [vs2 [Heqvs2 Vvs]]; eauto.
      eapply AT.free_app_xs_subset; eauto.

      destruct (set_lists_length3 (M.set v (AT.Tag w (AT.Vfun v t l0 e)) t) l0 vs2) as [ρ4 Heqρ4].
      unfold wval in *.
      rewrite <- (Forall2_length _ _ _ Vvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H12); auto.

      assert (HE : E (exposedb w) (i - (i - i)) ρ''0 e0 ρ4 e).
      {
        eapply (HV i vs0 vs2); eauto.
        intros.
        destruct H18; auto.
        eapply V_exposed_Forall; eauto.
        apply V_mono_Forall with (S i); auto; lia.

        unfold web_map_inv; intros.
        assert (Hcbstep_e : cbstep_fuel ex ρ1 (AS.Eapp f l xs) (S i0) r).
        {
          eapply H; eauto; try lia.
        }
        inv Hcbstep_e.
        inv H4; invc; auto.
      }

      apply (E_mono _ i) in HE; try lia.
      unfold E in HE.
      destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
      exists (S j2), r2; split; eauto.
      constructor; auto.
      + econstructor; eauto.
        intros.
        destruct (exposed_reflect w); try contradiction; auto; split.
        * destruct H18; auto.
          eapply V_exposed_Forall; eauto.
        * pose proof He0 as Hr2.
          destruct (exposed_reflect w); try contradiction.
          apply bstep_fuel_exposed_inv in Hr2; auto.
      + destruct ex; simpl in *; auto.
        unfold R' in Rr.
        destruct r1.
        * destruct r2; auto; contradiction.
        * destruct r2; try contradiction.
          destruct w1.
          eapply V_exposed_res; eauto.
  Qed.

  Lemma letapp_compat Γ k k' xs x f l w :
    W ! l = Some w ->
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct (x |: Γ) k k' ->
    trans_correct Γ (AS.Eletapp x f l xs k) (AT.Eletapp x f w xs k').
  Proof.
    unfold trans_correct, web_map_inv, E, E'.
    intros HWl Hf Hxs Hk.
    intros; simpl.

    pose proof H2 as Hbstep.
    assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Eletapp x f l xs k) j1 r1) by (eapply H; eauto; lia).

    inv H2.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv H3.
      2 : { eexists; eexists; split; eauto.
            unfold R'; auto. }
      inv Hcbstep.
      inv H3; invc.
      2 : { eexists; eexists; split; eauto.
            unfold R'; auto. }
      edestruct (G_get H0 f) as [fv2 [Heqfv2 HV]]; eauto.
      destruct i. inv H1.
      destruct fv2; simpl in HV;
        destruct HV as [Hv1 [Hl' [Hex HV]]]; invc;
        destruct v1; try contradiction.
      destruct HV as [Hlen HV].

      edestruct (G_get_list H0 xs vs0) as [vs2 [Heqvs2 Vvs]]; eauto.
      eapply AT.free_letapp_xs_subset; eauto.

      destruct (set_lists_length3 (M.set v1 (AT.Tag w (AT.Vfun v1 t l0 e)) t) l0 vs2) as [ρ4 Heqρ4].
      {
        unfold wval in *.
        rewrite <- (Forall2_length _ _ _ Vvs).
        rewrite <- (set_lists_length_eq _ _ _ _ H12); auto.
      }

      assert (Hc : c0 = c /\ v = v0) by (eapply cbstep_fuel_bstep_fuel; eauto).
      assert (Hc' : c'0 = c') by lia.
      inv Hc.

      assert (HE : E (exposedb w) (i - (i - i)) ρ''0 e0 ρ4 e).
      {
        eapply (HV i vs0 vs2); eauto.
        intros.
        destruct H23; auto.
        eapply V_exposed_Forall; eauto.
        apply V_mono_Forall with (S i); auto; lia.

        unfold web_map_inv; intros.
        destruct r.
        - assert (Hcbstep_e : cbstep_fuel ex ρ1 (AS.Eletapp x f l xs k) (S i0) AS.OOT).
          {
            eapply H; eauto; try lia.
          }
          inv Hcbstep_e.
          inv H4; invc; eauto.
          assert (Hc : c = c0 /\ v0 = v).
          {
            eapply cbstep_fuel_bstep_fuel; eauto.
          }
          inv Hc.
          eapply AS.bstep_fuel_lt_Res_not_OOT with (c0 := (c0 + c'0)) in H13; eauto; try lia.
          contradiction.
        - assert (Hcv : v0 = w0 /\ c = i0).
          {
            eapply AS.bstep_fuel_deterministic; eauto.
          }
          inv Hcv.

          assert (Hcbstep_e : cbstep_fuel ex ρ1 (AS.Eletapp x f l xs k) (S (i0 + c')) r1).
          {
            eapply H; eauto; try lia.
          }
          inv Hcbstep_e.
          inv H4; invc; eauto.
      }

      apply (E_mono _ i) in HE; try lia.
      unfold E in HE.
      destruct (HE c (AS.Res v0)) as [j1 [ra [Hap Rra]]]; try lia; auto.

      simpl in Rra.
      destruct ra; try contradiction.

      edestruct (Hk ex (i - c) (M.set x v0 ρ1) (M.set x w0 ρ2))
        with (j1 := c') (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + intros.
        assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Eletapp x f l xs k) (S (c + i0)) r).
        {
          eapply H; eauto; try lia.
        }
        inv Hcbstep.
        inv H4; invc; eauto.
        * assert (Hcv : v0 = v /\ c = c0).
          {
            eapply cbstep_fuel_deterministic; eauto.
          }
          inv Hcv.
          rewrite_math (c'0 = i0); eauto.
        * eapply cbstep_fuel_to_bstep_fuel in H26; eauto.
          eapply AS.bstep_fuel_lt_Res_not_OOT with (c0 := (c + i0)) in H26; eauto; try lia.
      + eapply G_subset with (Γ2 := (x |: (AT.occurs_free (AT.Eletapp x f w xs k')))).
        ++ eapply G_set; eauto.
           eapply G_mono with (S i); eauto; lia.
        ++ apply Included_refl.
        ++ apply AT.free_letapp_k_subset.
      + exists (S (j1 + j2)), r2; split.
        ++ constructor; auto.
           ** eapply AT.BStep_letapp_Res; eauto.
              intros.
              destruct H23; auto.
              split.
              --- eapply V_exposed_Forall; eauto.
              --- eapply V_exposed; eauto.
           ** destruct ex; simpl in *; auto.
              unfold R' in Rr.
              destruct r1; destruct r2; try contradiction; auto.
              destruct w1.
              eapply V_exposed_res; eauto.
        ++ eapply R_mono; eauto; lia.
  Qed.

  Lemma constr_compat Γ x l w t xs k k' :
    W ! l = Some w ->
    (FromList xs \subset Γ) ->
    trans_correct (x |: Γ) k k' ->
    trans_correct Γ (AS.Econstr x l t xs k) (AT.Econstr x w t xs k').
  Proof.
    unfold trans_correct, E, E'.
    intros HWl Hxs Hk.
    intros; simpl.

    assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Econstr x l t xs k) j1 r1) by (eapply H; eauto).

    inv H2.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv Hcbstep; inv H3.
      inv H4; invc.
      edestruct (G_get_list H0 xs vs0) as [vs' [Heqvs' Vvs]]; eauto.
      eapply AT.free_constr_xs_subset; eauto.

      assert (Hlen : length vs0 = length vs').
      { unfold wval in *.
        rewrite <- (Forall2_length _ _ _ Vvs); auto. }

      edestruct (Hk ex i (M.set x (AS.Tag l (AS.Vconstr t vs0)) ρ1)
                      (M.set x (AT.Tag w0 (AT.Vconstr t vs')) ρ2))
        with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + unfold web_map_inv in *.
        intros.
        assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Econstr x l t xs k) (S i0) r).
        {
          eapply H; eauto.
        }
        inv Hcbstep.
        inv H4; invc; eauto.
      + eapply G_subset with (Γ2 := (x |: (AT.occurs_free (AT.Econstr x w0 t xs k')))).
        * eapply G_set; eauto.

          assert (Hexvs : Ensembles.In web Exposed w0 -> Forall exposed vs').
          {
            intros.
            eapply V_exposed_Forall; eauto.
          }

          assert (Hex : Ensembles.In web Exposed w0 -> exposed (AT.Tag w0 (AT.Vconstr t vs'))) by eauto.
          assert (Hwf : wf_val (AT.Tag w0 (AT.Vconstr t vs'))).
          {
            eapply wf_val_Vconstr; eauto.
            eapply V_wf_val_Forall_r; eauto.
          }

          destruct i; simpl; repeat (split; auto).
          eapply V_mono_Forall; eauto; lia.
        * apply Included_refl.
        * apply AT.free_constr_k_subset.
      + exists (S j2), r2; split.
        * constructor; auto.
          -- econstructor; eauto.
             intros.
             eapply V_exposed_Forall; eauto.
          -- destruct ex; simpl in *; auto.
             unfold R' in Rr.
             destruct r1; destruct r2; try contradiction; auto.
             eapply V_exposed_res; eauto.
        * eapply R_mono; eauto; lia.
  Qed.

  Lemma proj_compat Γ x l w n y k k' :
    W ! l = Some w ->
    (y \in Γ) ->
    trans_correct (x |: Γ) k k' ->
    trans_correct Γ (AS.Eproj x l n y k) (AT.Eproj x w n y k').
  Proof.
    unfold trans_correct, E, E'.
    intros HWl Hy Hk.
    intros; simpl.

    assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Eproj x l n y k) j1 r1) by (eapply H; eauto).

    inv H2.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv Hcbstep; inv H3.
      inv H4; invc.
      edestruct (G_get H0 y) as [v2 [Heqv2 HV]]; eauto.
      destruct i. inv H1.
      destruct v2; simpl in HV;
        destruct HV as [Hv1 HV];
        destruct v.
      destruct HV as [_ [_ Hc]]; contradiction.
      destruct HV as [HWl' [Hex [Heqt HFvs]]]; subst; invc.

      destruct (Forall2_nth_error H13 HFvs) as [v2' [Heqv2' HVv]].

      edestruct (Hk ex i (M.set x v0 ρ1) (M.set x v2' ρ2))
        with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + unfold web_map_inv in *; intros.
        assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Eproj x l n y k) (S i0) r) by (eapply H; eauto).
        inv Hcbstep.
        inv H4; invc; eauto.
      + eapply G_subset with (Γ2 := (x |: (AT.occurs_free (AT.Eproj x w n y k')))).
        * eapply G_set; eauto.
          eapply G_mono with (S i); eauto; lia.
        * apply Included_refl.
        * apply AT.free_proj_k_subset.
      + exists (S j2), r2; split.
        * constructor; auto.
          -- econstructor; eauto.
          -- destruct ex; simpl in *; auto.
             unfold R' in Rr.
             destruct r1; destruct r2; try contradiction; auto.
             destruct w0.
             eapply V_exposed_res; eauto.
        * eapply R_mono; eauto; lia.
  Qed.

  Lemma case_nil_compat Γ x l w :
    W ! l = Some w ->
    (x \in Γ) ->
    trans_correct Γ (AS.Ecase x l []) (AT.Ecase x w []).
  Proof.
    unfold trans_correct, E, E'.
    intros HWl Hx.
    intros; simpl.
    inv H2.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv H3.
      inv H9.
  Qed.

  Lemma case_cons_compat Γ x l w t e e' cl cl' :
    W ! l = Some w ->
    (x \in Γ) ->
    trans_correct Γ e e' ->
    trans_correct Γ (AS.Ecase x l cl) (AT.Ecase x w cl') ->
    trans_correct Γ (AS.Ecase x l ((t, e) :: cl)) (AT.Ecase x w ((t, e') :: cl')).
  Proof.
    unfold trans_correct, E, E'.
    intros HWl Hx He Hcl.
    intros; simpl.

    assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Ecase x l ((t, e) :: cl)) j1 r1) by (eapply H; eauto).

    inv H2.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv Hcbstep; inv H3.
      inv H4; invc.
      edestruct (G_get H0 x) as [v2 [Heqv2 HV]]; eauto.
      destruct i. inv H1.
      destruct v2; simpl in HV;
        destruct HV as [Hv1 HV];
        destruct v.
      { destruct HV as [_ [_ Hc]]; contradiction. }
      destruct HV as [HWl' [Hex [Heqt HFvs]]]; subst.

      assert (Heqe : e0 = e1).
      {
        eapply find_tag_deterministic; eauto.
      }

      inv H9; invc.
      + (* head tag matches *)
        edestruct (He ex (S i) ρ1 ρ2)
          with (j1 := c) (r1 := r1) as [j2 [r2 [He2 Rr]]]; eauto; try lia.
        * unfold web_map_inv in *; intros.

          assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Ecase x l ((c0, e1) :: cl)) (S i0) r) by (eapply H; eauto).
          inv Hcbstep.
          inv H4; invc.

          assert (Heqe : e = e1).
          {
            eapply find_tag_deterministic; eauto.
          }
          inv Heqe; eauto.
        * eapply G_subset; eauto.
          apply Included_refl.
          apply AT.free_case_hd_subset.
        * exists (S j2), r2; split; auto.
          inv He2; auto.
          constructor; auto.
          econstructor; eauto.
          destruct ex; auto.
          econstructor; eauto.
          eapply R_mono; eauto; lia.
      + (* tail: recurse on cl/cl' *)
        inv H11; try contradiction.
        edestruct (Hcl ex (S i) ρ1 ρ2)
          with (j1 := S c) (r1 := r1) as [j2 [r2 [Hcl2 Rr]]]; eauto; try lia.
        * unfold web_map_inv in *; intros.
          inv H2; auto.
          inv H3; invc.
          assert (Hcbstep : cbstep_fuel ex ρ1 (AS.Ecase x l ((t, e) :: cl)) (S c1) r).
          {
            eapply H; eauto.
          }
          assert (Heqe : e1 = e0) by (eapply find_tag_deterministic; eauto).
          inv Heqe.

          inv Hcbstep.
          inv H3; invc.
          inv H17; eauto; contradiction.
        * eapply G_subset; eauto.
          apply Included_refl.
          apply AT.free_case_tl_subset; auto.
        * exists j2, r2; split; auto.
          inv Hcl2; auto.
          inv H2; invc; eauto.
  Qed.

  (* Fundamental Property *)
  Lemma fundamental_property {Γ e e'}:
    trans Γ e e' -> trans_correct Γ e e'.
  Proof.
    intros.
    induction H; intros.
    - eapply ret_compat; eauto.
    - eapply fun_compat; eauto.
    - eapply app_compat; eauto.
    - eapply letapp_compat; eauto.
    - eapply constr_compat; eauto.
    - eapply proj_compat; eauto.
    - eapply case_nil_compat; eauto.
    - eapply case_cons_compat; eauto.
  Qed.

End Collecting.

Section Approx.

  Definition leq W1 W2 :=
    exists f : web -> web,
      (forall w, w \in Exposed <-> f w \in Exposed) /\
      (forall l w, W1 ! l = Some w -> W2 ! l = Some (f w)).

  Lemma leq_refl W :
    leq W W.
  Proof.
    unfold leq.
    exists (fun x => x).
    sfirstorder.
  Qed.

  Lemma leq_trans W1 W2 W3 :
    leq W1 W2 ->
    leq W2 W3 ->
    leq W1 W3.
  Proof.
    intros [f1 [Hf1_iff Hf1_W]] [f2 [Hf2_iff Hf2_W]].
    exists (fun w => f2 (f1 w)).
    split.
    - intro w. rewrite Hf1_iff. apply Hf2_iff.
    - intros l w HW1.
      apply Hf1_W in HW1.
      apply Hf2_W in HW1.
      exact HW1.
  Qed.

  Lemma leq_exposed l w1 v W1 W2:
    W1 ! l = Some w1 ->
    leq W1 W2 ->
    exposed (TAG val w1 v) ->
    exists w2, W2 ! l = Some w2 /\ (w2 \in Exposed).
  Proof. qauto unfold: wval, Tag, Ensembles.In, leq inv: exposed. Qed.

  (* We rely on `exposed_singleton` so that we can look up the same exposed web *)
  Lemma leq_single_exposed l w v W1 W2:
    W1 ! l = Some w ->
    leq W1 W2 ->
    exposed (TAG val w v) ->
    W2 ! l = Some w.
  Proof.
    intros HW1 Hleq Hexp.
    destruct (leq_exposed _ _ _ _ _ HW1 Hleq Hexp) as [w2 [HW2 Hw2_exp]].
    assert (Hw_exp : w \in Exposed) by (inv Hexp; auto).
    apply Exposed_singleton in Hw_exp.
    apply Exposed_singleton in Hw2_exp.
    congruence.
  Qed.

  Lemma cbstep_approx W1 W2 ex ρ e i r :
    leq W1 W2 ->
    cbstep W1 ex ρ e i r ->
    cbstep W2 ex ρ e i r.
  Proof.
    intros Hleq Hcb.
    destruct Hleq as [f [Hf_iff Hf_W]].
    assert (Hexposedb : forall w, exposedb (f w) = exposedb w).
    { intro w.
      destruct (exposed_reflect w), (exposed_reflect (f w)); auto.
      - exfalso. apply n. apply -> Hf_iff; auto.
      - exfalso. apply n. apply Hf_iff; auto. }
    assert (Hto_exposed : forall v, to_exposed W1 v -> to_exposed W2 v).
    { intros [l_v v_inner] [w' [HW1' Hw'_exp]].
      exists (f w'); split; auto.
      apply -> Hf_iff; auto. }
    assert (Hto_exposed_res : forall r0, to_exposed_res W1 r0 -> to_exposed_res W2 r0).
    { intros [|v_r] Hr; simpl in *; auto. }
    assert (Hto_exposed_F : forall vs, Forall (to_exposed W1) vs -> Forall (to_exposed W2) vs).
    { intros vs Hvs; induction Hvs; constructor; auto. }
    induction Hcb using cbstep_ind' with
      (P  := fun ex ρ e i r => cbstep W2 ex ρ e i r)
      (P0 := fun ex ρ e i r => cbstep_fuel W2 ex ρ e i r); intros.
    - eapply Cbstep_ret; eauto.
    - eapply Cbstep_fun; eauto.
    - eapply Cbstep_app with (w := f w); eauto.
      + intros Hfw_exp.
        assert (Hw_exp : w \in Exposed) by (apply Hf_iff; auto).
        destruct (H4 Hw_exp) as [Hvs Hr].
        split; auto.
      + rewrite Hexposedb; auto.
    - eapply Cbstep_letapp_Res with (w := f w); eauto.
      + rewrite Hexposedb; auto.
      + intros Hfw_exp.
        assert (Hw_exp : w \in Exposed) by (apply Hf_iff; auto).
        destruct (H6 Hw_exp) as [Hvs Hv].
        split; auto.
    - eapply Cbstep_letapp_OOT with (w := f w); eauto.
      + rewrite Hexposedb; auto.
      + intros Hfw_exp.
        assert (Hw_exp : w \in Exposed) by (apply Hf_iff; auto).
        apply Hto_exposed_F; auto.
    - eapply Cbstep_constr; eauto.
      intros Hfw_exp.
      assert (Hw_exp : w \in Exposed) by (apply Hf_iff; auto).
      apply Hto_exposed_F; auto.
    - eapply Cbstep_proj with (w := f w); eauto.
    - eapply Cbstep_case with (w := f w); eauto.
    - constructor.
    - constructor; auto.
      destruct ex; auto.
  Qed.

  Lemma cbstep_fuel_approx W1 W2 ex ρ e i r :
    leq W1 W2 ->
    cbstep_fuel W1 ex ρ e i r ->
    cbstep_fuel W2 ex ρ e i r.
  Proof.
    intros Hleq Hcbf.
    inv Hcbf.
    - constructor.
    - constructor.
      + eapply cbstep_approx; eauto.
      + destruct ex; auto.
        destruct r as [|[l_v v_inner]]; simpl in *; auto.
        destruct Hleq as [f [Hf_iff Hf_W]].
        destruct H0 as [w' [HW1' Hw'_exp]].
        exists (f w'); split.
        * apply Hf_W; auto.
        * apply -> Hf_iff; auto.
  Qed.

  Lemma web_map_inv_approx W1 W2 ex ρ e:
    leq W1 W2 ->
    web_map_inv W1 ex ρ e ->
    web_map_inv W2 ex ρ e.
  Proof.
    unfold web_map_inv.
    intros.
    eapply H0 in H1; eauto.
    eapply cbstep_fuel_approx; eauto.
  Qed.

  Lemma V_approx_Forall_aux :
    forall i W1 W2,
      (forall m : nat,
          m < S i ->
          forall W1 W2 v1 v2,
            exposed v2 ->
            leq W1 W2 ->
            V W1 m v1 v2 <-> V W2 m v1 v2) ->
      leq W1 W2 ->
      forall j vs1 vs2,
        j <= i ->
        Forall exposed vs2 ->
        Forall2 (V W1 j) vs1 vs2 <-> Forall2 (V W2 j) vs1 vs2.
  Proof.
    intros.
    revert vs1 j H1.
    induction H2; simpl; intros.
    - split; intros; inv H2; auto.
    - split; intros; inv H4; constructor; auto;
        try solve [ eapply H; try lia; eauto |
                    eapply IHForall; eauto ].
      fcrush.
  Qed.

  (* This doesn't work because of the <-> *)
  Lemma V_approx :
    forall i W1 W2 v1 v2,
      exposed v2 ->
      leq W1 W2 ->
      (V W1 i v1 v2 <-> V W2 i v1 v2).
  Proof.
    intro i.
    induction i using lt_wf_rec; intros.
    split; intros.
    - destruct i; simpl in *;
        inv H2; split; auto;
        destruct v1; destruct v2.
      + assert (HW2 : W2 ! l = Some w) by (eapply leq_single_exposed; fcrush).
        fcrush.
      + destruct H4 as [Hl [Hex HV]].
        repeat (split; auto).
        eapply leq_single_exposed; eauto.
        destruct v; destruct v0; try contradiction.
        * destruct HV as [Hlen HV].
          split; auto; intros.

          assert (HE : E' (V W1) (exposedb w) (i - (i - j)) ρ3 e ρ4 e0).
          {
            eapply HV; eauto.
            eapply V_approx_Forall_aux; eauto; try lia.
            fcrush.
            admit.
          }
          unfold E' in *; intros.
          edestruct HE as [j2 [r2 [Hstep HR]]]; eauto.
          eexists; eexists; split; eauto.
          unfold R' in *.
          destruct r1; destruct r2; auto.
          eapply H with (W1 := W1); eauto; try lia.
          destruct (exposed_reflect w); try contradiction.
          eapply AT.bstep_fuel_exposed_inv in Hstep; eauto; fcrush.
          exfalso.
          inv H0; contradiction.
        * inv HV.
          split; auto.
          eapply V_approx_Forall_aux with (W1 := W1); eauto.
          fcrush.
    - admit.
  Abort.

End Approx.

Section Top.

  (* Top Level *)
  Definition G_top W i Γ1 ρ1 Γ2 ρ2 :=
    wf_env ρ2 /\
    Γ2 \subset Γ1 /\
    forall x,
      (x \in Γ1) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
        M.get x ρ2 = Some v2 /\
        exposed v2 /\
        V W i v1 v2.

  Lemma G_top_wf_env_r W i Γ1 ρ1 Γ2 ρ2 :
    G_top W i Γ1 ρ1 Γ2 ρ2 ->
    wf_env ρ2.
  Proof.
    unfold G_top.
    intros; tauto.
  Qed.

  Lemma G_top_subset W i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4 :
    G_top W i Γ1 ρ1 Γ2 ρ2 ->
    Γ3 \subset Γ1 ->
    Γ4 \subset Γ3 ->
    G_top W i Γ3 ρ1 Γ4 ρ2.
  Proof.
    unfold G_top.
    intros.
    destruct H as [Hr [Hs HG]].
    repeat (split; auto).
  Qed.

  Lemma G_top_G :
    forall {W i Γ1 ρ1 Γ2 ρ2},
      G_top W i Γ1 ρ1 Γ2 ρ2 ->
      G W i Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold G_top, G.
    intros.
    destruct H as [HΓ [Hρ HG]].
    unfold Ensembles.Included, Ensembles.In, Dom_map in *.
    split; auto; intros.
    edestruct HG as [v1' [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto.
    rewrite Heqv1 in H0; inv H0; eauto.
  Qed.

  Definition trans_correct_top W etop etop' :=
    AT.occurs_free etop' \subset AS.occurs_free etop /\
      forall i W' ρ1 ρ2,
        web_map_inv W true ρ1 etop ->
        leq W W' ->
        G_top W' i (AS.occurs_free etop) ρ1 (AT.occurs_free etop') ρ2 ->
        E W' true i ρ1 etop ρ2 etop'.

  Lemma trans_correct_top_subset W e1 e2 :
    trans_correct_top W e1 e2 ->
    AT.occurs_free e2 \subset AS.occurs_free e1.
  Proof.
    unfold trans_correct_top.
    intros.
    inv H; auto.
  Qed.

  Theorem top W etop etop':
    trans W (AS.occurs_free etop) etop etop' ->
    trans_correct_top W etop etop'.
  Proof.
    unfold trans_correct_top.
    intros H.
    split.
    - eapply trans_exp_inv; eauto.
    - intros.
      specialize (fundamental_property _ H);
        unfold trans_correct; intros.
  Abort.

  Theorem top W etop etop':
    (forall W',
        leq W W' ->
        trans W' (AS.occurs_free etop) etop etop') ->
    trans_correct_top W etop etop'.
  Proof.
    unfold trans_correct_top.
    intros H.
    split.
    - specialize (H W).
      assert (leq W W) by (apply leq_refl; auto).
      eapply trans_exp_inv; eauto.
    - intros.
      specialize (H _ H1).
      specialize (fundamental_property _ H);
        unfold trans_correct; intros.
      eapply H3; eauto.
      eapply web_map_inv_approx; eauto.
      eapply G_top_G; eauto.
  Qed.

  Theorem trans_correct_upward_approx W1 e1 e2 :
    (forall W2,
        leq W1 W2 ->
        trans_correct_top W2 e1 e2) ->
    trans_correct_top W1 e1 e2.
  Proof.
    unfold trans_correct_top.
    intros.
    split.
    - specialize (H W1).
      assert (leq W1 W1) by (apply leq_refl; auto).
      firstorder.
    - intros.
      eapply H; eauto.
      eapply web_map_inv_approx; eauto.
      apply leq_refl.
  Qed.

  Theorem trans_correct_downward_approx W2 e1 e2 :
    (forall W1,
        leq W1 W2 ->
        trans_correct_top W1 e1 e2) ->
    trans_correct_top W2 e1 e2.
  Proof.
    unfold trans_correct_top.
    intros.
    split.
    - specialize (H W2).
      assert (leq W2 W2) by (apply leq_refl; auto).
      firstorder.
    - intros.
      eapply H; eauto.
      apply leq_refl.
  Qed.

End Top.

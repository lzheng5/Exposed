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

(* Checking Semantics *)

Section Checking.

  (* Tagged Value *)
  Inductive ctag A : Type :=
  | CTAG : label -> web_map -> A -> ctag A.

  Hint Constructors tag : core.

  (* Value *)
  Inductive cval : Type :=
  | CVfun : var -> M.t (ctag cval) -> list var -> AS.exp -> cval (* Need to capture a web_map for the function body exp *)
  | CVconstr : ctor_tag -> list (ctag cval) -> cval.

  Hint Constructors cval : core.

  Definition clval := ctag cval.

  Definition CTag l W cv := CTAG cval l W cv.

  (* Environment *)
  Definition cenv := M.t clval.

  (* Result *)
  Inductive cres : Type :=
  | COOT
  | CRes : clval -> cres.

  Hint Constructors cres : core.

  Definition to_exposed (tv : clval) : Prop :=
    match tv with
    | CTAG _ l W v => exists w, W ! l = Some w /\ (w \in Exposed)
    end.

  Definition to_exposed_res (r : cres) : Prop :=
    match r with
    | COOT => True
    | CRes v => to_exposed v
    end.

  (* Checking Semantics *)
  (* `W` is a valid analysis result with respect to the checking big-step semantics *)
  Inductive cbstep (W : web_map) (ex : bool) (ρ : cenv) : AS.exp -> fuel -> cres -> Prop :=
  | Cbstep_ret :
    forall {x v},
      M.get x ρ = Some v ->
      cbstep W ex ρ (AS.Eret x) 0 (CRes v)

  | Cbstep_fun :
    forall {f l w xs e k c r},
      W ! l = Some w ->
      cbstep_fuel W ex (M.set f (CTag l W (CVfun f ρ xs e)) ρ) k c r ->
      cbstep W ex ρ (AS.Efun f l xs e k) c r

  | Cbstep_app :
    forall {W' f f' l l' w xs ρ' xs' e vs ρ'' c r},
      M.get f ρ = Some (CTag l' W' (CVfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (CTag l' W' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      W ! l = Some w -> (* W controls caller *)
      W' ! l' = Some w -> (* W' controls callee *)
      (w \in Exposed -> Forall to_exposed vs /\ to_exposed_res r) -> (* Doesn't matter which W as long as `vs` and `r` are mapped to exposed web ids. *)
      cbstep_fuel W' (exposedb w) ρ'' e c r ->
      cbstep W ex ρ (AS.Eapp f l xs) c r

  | Cbstep_letapp_Res :
    forall {W' x f f' l l' w xs k ρ' xs' e vs ρ'' c c' v r},
      M.get f ρ = Some (CTag l' W' (CVfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (CTag l' W' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      W ! l = Some w ->
      W' ! l' = Some w ->
      cbstep_fuel W' (exposedb w) ρ'' e c (CRes v) ->
      cbstep_fuel W ex (M.set x v ρ) k c' r ->
      (w \in Exposed -> Forall to_exposed vs /\ to_exposed v) ->
      cbstep W ex ρ (AS.Eletapp x f l xs k) (c + c') r

  | Cbstep_letapp_OOT :
    forall {W' x f f' l l' w xs k ρ' xs' e vs ρ'' c},
      M.get f ρ = Some (CTag l' W' (CVfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (CTag l' W' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      W ! l = Some w ->
      W' ! l' = Some w ->
      cbstep_fuel W' (exposedb w) ρ'' e c COOT ->
      (w \in Exposed -> Forall to_exposed vs) ->
      cbstep W ex ρ (AS.Eletapp x f l xs k) c COOT

  | Cbstep_constr :
    forall {x l w t xs e r vs c},
      get_list xs ρ = Some vs ->
      W ! l = Some w ->
      (w \in Exposed -> Forall to_exposed vs) ->
      cbstep_fuel W ex (M.set x (CTag l W (CVconstr t vs)) ρ) e c r ->
      cbstep W ex ρ (AS.Econstr x l t xs e) c r

  | Cbstep_proj :
    forall {W' x l l' w t i y e c r v vs},
      M.get y ρ = Some (CTag l' W' (CVconstr t vs)) ->
      nth_error vs i = Some v ->
      W ! l = Some w ->
      W' ! l' = Some w ->
      cbstep_fuel W ex (M.set x v ρ) e c r ->
      cbstep W ex ρ (AS.Eproj x l i y e) c r

  | Cbstep_case :
    forall {W' x l l' w cl t e r c vs},
      M.get x ρ = Some (CTag l' W' (CVconstr t vs)) ->
      find_tag cl t e ->
      W ! l = Some w ->
      W' ! l' = Some w ->
      cbstep_fuel W ex ρ e c r ->
      cbstep W ex ρ (AS.Ecase x l cl) c r

  with cbstep_fuel (W : web_map) (ex : bool) (ρ : cenv) : AS.exp -> fuel -> cres -> Prop :=
  | CbstepF_OOT :
    forall {e},
      cbstep_fuel W ex ρ e 0 COOT

  | CbstepF_Step :
    forall {e c r},
      cbstep W ex ρ e c r ->
      (if ex then to_exposed_res r else True) ->
      cbstep_fuel W ex ρ e (S c) r.

  Hint Constructors cbstep : core.
  Hint Constructors cbstep_fuel : core.

  Scheme cbstep_ind' := Minimality for cbstep Sort Prop
  with cbstep_fuel_ind' := Minimality for cbstep_fuel Sort Prop.

  Theorem cbstep_deterministic v v' {W ex ρ e c c' r r'}:
    cbstep W ex ρ e c r ->
    cbstep W ex ρ e c' r' ->
    r = CRes v ->
    r' = CRes v' ->
    (v = v' /\ c = c').
  Proof.
    intros H.
    generalize dependent v'.
    generalize dependent r'.
    generalize dependent c'.
    generalize dependent v.
    induction H using cbstep_ind' with (P := fun W ex ρ e c r =>
                                              forall v c' r' v',
                                                cbstep W ex ρ e c' r' ->
                                                r = CRes v -> r' = CRes v' ->
                                                v = v' /\ c = c')
                                      (P0 := fun W ex ρ e c r =>
                                               forall v c' r' v',
                                                 cbstep_fuel W ex ρ e c' r' ->
                                                 r = CRes v -> r' = CRes v' ->
                                                 v = v' /\ c = c');
      intros; subst.
    - inv H0; inv H1; invc; auto.
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

  Theorem cbstep_fuel_deterministic v v' {W ex ρ e c c' r r'}:
    cbstep_fuel W ex ρ e c r ->
    cbstep_fuel W ex ρ e c' r' ->
    r = CRes v ->
    r' = CRes v' ->
    (v = v' /\ c = c').
  Proof.
    intros.
    inv H; inv H0; try discriminate.
    edestruct (cbstep_deterministic v v' H3 H); eauto.
  Qed.

  (* Valid W Specification *)
  Inductive web_map_inv (W : web_map) (Γ : vars) : AS.exp -> Prop :=
  | Web_Map_Inv_ret :
    forall x,
      (x \in Γ) ->
      web_map_inv W Γ (AS.Eret x)

  | Web_Map_Inv_fun :
    forall {f l w xs e k},
      W ! l = Some w ->
      web_map_inv W (FromList xs :|: (f |: Γ)) e ->
      web_map_inv W (f |: Γ) k ->
      web_map_inv W Γ (AS.Efun f l xs e k)

  | Web_Map_Inv_app :
    forall {f l w xs},
      W ! l = Some w ->
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      web_map_inv W Γ (AS.Eapp f l xs)

  | Web_Map_Inv_letapp :
    forall {x f l w xs k},
      W ! l = Some w ->
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      web_map_inv W (x |: Γ) k ->
      web_map_inv W Γ (AS.Eletapp x f l xs k)

  | Web_Map_Inv_constr :
    forall {x l w t xs k},
      W ! l = Some w ->
      (FromList xs \subset Γ) ->
      web_map_inv W (x |: Γ) k ->
      web_map_inv W Γ (AS.Econstr x l t xs k)

  | Web_Map_Inv_proj :
    forall {l w x y k n},
      W ! l = Some w ->
      (y \in Γ) ->
      web_map_inv W (x |: Γ) k ->
      web_map_inv W Γ (AS.Eproj x l n y k)

  | Web_Map_Inv_case_nil :
    forall {l w x},
      W ! l = Some w ->
      (x \in Γ) ->
      web_map_inv W Γ (AS.Ecase x l [])

  | Web_Map_Inv_case_cons :
    forall {x l w e t cl},
      W ! l = Some w ->
      (x \in Γ) ->
      web_map_inv W Γ e ->
      web_map_inv W Γ (AS.Ecase x l cl) ->
      web_map_inv W Γ (AS.Ecase x l ((t, e) :: cl)).

  Hint Constructors web_map_inv : core.

  (* Cross-semantics Logical Relations *)
  Definition R' (P : nat -> AS.wval -> clval -> Prop) (i : nat) (r1 : AS.res) (r2 : cres) :=
    match r1, r2 with
    | AS.OOT, COOT => True
    | AS.Res v1, CRes v2 => P i v1 v2
    | _, _ => False
    end.

  Definition E' (P : nat -> AS.wval -> clval -> Prop) (W : web_map) (ex : bool) (i : nat) (ρ1 : AS.env) (ρ2 : cenv) (e : AS.exp) : Prop :=
    forall j1 r1,
      j1 <= i ->
      AS.bstep_fuel ρ1 e j1 r1 ->
      exists j2 r2,
        cbstep_fuel W ex ρ2 e j2 r2 /\
        R' P (i - j1) r1 r2.

  Definition well_annotated W ex ρ1 ρ2 e :=
    forall i r,
      AS.bstep_fuel ρ1 e i r ->
      match r with
      | AS.OOT => cbstep_fuel W ex ρ2 e i COOT
      | AS.Res v => exists cv, cbstep_fuel W ex ρ2 e i (CRes cv)
      end.

  Fixpoint V (i : nat) (wv : AS.wval) (cv : clval) {struct i} : Prop :=
    match wv, cv with
    | AS.TAG _ l1 v1, CTAG _ l2 W v2 =>
        l1 = l2 /\
        exists w2, W ! l2 = Some w2 /\
        match v1, v2 with
        | AS.Vconstr c1 vs1, CVconstr c2 vs2 =>
            c1 = c2 /\
            length vs1 = length vs2 /\
            match exposedb w2 with
            | true =>
                to_exposed cv /\
                match i with
                | 0 => True
                | S i0 => Forall2 (V i0) vs1 vs2
                end

            | false =>
                match i with
                | 0 => True
                | S i0 => Forall2 (V i0) vs1 vs2
                end
            end

        | AS.Vfun f1 ρ1 xs1 e1, CVfun f2 ρ2 xs2 e2 =>
            length xs1 = length xs2 /\
            e1 = e2 /\
            match exposedb w2 with
            | true =>
                match i with
                | 0 => True
                | S i0 =>
                    forall j vs1 vs2 ρ3 ρ4,
                      j <= i0 ->
                      Forall to_exposed vs2 ->
                      Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                      set_lists xs1 vs1 (M.set f1 (AS.Tag l1 (AS.Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                      set_lists xs2 vs2 (M.set f2 (CTag l2 W (CVfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                      (* well_annotated W true ρ3 ρ4 e1 -> *)
                      E' V W true (i0 - (i0 - j)) ρ3 ρ4 e1
                end

            | false =>
                match i with
                | 0 => True
                | S i0 =>
                    forall j vs1 vs2 ρ3 ρ4,
                      j <= i0 ->
                      Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                      set_lists xs1 vs1 (M.set f1 (AS.Tag l1 (AS.Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                      set_lists xs2 vs2 (M.set f2 (CTag l2 W (CVfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                      (* well_annotated W false ρ3 e1 -> *)
                      E' V W false (i0 - (i0 - j)) ρ3 ρ4 e1
                end
            end

        | _, _ => False
        end
    end.

  Definition R := (R' V).

  Definition E := (E' V).

  (* Environment Relation *)
  Definition G i Γ1 ρ1 Γ2 ρ2 :=
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
    forall i j (V : nat -> AS.wval -> clval -> Prop) vs1 vs2,
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
      destruct H0 as [Heql [w [Hw HV]]]; subst.
    - destruct v; destruct c; fcrush.
    - fcrush.
    - repeat (split; auto).
      eexists; split; eauto.
      destruct v; destruct c; try contradiction.
      + destruct HV.
        destruct (exposed_reflect w); fcrush.
      + destruct HV as [Hc [Hlen HV]]; subst.
        destruct (exposed_reflect w); fcrush.
    - repeat (split; auto).
      destruct v; destruct c; try contradiction.
      + destruct HV as [Hlen [Heqe HV]]; subst.
        eexists; repeat (split; eauto); intros.
        destruct (exposed_reflect w); intros.
        * specialize (HV j0 vs1 vs2 ρ3 ρ4).
          rewrite normalize_step in *; try lia.
          apply HV; eauto; lia.
        * specialize (HV j0 vs1 vs2 ρ3 ρ4).
          rewrite normalize_step in *; try lia.
          eapply HV; eauto; lia.
      + destruct HV as [Heqc [Hlen HV]]; subst.
        eexists; repeat (split; eauto).
        destruct (exposed_reflect w).
        * destruct HV as [[w' [Hw' Hex]] HV].
          repeat (split; eauto).
          eapply V_mono_Forall_aux; eauto; lia.
        * eapply V_mono_Forall_aux; eauto; lia.
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

  Lemma E_mono {W ex ρ1 ρ2 e} i j:
    E W ex i ρ1 ρ2 e ->
    j <= i ->
    E W ex j ρ1 ρ2 e.
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
    edestruct H as [v2 [Heqv2 HV]]; eauto.
    eexists; eexists; repeat split; eauto.
    apply V_mono with i; eauto.
  Qed.

  (* Compatibility Lemmas *)
  (* TODO: rename -> well_annotated *)
  Definition trans_correct W Γ e :=
    forall ex i ρ1 ρ2,
      G i Γ ρ1 (AS.occurs_free e) ρ2 ->
      E W ex i ρ1 ρ2 e.

  Lemma ret_compat W Γ x :
    (x \in Γ) ->
    trans_correct W Γ (AS.Eret x).
  Proof.
    unfold trans_correct, well_annotated, E, E', R, R', Ensembles.Included, Ensembles.In.
    intros; simpl.
    assert (Hcbstep : cbstep_fuel W ex ρ1 (AS.Eret x) j1 r1) by (eapply H0; eauto; try lia).
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

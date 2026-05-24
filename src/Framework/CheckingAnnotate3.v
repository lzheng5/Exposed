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

(* Annotate Based on The Checking Semantics *)

Section Checking.

  (* Value *)
  Inductive cval : Type :=
  | CVfun : var -> M.t (tag cval) -> web_map -> list var -> AS.exp -> cval (* Need to capture a web_map for the function body exp *)
  | CVconstr : ctor_tag -> list (tag cval) -> cval.

  Hint Constructors cval : core.

  Definition clval := tag cval.

  Definition Tag l cv := TAG cval l cv.

  (* Environment *)
  Definition cenv := M.t clval.

  (* Result *)
  Inductive cres : Type :=
  | COOT
  | CRes : clval -> cres.

  Hint Constructors cres : core.

  Definition to_exposed (W : web_map) (tv : clval) : Prop :=
    match tv with
    | TAG _ l v => exists w, W ! l = Some w /\ (w \in Exposed)
    end.

  Definition to_exposed_res (W : web_map) (r : cres) : Prop :=
    match r with
    | COOT => True
    | CRes v => to_exposed W v
    end.

  (* `W` is a valid analysis result with respect to the checking big-step semantics *)
  Inductive cbstep (W : web_map) (ex : bool) (ρ : cenv) : AS.exp -> fuel -> cres -> Prop :=
  | Cbstep_ret :
    forall {x l w v},
      M.get x ρ = Some (Tag l v) ->
      W ! l = Some w ->
      cbstep W ex ρ (AS.Eret x) 0 (CRes (Tag l v))

  | Cbstep_fun :
    forall {f l w xs e k c r},
      W ! l = Some w ->
      cbstep_fuel W ex (M.set f (Tag l (CVfun f ρ W xs e)) ρ) k c r ->
      cbstep W ex ρ (AS.Efun f l xs e k) c r

  | Cbstep_app :
    forall {W' f f' l l' w xs ρ' xs' e vs ρ'' c r},
      M.get f ρ = Some (Tag l' (CVfun f' ρ' W' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (Tag l' (CVfun f' ρ' W' xs' e)) ρ') = Some ρ'' ->
      W ! l = Some w ->
      W' ! l' = Some w ->
      (w \in Exposed -> Forall (to_exposed W') vs /\ to_exposed_res W' r) ->
      cbstep_fuel W' (exposedb w) ρ'' e c r ->
      cbstep W ex ρ (AS.Eapp f l xs) c r

  | Cbstep_letapp_Res :
    forall {W' x f f' l l' w xs k ρ' xs' e vs ρ'' c c' v r},
      M.get f ρ = Some (Tag l' (CVfun f' ρ' W' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (Tag l' (CVfun f' ρ' W' xs' e)) ρ') = Some ρ'' ->
      W ! l = Some w ->
      W' ! l' = Some w ->
      cbstep_fuel W' (exposedb w) ρ'' e c (CRes v) ->
      cbstep_fuel W ex (M.set x v ρ) k c' r ->
      (w \in Exposed -> Forall (to_exposed W') vs /\ to_exposed W' v) ->
      cbstep W ex ρ (AS.Eletapp x f l xs k) (c + c') r

  | Cbstep_letapp_OOT :
    forall {W' x f f' l l' w xs k ρ' xs' e vs ρ'' c},
      M.get f ρ = Some (Tag l' (CVfun f' ρ' W' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (Tag l' (CVfun f' ρ' W' xs' e)) ρ') = Some ρ'' ->
      W ! l = Some w ->
      W' ! l' = Some w ->
      cbstep_fuel W' (exposedb w) ρ'' e c COOT ->
      (w \in Exposed -> Forall (to_exposed W') vs) ->
      cbstep W ex ρ (AS.Eletapp x f l xs k) c COOT

  | Cbstep_constr :
    forall {x l w t xs e r vs c},
      get_list xs ρ = Some vs ->
      W ! l = Some w ->
      (w \in Exposed -> Forall (to_exposed W) vs) ->
      cbstep_fuel W ex (M.set x (Tag l (CVconstr t vs)) ρ) e c r ->
      cbstep W ex ρ (AS.Econstr x l t xs e) c r

  | Cbstep_proj :
    forall {x l l' w t i y e c r v vs},
      M.get y ρ = Some (Tag l' (CVconstr t vs)) ->
      nth_error vs i = Some v ->
      W ! l = Some w ->
      W ! l' = Some w ->
      cbstep_fuel W ex (M.set x v ρ) e c r ->
      cbstep W ex ρ (AS.Eproj x l i y e) c r

  | Cbstep_case :
    forall {x l l' w cl t e r c vs},
      M.get x ρ = Some (Tag l' (CVconstr t vs)) ->
      find_tag cl t e ->
      W ! l = Some w ->
      W ! l' = Some w ->
      cbstep_fuel W ex ρ e c r ->
      cbstep W ex ρ (AS.Ecase x l cl) c r

  with cbstep_fuel (W : web_map) (ex : bool) (ρ : cenv) : AS.exp -> fuel -> cres -> Prop :=
  | CbstepF_OOT :
    forall {e},
      cbstep_fuel W ex ρ e 0 COOT

  | CbstepF_Step :
    forall {e c r},
      cbstep W ex ρ e c r ->
      (if ex then to_exposed_res W r else True) ->
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
    forall i r1 r2,
      AS.bstep_fuel ρ1 e i r1 ->
      cbstep_fuel W ex ρ2 e i r2.

  Fixpoint V (i : nat) (wv1 : AS.wval) (wv2 : clval) {struct i} : Prop :=
    wf_val wv2 /\
    match wv1, wv2 with
    | AS.TAG _ l1 v1, TAG _ l2 v2 =>
        l1 = l2 /\
        match v1, v2 with
        | AS.Vconstr c1 vs1, CVconstr c2 vs2 =>
            c1 = c2 /\
            length vs1 = length vs2 /\
            match i with
            | 0 => True
            | S i0 => Forall2 (V i0) vs1 vs2
            end

        | AS.Vfun f1 ρ1 xs1 e1, CVfun f2 ρ2 W xs2 e2 =>
            length xs1 = length xs2 /\
            match exposedb w2 with
            | true =>
                match i with
                | 0 => True
                | S i0 =>
                    forall j vs1 vs2 ρ3 ρ4,
                      j <= i0 ->
                      Forall exposed vs2 ->
                      Forall2 (V W (i0 - (i0 - j))) vs1 vs2 ->
                      set_lists xs1 vs1 (M.set f1 (AS.Tag l1 (AS.Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                      set_lists xs2 vs2 (M.set f2 (AT.Tag w2 (AT.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                      (exists W', well_annotated W' true ρ3 e1) ->
                      E' (V W) true (i0 - (i0 - j)) ρ3 e1 ρ4 e2
                end

            | false =>
                W ! l1 = Some w2 /\
                match i with
                | 0 => True
                | S i0 =>
                    forall j vs1 vs2 ρ3 ρ4,
                      j <= i0 ->
                      Forall2 (V W (i0 - (i0 - j))) vs1 vs2 ->
                      set_lists xs1 vs1 (M.set f1 (AS.Tag l1 (AS.Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                      set_lists xs2 vs2 (M.set f2 (AT.Tag w2 (AT.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                      well_annotated W false ρ3 e1 ->
                      E' (V W) false (i0 - (i0 - j)) ρ3 e1 ρ4 e2
                end
            end

        | _, _ => False
        end
    end.

  Definition R W := (R' (V W)).

  Definition E W := (E' (V W)).

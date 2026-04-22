From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Util W0 ANF1 ANF Erase.

Module AS := ANF1.
Module AT := ANF.

Definition web_map := M.t web.

Section Collecting.

  (* The analysis result mapping labels to the actual webs. *)
  Variable W : web_map.

  (* Collecting Big-step Semantics *)
  Inductive cbstep (ρ : AS.env) : AS.exp -> fuel -> AS.res -> Prop :=
  | Cbstep_ret :
    forall {x wv},
      M.get x ρ = Some wv ->
      cbstep ρ (AS.Eret x) 0 (AS.Res wv)

  | Cbstep_fun :
    forall {f l xs e k c r},
      cbstep_fuel (M.set f (AS.Tag l (AS.Vfun f ρ xs e)) ρ) k c r ->
      cbstep ρ (AS.Efun f l xs e k) c r

  | Cbstep_app :
    forall {f f' l l' w xs ρ' xs' e vs ρ'' c r},
      M.get f ρ = Some (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      W ! l = Some w ->
      W ! l' = Some w ->
      cbstep_fuel ρ'' e c r ->
      cbstep ρ (AS.Eapp f l xs) c r

  | Cbstep_letapp_Res :
    forall {x f f' l l' w xs k ρ' xs' e vs ρ'' c c' v r},
      M.get f ρ = Some (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      cbstep_fuel ρ'' e c (AS.Res v) ->
      cbstep_fuel (M.set x v ρ) k c' r ->
      W ! l = Some w ->
      W ! l' = Some w ->
      cbstep ρ (AS.Eletapp x f l xs k) (c + c') r

  | Cbstep_letapp_OOT :
    forall {x f f' l l' w xs k ρ' xs' e vs ρ'' c},
      M.get f ρ = Some (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      cbstep_fuel ρ'' e c AS.OOT ->
      W ! l = Some w ->
      W ! l' = Some w ->
      cbstep ρ (AS.Eletapp x f l xs k) c AS.OOT

  | Cbstep_constr :
    forall {x l t xs e r vs c},
      get_list xs ρ = Some vs ->
      cbstep_fuel (M.set x (AS.Tag l (AS.Vconstr t vs)) ρ) e c r ->
      cbstep ρ (AS.Econstr x l t xs e) c r

  | Cbstep_proj :
    forall {x l l' w t i y e c r v vs},
      M.get y ρ = Some (AS.Tag l' (AS.Vconstr t vs)) ->
      nth_error vs i = Some v ->
      W ! l = Some w ->
      W ! l' = Some w ->
      cbstep_fuel (M.set x v ρ) e c r ->
      cbstep ρ (AS.Eproj x l i y e) c r

  | Cbstep_case :
    forall {x l l' w cl t e r c vs},
      M.get x ρ = Some (AS.Tag l' (AS.Vconstr t vs)) ->
      find_tag cl t e ->
      W ! l = Some w ->
      W ! l' = Some w ->
      cbstep_fuel ρ e c r ->
      cbstep ρ (AS.Ecase x l cl) c r

  with cbstep_fuel (ρ : AS.env) : AS.exp -> fuel -> AS.res -> Prop :=
  | CbstepF_OOT :
    forall {e},
      cbstep_fuel ρ e 0 AS.OOT

  | CbstepF_Step :
    forall {e c r},
      cbstep ρ e c r ->
      cbstep_fuel ρ e (S c) r.

  Hint Constructors cbstep : core.
  Hint Constructors cbstep_fuel : core.

  Scheme cbstep_ind' := Minimality for cbstep Sort Prop
  with cbstep_fuel_ind' := Minimality for cbstep_fuel Sort Prop.

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
                  E' V (exposedb w2) (i0 - (i0 - j)) ρ3 e1 ρ4 e2
            end

        | _, _ => False
        end
    end.

  Definition R := (R' V).

  Definition E := (E' V).

End Collecting.

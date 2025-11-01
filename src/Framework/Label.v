From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF0 ANF1 Refl0.

Module A0 := ANF0.
Module A1 := ANF1.

(* Attach Unique Labels *)

(* Specification *)
(*
Inductive trans (Γ : A0.vars) : label -> A0.exp -> label -> A1.exp -> Prop :=
| Trans_ret :
  forall {x l0},
    (x \in Γ) ->
    trans Γ l0 (A0.Eret x) l0 (A1.Eret x)

| Trans_fun :
  forall {f xs e0 k0 e1 k1 l0 l2 l3},
    let l1 := next_label l0 in
    trans (FromList xs :|: (f |: Γ)) l1 e0 l2 e1 ->
    trans (f |: Γ) l2 k0 l3 k1 ->
    trans Γ l0 (A0.Efun f xs e0 k0) l3 (A1.Efun f l0 xs e1 k1)

| Trans_app :
  forall {f xs l0},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    let l1 := next_label l0 in
    trans Γ l0 (A0.Eapp f xs) l1 (A1.Eapp f l0 xs)

| Trans_letapp :
  forall {x f xs k0 k1 l0 l2},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    let l1 := next_label l0 in
    trans (x |: Γ) l1 k0 l2 k1 ->
    trans Γ l0 (A0.Eletapp x f xs k0) l2 (A1.Eletapp x f l0 xs k1)

| Trans_constr :
  forall {x t xs k0 k1 l0 l2},
    (FromList xs \subset Γ) ->
    let l1 := next_label l0 in
    trans (x |: Γ) l1 k0 l2 k1 ->
    trans Γ l0 (A0.Econstr x t xs k0) l2 (A1.Econstr x l0 t xs k1)

| Trans_proj :
  forall {x y k0 k1 n l0 l2},
    (y \in Γ) ->
    let l1 := next_label l0 in
    trans (x |: Γ) l1 k0 l2 k1 ->
    trans Γ l0 (A0.Eproj x n y k0) l2 (A1.Eproj x l0 n y k1)

| Trans_case_nil :
  forall {x l0},
    (x \in Γ) ->
    let l1 := next_label l0 in
    trans Γ l0 (A0.Ecase x []) l1 (A1.Ecase x l0 [])

| Trans_case_cons :
  forall {x e0 e1 t cl0 cl1 l0 l2 l4},
    (x \in Γ) ->
    let l1 := next_label l0 in
    trans Γ l1 e0 l2 e1 ->
    let l3 := next_label l2 in
    trans Γ l3 (A0.Ecase x cl0) l4 (A1.Ecase x l2 cl1) ->
    trans Γ l0 (A0.Ecase x ((t, e0) :: cl0)) l4 (A1.Ecase x l0 ((t, e1) :: cl1)).

Hint Constructors trans : core.

Lemma trans_unique_label Γ l1 e1 l2 e2 :
  trans Γ l1 e1 l2 e2 ->
  unique_label e2.
Proof.
  intro H.
  induction H; simpl; intros; eauto.
  - econstructor; eauto.
Abort.
 *)

(* Note this is directly based on `unique_label` *)
Inductive trans (Γ : A0.vars) : A0.exp -> A1.exp -> Prop :=
| Trans_ret :
  forall {x},
    (x \in Γ) ->
    trans Γ (A0.Eret x) (A1.Eret x)

| Trans_fun :
  forall {f xs e0 k0 e1 k1 l},
    (~ l \in has_label e1) ->
    (~ l \in has_label k1) ->
    Disjoint _ (has_label e1) (has_label k1) ->
    trans (FromList xs :|: (f |: Γ)) e0 e1 ->
    trans (f |: Γ) k0 k1 ->
    trans Γ (A0.Efun f xs e0 k0) (A1.Efun f l xs e1 k1)

| Trans_app :
  forall {f xs l},
    trans Γ (A0.Eapp f xs) (A1.Eapp f l xs)

| Trans_letapp :
  forall {x f xs k0 k1 l},
    (~ l \in has_label k1) ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k0 k1 ->
    trans Γ (A0.Eletapp x f xs k0) (A1.Eletapp x f l xs k1)

| Trans_constr :
  forall {x t xs k0 k1 l},
    (~ l \in has_label k1) ->
    (FromList xs \subset Γ) ->
    trans (x |: Γ) k0 k1 ->
    trans Γ (A0.Econstr x t xs k0) (A1.Econstr x l t xs k1)

| Trans_proj :
  forall {x y k0 k1 n l},
    (~ l \in has_label k1) ->
    (y \in Γ) ->
    trans (x |: Γ) k0 k1 ->
    trans Γ (A0.Eproj x n y k0) (A1.Eproj x l n y k1)

| Trans_case_nil :
  forall {x l},
    trans Γ (A0.Ecase x []) (A1.Ecase x l [])

| Trans_case_cons :
  forall {x e0 e1 c cl0 cl1 l},
    (~ l \in has_label e1) ->
    Disjoint _ (has_label e1) (has_label (A1.Ecase x l cl1)) ->
    (x \in Γ) ->
    trans Γ e0 e1 ->
    trans Γ (A0.Ecase x cl0) (A1.Ecase x l cl1) ->
    trans Γ (A0.Ecase x ((c, e0) :: cl0)) (A1.Ecase x l ((c, e1) :: cl1)).

Hint Constructors trans : core.

Lemma trans_unique_label Γ e0 e1 :
  trans Γ e0 e1 ->
  unique_label e1.
Proof.
  intro H.
  induction H; intros; eauto.
Qed.

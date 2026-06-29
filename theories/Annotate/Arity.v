From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From LambdaANF Require Import ANF.
From LambdaWeb Require Import ANF Erase.
From Annotate Require Import Annotate.

(* Trivial Web Annotation Based on Function Arities *)

(* We annotate function values with some Exposed web id based on their arities. *)
(* We annotate constructor values with a single Exposed web id. *)

(* Note this is basically annotating with `fun_tag`s in CertiCoq. *)

Module A0 := LambdaANF.ANF.
Module A1 := LambdaWeb.ANF.

Definition arity_to_web (n : nat) : web := Pos.of_nat n.

(* Annotate constructor values with `wc`.
   This works since closure and constructor values live in different web universes. *)
Definition wc := arity_to_web 0.

Section Trans.

  (* Specification *)
  Inductive trans (Γ : vars) : A0.exp -> A1.exp -> Prop :=
  | Trans_ret :
    forall {x},
      (x \in Γ) ->
      trans Γ (A0.Eret x) (A1.Eret x)

  | Trans_fun :
    forall {f xs e k e' k'},
      let w := arity_to_web (length xs) in
      trans (FromList xs :|: (f |: Γ)) e e' ->
      trans (f |: Γ) k k' ->
      trans Γ (A0.Efun f xs e k) (A1.Efun f w xs e' k')

  | Trans_app :
    forall {f xs},
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      let w := arity_to_web (length xs) in
      trans Γ (A0.Eapp f xs) (A1.Eapp f w xs)

  | Trans_letapp :
    forall {x f xs k k'},
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      let w := arity_to_web (length xs) in
      trans (x |: Γ) k k' ->
      trans Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w xs k')

  | Trans_constr :
    forall {x t xs k k'},
      (FromList xs \subset Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (A0.Econstr x t xs k) (A1.Econstr x wc t xs k')

  | Trans_proj :
    forall {x y k k' n},
      (y \in Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (A0.Eproj x n y k) (A1.Eproj x wc n y k')

  | Trans_case_nil :
    forall {x},
      (x \in Γ) ->
      trans Γ (A0.Ecase x []) (A1.Ecase x wc [])

  | Trans_case_cons :
    forall {x e e' t cl cl'},
      (x \in Γ) ->
      trans Γ e e' ->
      trans Γ (A0.Ecase x cl) (A1.Ecase x wc cl') ->
      trans Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x wc ((t, e') :: cl')).

  Hint Constructors trans : core.

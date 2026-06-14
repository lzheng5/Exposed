From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Base Util.

(* Multi-language untyped λANF with labels *)

(* Syntax *)
Inductive exp : Type :=
| BExp : bexp -> exp
| RExp : rexp -> exp

(* Blue Terms *)
with bexp : Type :=
| BEret : var -> bexp
| BEapp : var -> label -> list var -> bexp
| BEletapp : var -> var -> label -> list var -> exp -> bexp
| BEfun : var -> label -> list var -> bexp -> exp -> bexp
| BEconstr : var -> label -> ctor_tag -> list var -> exp -> bexp
| BEcase : var -> label -> list (ctor_tag * exp) -> bexp
| BEproj : var -> label -> nat -> var -> exp -> bexp

(* Red Terms *)
with rexp : Type :=
| REret : var -> rexp
| REapp : var -> label -> list var -> rexp
| REletapp : var -> var -> label -> list var -> exp -> rexp
| REfun : var -> label -> list var -> rexp -> exp -> rexp
| REconstr : var -> label -> ctor_tag -> list var -> exp -> rexp
| REcase : var -> label -> list (ctor_tag * exp) -> rexp
| REproj : var -> label -> nat -> var -> exp -> rexp.

Hint Constructors exp : core.
Hint Constructors bexp : core.
Hint Constructors rexp : core.

(* Tagged Value *)
Inductive tag A : Type :=
| TAG : label -> A -> tag A.

Hint Constructors tag : core.

(* Value *)
Inductive val : Type :=
| BVfun : var -> M.t (tag val) -> list var -> bexp -> val
| BVconstr : ctor_tag -> list (tag val) -> val
| RVfun : var -> M.t (tag val) -> list var -> rexp -> val
| RVconstr : ctor_tag -> list (tag val) -> val.

Hint Constructors val : core.

Definition wval := tag val.
Definition Tag w v := TAG val w v.

(* Environment *)
Definition env := M.t wval.

(* Result *)
Inductive res : Type :=
| OOT
| Res : wval -> res.

Hint Constructors res : core.

(* Big-step Semantics *)
Definition fuel := nat.

Inductive bstep (ρ : env) : exp -> fuel -> res -> Prop :=
| BStep_RExp :
  forall {re c r},
    rbstep ρ re c r ->
    bstep ρ (RExp re) c r

| BStep_BExp :
  forall {be c r},
    bbstep ρ be c r ->
    bstep ρ (BExp be) c r

with bbstep (ρ : env) : bexp -> fuel -> res -> Prop :=
| BBStep_ret :
  forall {x wv},
    M.get x ρ = Some wv ->
    bbstep ρ (BEret x) 0 (Res wv)

| BBStep_fun :
  forall {f w xs be k c r},
    bstep_fuel (M.set f (Tag w (BVfun f ρ xs be)) ρ) k c r ->
    bbstep ρ (BEfun f w xs be k) c r

| BBStep_app :
  forall {f f' w w' xs ρ' xs' be vs ρ'' c r},
    M.get f ρ = Some (Tag w' (BVfun f' ρ' xs' be)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w' (BVfun f' ρ' xs' be)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' (BExp be) c r ->
    bbstep ρ (BEapp f w xs) c r

| BBStep_letapp_Res :
  forall {x f f' w w' xs k ρ' xs' be vs ρ'' c c' v r},
    M.get f ρ = Some (Tag w' (BVfun f' ρ' xs' be)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w' (BVfun f' ρ' xs' be)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' (BExp be) c (Res v) ->
    bstep_fuel (M.set x v ρ) k c' r ->
    bbstep ρ (BEletapp x f w xs k) (c + c') r

| BBStep_letapp_OOT :
  forall {x f f' w w' xs k ρ' xs' be vs ρ'' c},
    M.get f ρ = Some (Tag w' (BVfun f' ρ' xs' be)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w' (BVfun f' ρ' xs' be)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' (BExp be) c OOT ->
    bbstep ρ (BEletapp x f w xs k) c OOT

| BBStep_constr :
  forall {x w t xs e r vs c},
    get_list xs ρ = Some vs ->
    bstep_fuel (M.set x (Tag w (BVconstr t vs)) ρ) e c r ->
    bbstep ρ (BEconstr x w t xs e) c r

| BBStep_proj :
  forall {x w w' t i y e c r v vs},
    M.get y ρ = Some (Tag w' (BVconstr t vs)) ->
    nth_error vs i = Some v ->
    bstep_fuel (M.set x v ρ) e c r ->
    bbstep ρ (BEproj x w i y e) c r

| BBStep_case :
  forall {x w w' cl t e r c vs},
    M.get x ρ = Some (Tag w' (BVconstr t vs)) ->
    find_tag cl t e ->
    bstep_fuel ρ e c r ->
    bbstep ρ (BEcase x w cl) c r

with rbstep (ρ : env) : rexp -> fuel -> res -> Prop :=
| RBstep_ret :
  forall {x wv},
    M.get x ρ = Some wv ->
    rbstep ρ (REret x) 0 (Res wv)

| RBstep_fun :
  forall {f w xs re k c r},
    bstep_fuel (M.set f (Tag w (RVfun f ρ xs re)) ρ) k c r ->
    rbstep ρ (REfun f w xs re k) c r

| RBstep_app :
  forall {f f' w w' xs ρ' xs' re vs ρ'' c r},
    M.get f ρ = Some (Tag w' (RVfun f' ρ' xs' re)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w' (RVfun f' ρ' xs' re)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' (RExp re) c r ->
    rbstep ρ (REapp f w xs) c r

| RBstep_letapp_Res :
  forall {x f f' w w' xs k ρ' xs' re vs ρ'' c c' v r},
    M.get f ρ = Some (Tag w' (RVfun f' ρ' xs' re)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w' (RVfun f' ρ' xs' re)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' (RExp re) c (Res v) ->
    bstep_fuel (M.set x v ρ) k c' r ->
    rbstep ρ (REletapp x f w xs k) (c + c') r

| RBstep_letapp_OOT :
  forall {x f f' w w' xs k ρ' xs' re vs ρ'' c},
    M.get f ρ = Some (Tag w' (RVfun f' ρ' xs' re)) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Tag w' (RVfun f' ρ' xs' re)) ρ') = Some ρ'' ->
    bstep_fuel ρ'' (RExp re) c OOT ->
    rbstep ρ (REletapp x f w xs k) c OOT

| RBstep_constr :
  forall {x w t xs e r vs c},
    get_list xs ρ = Some vs ->
    bstep_fuel (M.set x (Tag w (RVconstr t vs)) ρ) e c r ->
    rbstep ρ (REconstr x w t xs e) c r

| RBstep_proj :
  forall {x w w' t i y e c r v vs},
    M.get y ρ = Some (Tag w' (RVconstr t vs)) ->
    nth_error vs i = Some v ->
    bstep_fuel (M.set x v ρ) e c r ->
    rbstep ρ (REproj x w i y e) c r

| RBstep_case :
  forall {x w w' cl t e r c vs},
    M.get x ρ = Some (Tag w' (RVconstr t vs)) ->
    find_tag cl t e ->
    bstep_fuel ρ e c r ->
    rbstep ρ (REcase x w cl) c r

with bstep_fuel (ρ : env) : exp -> fuel -> res -> Prop :=
| BStepF_OOT :
  forall {e},
    bstep_fuel ρ e 0 OOT

| BStepF_Step :
  forall {e c r},
    bstep ρ e c r ->
    bstep_fuel ρ e (S c) r.

Hint Constructors bstep : core.
Hint Constructors bbstep : core.
Hint Constructors rbstep : core.
Hint Constructors bstep_fuel : core.

Scheme bstep_ind' := Minimality for bstep Sort Prop
with bbstep_ind' := Minimality for bbstep Sort Prop
with rbstep_ind' := Minimality for rbstep Sort Prop
with bstep_fuel_ind' := Minimality for bstep_fuel Sort Prop.

Lemma bstep_deterministic' v v' {ρ e c c' r r'}:
  bstep ρ e c r ->
  bstep ρ e c' r' ->
  r = Res v ->
  r' = Res v' ->
  (v = v' /\ c = c').
Proof.
  intros H.
  generalize dependent v'.
  generalize dependent r'.
  generalize dependent c'.
  generalize dependent v.

  induction H using bstep_ind' with (P := fun ρ e c r =>
                                            forall v c' r' v',
                                              bstep ρ e c' r' ->
                                              r = Res v -> r' = Res v' ->
                                              v = v' /\ c = c')
                                    (P0 := fun ρ e c r =>
                                             forall v c' r' v',
                                               bbstep ρ e c' r' ->
                                               r = Res v -> r' = Res v' ->
                                               v = v' /\ c = c')
                                    (P1 := fun ρ e c r =>
                                             forall v c' r' v',
                                               rbstep ρ e c' r' ->
                                               r = Res v -> r' = Res v' ->
                                               v = v' /\ c = c')
                                    (P2 := fun ρ e c r =>
                                             forall v c' r' v',
                                               bstep_fuel ρ e c' r' ->
                                               r = Res v -> r' = Res v' ->
                                               v = v' /\ c = c'); intros; subst.
  - sauto lq: on drew: off.
  - sauto lq: on.
  - sauto.
  - sauto lq: on drew: off.
  - inv H3; invc; eauto.
  - inv H4; invc; eauto.
    edestruct IHbstep; eauto; subst.
    edestruct IHbstep0; eauto.
  - sauto.
  - inv H1; invc; eauto.
  - inv H2; invc; eauto.
  - inv H2; invc.
    destruct (find_tag_deterministic H0 H9); subst; eauto.
  - sauto.
  - inv H0; sauto.
  - inv H3; invc; sauto.
  - inv H4; invc.
    edestruct IHbstep; eauto; subst.
    edestruct IHbstep0; eauto.
  - sauto.
  - inv H1; invc; eauto.
  - inv H2; invc; eauto.
  - inv H2; invc; eauto.
    destruct (find_tag_deterministic H0 H9); subst; eauto.
  - sauto.
  - sauto lq: on.
Qed.

Theorem bstep_deterministic v v' {ρ e c c'}:
  bstep ρ e c (Res v) ->
  bstep ρ e c' (Res v') ->
  (v = v' /\ c = c').
Proof. sauto use: bstep_deterministic'. Qed.

Theorem bstep_fuel_deterministic v v' {ρ e c c'}:
  bstep_fuel ρ e c (Res v) ->
  bstep_fuel ρ e c' (Res v') ->
  (v = v' /\ c = c').
Proof. hauto use: bstep_deterministic inv: bstep_fuel. Qed.

Theorem bbstep_deterministic v v' {ρ e c c'}:
  bbstep ρ e c (Res v) ->
  bbstep ρ e c' (Res v') ->
  (v = v' /\ c = c').
Proof. hauto lq: on use: BStep_BExp, bstep_deterministic. Qed.

Theorem rbstep_deterministic v v' {ρ e c c'}:
  rbstep ρ e c (Res v) ->
  rbstep ρ e c' (Res v') ->
  (v = v' /\ c = c').
Proof. hauto lq: on use: BStep_RExp, bstep_deterministic. Qed.

(* Free Variables *)
Inductive occurs_free : exp -> vars :=
| Free_bexp :
  forall x be,
    occurs_free_bexp be x ->
    occurs_free (BExp be) x

| Free_rexp :
  forall x re,
    occurs_free_rexp re x ->
    occurs_free (RExp re) x

with occurs_free_bexp : bexp -> vars :=
| BFree_ret :
  forall x,
    occurs_free_bexp (BEret x) x

| BFree_fun1 :
  forall x f w xs e k,
    f <> x ->
    occurs_free k x ->
    occurs_free_bexp (BEfun f w xs e k) x

| BFree_fun2 :
  forall x f w xs e k,
    f <> x ->
    ~ (List.In x xs) ->
    occurs_free_bexp e x ->
    occurs_free_bexp (BEfun f w xs e k) x

| BFree_app1 :
  forall f w xs,
    occurs_free_bexp (BEapp f w xs) f

| BFree_app2 :
  forall x f w xs,
    List.In x xs ->
    occurs_free_bexp (BEapp f w xs) x

| BFree_letapp1 :
  forall y x f w xs k,
    x <> y ->
    occurs_free k y ->
    occurs_free_bexp (BEletapp x f w xs k) y

| BFree_letapp2 :
  forall x f w xs k,
    occurs_free_bexp (BEletapp x f w xs k) f

| BFree_letapp3 :
  forall y x f w xs k,
    List.In y xs ->
    occurs_free_bexp (BEletapp x f w xs k) y

| BFree_constr1 :
  forall y x xs t w k,
    List.In y xs ->
    occurs_free_bexp (BEconstr x w t xs k) y

| BFree_constr2 :
  forall y x w t xs k,
    y <> x ->
    occurs_free k y ->
    occurs_free_bexp (BEconstr x w t xs k) y

| BFree_proj1 :
  forall y x w i e,
    occurs_free_bexp (BEproj x w i y e) y

| BFree_proj2 :
  forall y x z w i e,
    x <> y ->
    occurs_free e y ->
    occurs_free_bexp (BEproj x w i z e) y

| BFree_case1 :
  forall y w cl,
    occurs_free_bexp (BEcase y w cl) y

| BFree_case2 :
  forall y x w c e cl,
    occurs_free e y ->
    occurs_free_bexp (BEcase x w ((c, e) :: cl)) y

| BFree_case3 :
  forall y x c e w cl,
    occurs_free_bexp (BEcase x w cl) y ->
    occurs_free_bexp (BEcase x w ((c, e) :: cl)) y

with occurs_free_rexp : rexp -> vars :=
| RFree_ret :
  forall x,
    occurs_free_rexp (REret x) x

| RFree_fun1 :
  forall x f w xs e k,
    f <> x ->
    occurs_free k x ->
    occurs_free_rexp (REfun f w xs e k) x

| RFree_fun2 :
  forall x f w xs e k,
    f <> x ->
    ~ (List.In x xs) ->
    occurs_free_rexp e x ->
    occurs_free_rexp (REfun f w xs e k) x

| RFree_app1 :
  forall f w xs,
    occurs_free_rexp (REapp f w xs) f

| RFree_app2 :
  forall x f w xs,
    List.In x xs ->
    occurs_free_rexp (REapp f w xs) x

| RFree_letapp1 :
  forall y x f w xs k,
    x <> y ->
    occurs_free k y ->
    occurs_free_rexp (REletapp x f w xs k) y

| RFree_letapp2 :
  forall x f w xs k,
    occurs_free_rexp (REletapp x f w xs k) f

| RFree_letapp3 :
  forall y x f w xs k,
    List.In y xs ->
    occurs_free_rexp (REletapp x f w xs k) y

| RFree_constr1 :
  forall y x xs t w k,
    List.In y xs ->
    occurs_free_rexp (REconstr x w t xs k) y

| RFree_constr2 :
  forall y x w t xs k,
    y <> x ->
    occurs_free k y ->
    occurs_free_rexp (REconstr x w t xs k) y

| RFree_proj1 :
  forall y x w i e,
    occurs_free_rexp (REproj x w i y e) y

| RFree_proj2 :
  forall y x z w i e,
    x <> y ->
    occurs_free e y ->
    occurs_free_rexp (REproj x w i z e) y

| RFree_case1 :
  forall y w cl,
    occurs_free_rexp (REcase y w cl) y

| RFree_case2 :
  forall y x w c e cl,
    occurs_free e y ->
    occurs_free_rexp (REcase x w ((c, e) :: cl)) y

| RFree_case3 :
  forall y x c e w cl,
    occurs_free_rexp (REcase x w cl) y ->
    occurs_free_rexp (REcase x w ((c, e) :: cl)) y.

Hint Constructors occurs_free : core.
Hint Constructors occurs_free_bexp : core.
Hint Constructors occurs_free_rexp : core.

(* Linking *)
Definition link tmp x lr1 re lr2 be : exp :=
  RExp
    (REfun tmp lr1 [] re
       (RExp
          (REletapp x tmp lr2 []
             (BExp be)))).

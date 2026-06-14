From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

(* untyped miniλANF based on λANF in CertiCoq *)

Module ANF.

Module M := Maps.PTree.
Definition var := M.elt.
Definition web := M.elt.

(* Syntax *)
Inductive primitive : Type :=
| Ptrue
| Pfalse.

Hint Constructors primitive : core.

Inductive exp : Type :=
| Eret : var -> exp
| Eapp : var -> web -> list var -> exp
| Eletapp : var -> var -> web -> list var -> exp -> exp
| Efun : var -> web -> list var -> exp -> exp -> exp
| Eprim_val : var -> primitive -> exp -> exp
| Eif : var -> exp -> exp -> exp.

Hint Constructors exp : core.

(* Value *)
Inductive val : Type :=
| Vfun : var -> M.t val -> web -> list var -> exp -> val
| Vprim : primitive -> val.

Hint Constructors val : core.

(* Environment *)
Definition env := M.t val.

(* Result *)
Inductive res : Type :=
| OOT
| Res : val -> res.

Hint Constructors res : core.

Definition fuel := nat.

(* Big-step Reduction *)
Inductive bstep : env -> exp -> fuel -> res -> Prop :=
| BStep_ret :
  forall {x v ρ},
    M.get x ρ = Some v ->
    bstep ρ (Eret x) 0 (Res v)

| BStep_fun :
  forall {ρ f w xs e k c r},
    bstep_fuel (M.set f (Vfun f ρ w xs e) ρ) k c r ->
    bstep ρ (Efun f w xs e k) c r

| BStep_app :
  forall {ρ f f' w xs ρ' xs' e vs ρ'' c r},
    M.get f ρ = Some (Vfun f' ρ' w xs' e) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Vfun f' ρ' w xs' e) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c r ->
    bstep ρ (Eapp f w xs) c r

| BStep_letapp_Res :
  forall {ρ x f f' w xs k ρ' xs' e vs ρ'' c c' v r},
    M.get f ρ = Some (Vfun f' ρ' w xs' e) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Vfun f' ρ' w xs' e) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c (Res v) ->
    bstep_fuel (M.set x v ρ) k c' r ->
    bstep ρ (Eletapp x f w xs k) (c + c') r

| BStep_letapp_OOT :
  forall {ρ x f f' w xs k ρ' xs' e vs ρ'' c},
    M.get f ρ = Some (Vfun f' ρ' w xs' e) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs (M.set f' (Vfun f' ρ' w xs' e) ρ') = Some ρ'' ->
    bstep_fuel ρ'' e c OOT ->
    bstep ρ (Eletapp x f w xs k) c OOT

| BStep_prim_val :
  forall {ρ x p k c r},
    bstep_fuel (M.set x (Vprim p) ρ) k c r ->
    bstep ρ (Eprim_val x p k) c r

| BStep_if_true :
  forall {ρ x t e c r},
    M.get x ρ = Some (Vprim Ptrue) ->
    bstep_fuel ρ t c r ->
    bstep ρ (Eif x t e) c r

| BStep_if_false :
  forall {ρ x t e c r},
    M.get x ρ = Some (Vprim Pfalse) ->
    bstep_fuel ρ e c r ->
    bstep ρ (Eif x t e) c r

with bstep_fuel : env -> exp -> fuel -> res -> Prop :=
| BStepF_OOT :
  forall {ρ e},
    bstep_fuel ρ e 0 OOT

| BStepF_Step :
  forall {ρ e c r},
    bstep ρ e c r ->
    bstep_fuel ρ e (S c) r.

Hint Constructors bstep : core.
Hint Constructors bstep_fuel : core.

Scheme bstep_ind' := Minimality for bstep Sort Prop
with bstep_fuel_ind' := Minimality for bstep_fuel Sort Prop.

Theorem bstep_deterministic {ρ e c v c' v' r r'}:
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
                                               bstep_fuel ρ e c' r' ->
                                               r = Res v -> r' = Res v' ->
                                               v = v' /\ c = c');
    intros; subst.
  - inv H0; inv H1.
    rewrite H in H6.
    inv H6; auto.
  - inv H0.
    edestruct IHbstep as [Hv Hc]; eauto.
  - inv H3.
    rewrite H in H7; inv H7.
    rewrite H0 in H9; inv H9.
    rewrite H1 in H12; inv H12.
    edestruct IHbstep as [Hv Hc]; eauto.
  - inv H4.
    rewrite H in H11; inv H11.
    rewrite H0 in H14; inv H14.
    rewrite H1 in H15; inv H15.
    edestruct IHbstep as [Hv Hc]; eauto.
    subst.
    edestruct IHbstep0 as [Hvk Hck]; eauto.
  - inv H4.
  - inv H0.
    edestruct IHbstep as [Hv Hc]; eauto.
  - inv H1.
    + edestruct IHbstep as [Hv Hc]; eauto.
    + rewrite H in H8.
      inv H8.
  - inv H1.
    + rewrite H in H8.
      inv H8.
    + edestruct IHbstep as [Hv Hc]; eauto.
  - inv H0.
  - inv H0.
    edestruct IHbstep as [Hv Hc]; eauto.
Qed.

(* Free Variables *)
Inductive occurs_free : exp -> Ensemble var :=
| Free_ret :
  forall x,
    occurs_free (Eret x) x

| Free_fun1 :
  forall x f w xs e k,
    f <> x ->
    occurs_free k x ->
    occurs_free (Efun f w xs e k) x

| Free_fun2 :
  forall x f w xs e k,
    f <> x ->
    ~ (List.In x xs) ->
    occurs_free e x ->
    occurs_free (Efun f w xs e k) x

| Free_app1 :
  forall f w xs,
    occurs_free (Eapp f w xs) f

| Free_app2 :
  forall x f w xs,
    List.In x xs ->
    occurs_free (Eapp f w xs) x

| Free_letapp1 :
  forall y x f w xs k,
    x <> y ->
    occurs_free k y ->
    occurs_free (Eletapp x f w xs k) y

| Free_letapp2 :
  forall x f w xs k,
    occurs_free (Eletapp x f w xs k) f

| Free_letapp3 :
  forall y x f w xs k,
    List.In y xs ->
    occurs_free (Eletapp x f w xs k) y

| Free_prim_val :
  forall y x p k,
    y <> x ->
    occurs_free k y ->
    occurs_free (Eprim_val x p k) y

| Free_if1 :
  forall x t e,
    occurs_free (Eif x t e) x

| Free_if2 :
  forall y x t e,
    occurs_free t y ->
    occurs_free (Eif x t e) y

| Free_if3 :
  forall y x t e,
    occurs_free e y ->
    occurs_free (Eif x t e) y.

Hint Constructors occurs_free : core.

(* Lemmas related to [occurs_free] *)
Lemma free_prim_val_k_subset {k x p} :
  (occurs_free k) \subset (x |: occurs_free (Eprim_val x p k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    constructor; auto.
Qed.

Lemma free_fun_e_subset {k f w e} : forall {xs},
  (occurs_free e) \subset (FromList xs :|: (f |: occurs_free (Efun f w xs e k))).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (in_dec M.elt_eq x xs).
  - apply Union_introl; auto.
  - apply Union_intror; auto.
    unfold Ensembles.In.
    destruct (M.elt_eq f x); subst.
    + apply Union_introl; auto.
    + apply Union_intror.
      unfold Ensembles.In.
      apply Free_fun2; auto.
Qed.

Lemma free_fun_k_subset {k f w xs e} :
  (occurs_free k) \subset (f |: occurs_free (Efun f w xs e k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq f x); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    constructor; auto.
Qed.

Lemma free_letapp_k_subset {f x w xs k} :
  (occurs_free k) \subset (x |: occurs_free (Eletapp x f w xs k)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq x x0); subst.
  - apply Union_introl; auto.
  - apply Union_intror.
    unfold Ensembles.In.
    constructor; auto.
Qed.

Lemma free_if_t_subset {x t e} :
  (occurs_free t) \subset (occurs_free (Eif x t e)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros; eauto.
Qed.

Lemma free_if_e_subset {x t e} :
  (occurs_free e) \subset (occurs_free (Eif x t e)).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros; eauto.
Qed.

(* Web Identifiers *)
Inductive has_web : exp -> Ensemble web :=
| Web_fun1 :
  forall f w xs e k,
    has_web (Efun f w xs e k) w

| Web_fun2 :
  forall w' f w xs e k,
    has_web e w' ->
    has_web (Efun f w xs e k) w'

| Web_fun3 :
  forall w' f w xs e k,
    has_web k w' ->
    has_web (Efun f w xs e k) w'

| Web_app :
  forall f w xs,
    has_web (Eapp f w xs) w

| Web_letapp1 :
  forall x f w xs k,
    has_web (Eletapp x f w xs k) w

| Web_letapp2 :
  forall w' x f w xs k,
    has_web k w' ->
    has_web (Eletapp x f w xs k) w'

| Web_prim_val :
  forall x p k w,
  has_web k w ->
  has_web (Eprim_val x p k) w

| Web_if1 :
  forall x t e w,
    has_web t w ->
    has_web (Eif x t e) w

| Web_if2 :
  forall x t e w,
    has_web e w ->
    has_web (Eif x t e) w.

Hint Constructors has_web : core.

End ANF.

Module Unary.

Import ANF.

(* Logical Relations *)
Definition R' (P : nat -> val -> Prop) (i : nat) (r : res) :=
  match r with
  | OOT => True
  | Res v => P i v
  end.

Definition E' (P : nat -> val -> Prop) (i : nat) (ρ : env) (e : exp) : Prop :=
  forall j r,
    j <= i ->
    bstep_fuel ρ e j r ->
    R' P (i - j) r.

Fixpoint V (i : nat) (v : val) {struct i} : Prop :=
  match i with
  | 0 => True
  | S i' =>
      let fix V' (v : val) : Prop :=
        match v with
        | Vprim p => True
        | Vfun f ρ w xs e =>
            forall j vs ρ',
              j <= i' ->
              Forall (V (i' - (i' - j))) vs -> (* TODO: try V j Vfun *)
              set_lists xs vs (M.set f (Vfun f ρ w xs e) ρ) = Some ρ' ->
              E' V (i' - (i' - j)) ρ' e
        end
      in V' v
  end.

Notation R := (R' V).

Notation E := (E' V).

(* Environment Relation *)
Definition G i ρ := forall x v, M.get x ρ = Some v -> V i v.

Definition has_semantic_meaning e := forall i ρ, G i ρ -> E i ρ e.

(* Environment Lemmas *)
Lemma G_set {i ρ}:
  G i ρ ->
  forall {x v},
    V i v ->
    G i (M.set x v ρ).
Proof.
  unfold G.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - rewrite M.gss in *.
    inv H1; eauto.
  - rewrite M.gso in *; auto.
    eapply H; eauto.
Qed.

Lemma G_set_lists {i ρ}:
  G i ρ ->
  forall {xs vs ρ'},
    Forall (V i) vs ->
    set_lists xs vs ρ = Some ρ' ->
    G i ρ'.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct vs; try discriminate.
    inv H0.
    eapply HG; eauto.
  - destruct vs; try discriminate.
    destruct (set_lists xs vs ρ) eqn:Heq2; try discriminate.
    inv H; inv H0.
    destruct (M.elt_eq x a); subst.
    + rewrite M.gss in *; eauto.
      inv H1; auto.
    + rewrite M.gso in *; auto.
      eapply IHxs; eauto.
Qed.

Lemma G_get_list {i ρ} :
  G i ρ ->
  forall {xs vs},
    get_list xs ρ = Some vs ->
    Forall (V i) vs.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - inv H; auto.
  - destruct (ρ ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ) eqn:Heq2; try discriminate.
    inv H; constructor; eauto.
Qed.

(* Monotonicity Lemmas *)
Lemma V_mono {v} i j:
  V i v ->
  j <= i ->
  V j v.
Proof.
  intros.
  generalize dependent v.
  induction H0; simpl; intros; auto.
  apply IHle.
  destruct m.
  - unfold V. auto.
  - destruct v; auto.
    simpl.
    intros.
    assert (j0 <= S m). lia.
    assert ((m - (m - j0)) = (S m - (S m - j0))). lia.
    rewrite H5 in H2.
    rewrite H5.
    apply (H j0 vs ρ'); auto.
Qed.

Lemma ForallV_mono {vs} i j :
  Forall (V i) vs ->
  j <= i ->
  Forall (V j) vs.
Proof.
  intros H.
  revert j.
  induction H; simpl; intros; auto.
  constructor; eauto.
  eapply V_mono; eauto.
Qed.

Lemma R_mono {r} i j :
  R i r ->
  j <= i ->
  R j r.
Proof.
  unfold R.
  intros.
  destruct r; auto.
  eapply V_mono; eauto.
Qed.

Lemma E_mono {ρ e} i j:
  E i ρ e ->
  j <= i ->
  E j ρ e.
Proof.
  unfold E.
  intros.
  apply R_mono with (i - j0); try lia.
  eapply H; eauto.
  lia.
Qed.

Lemma G_mono {ρ} i j:
  G i ρ ->
  j <= i ->
  G j ρ.
Proof.
  unfold G.
  intros.
  apply V_mono with i; eauto.
Qed.

(* Compatibility Lemmas *)
Lemma ret_compat x :
  has_semantic_meaning (Eret x).
Proof.
  unfold has_semantic_meaning, G, E, R.
  intros.
  inv H1; auto.
  inv H2.
  apply V_mono with i; try lia.
  eapply H; eauto.
Qed.

Lemma prim_val_compat {k} x p :
  has_semantic_meaning k ->
  has_semantic_meaning (Eprim_val x p k).
Proof.
  unfold has_semantic_meaning, E.
  intros.

  assert (HG : G i (M.set x (Vprim p) ρ)).
  {
    apply G_set; auto.
    destruct i; simpl; auto.
  }
  specialize (H i (M.set x (Vprim p) ρ) HG).

  inv H2.
  - eapply H; eauto.
  - inv H3.
    apply R_mono with (i - c); try lia.
    eapply H; eauto; lia.
Qed.

Lemma Vfun_V {e} :
  has_semantic_meaning e ->
  forall {i ρ } f w xs,
    G i ρ ->
    V i (Vfun f ρ w xs e).
Proof.
  unfold has_semantic_meaning.
  intros He i.
  induction i; simpl; intros; auto.
  apply (He (i - (i - j)) ρ').
  eapply G_set_lists; eauto.
  apply G_set; auto.
  - apply G_mono with (S i); auto; lia.
  - apply V_mono with i; try lia.
    apply IHi; auto.
    apply G_mono with (S i); auto; lia.
Qed.

Lemma fun_compat {e k} f w xs :
  has_semantic_meaning e ->
  has_semantic_meaning k ->
  has_semantic_meaning (Efun f w xs e k).
Proof.
  unfold has_semantic_meaning, E.
  intros.
  inv H3.
  - simpl; auto.
  - inv H4.
    apply R_mono with ((i - 1) - c); try lia.
    eapply (H0 (i - 1) (M.set f (Vfun f ρ w xs e) ρ)); eauto; try lia.
    apply G_set.
    + apply G_mono with i; auto; lia.
    + eapply Vfun_V; eauto.
      apply G_mono with i; auto; lia.
Qed.

Lemma app_compat f w xs :
  has_semantic_meaning (Eapp f w xs).
Proof.
  unfold has_semantic_meaning, G, E.
  intros.
  inv H1; simpl; auto.
  inv H2.
  apply H in H5.
  unfold R.
  destruct r; auto.
  destruct i; simpl; auto.
  simpl in H5.

  assert (HE : E i ρ'' e).
  {
    apply E_mono with (i - (i - i)); try lia.
    eapply (H5 i vs); eauto.
    apply ForallV_mono with (S i).
    eapply G_get_list; eauto.
    lia.
  }

  unfold E in HE.
  specialize (HE c (Res v)).
  simpl in HE.
  apply HE; auto; lia.
Qed.

Lemma letapp_compat {k} x f w xs :
  has_semantic_meaning k ->
  has_semantic_meaning (Eletapp x f w xs k).
Proof.
  intros.
  specialize (app_compat f w xs); intros Ha.
  unfold has_semantic_meaning, E in *.
  intros.
  specialize (Ha _ _ H0).
  inv H2; auto.
  inv H3; simpl; auto.
  apply R_mono with ((i - (S c0)) - c'); try lia.
  eapply (H (i - (S c0)) (M.set x v ρ)); eauto; try lia.
  apply G_set.
  apply G_mono with i; try lia; auto.
  specialize (Ha (S c0) (Res v)).
  simpl in Ha.
  apply Ha; try lia; eauto.
Qed.

Lemma if_compat {e t} x :
  has_semantic_meaning t ->
  has_semantic_meaning e ->
  has_semantic_meaning (Eif x t e).
Proof.
  unfold has_semantic_meaning, G, E.
  intros Ht He. intros.
  inv H1; simpl; auto.
  inv H2; apply R_mono with (i - c); try lia.
  - eapply Ht; try lia; eauto.
  - eapply He; try lia; eauto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {e} :
  has_semantic_meaning e.
Proof.
  induction e.
  - apply ret_compat.
  - apply app_compat.
  - apply letapp_compat; auto.
  - apply fun_compat; auto.
  - apply prim_val_compat; auto.
  - apply if_compat; auto.
Qed.

End Unary.

Module Refl.

Import ANF.

(* Logical Relations *)
Definition R' (P : nat -> val -> val -> Prop) (i : nat) (r1 : res) (r2 : res) :=
  match r1, r2 with
  | OOT, OOT => True
  | Res v1, Res v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> val -> val -> Prop) (i : nat) (ρ1 : env) (ρ2 : env) (e1 : exp) (e2 : exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    bstep_fuel ρ1 e1 j1 r1 ->
    exists j2 r2,
      bstep_fuel ρ2 e2 j2 r2 /\
      R' P (i - j1) r1 r2.

Fixpoint V (i : nat) (v1 : val) (v2 : val) {struct i} : Prop :=
  match v1, v2 with
  | Vprim p1, Vprim p2 => p1 = p2
  | Vfun f1 ρ1 w1 xs1 e1, Vfun f2 ρ2 w2 xs2 e2 =>
      match i with
      | 0 => True
      | S i0 =>
          w1 = w2 /\
          length xs1 = length xs2 /\
          forall j vs1 vs2 ρ3 ρ4,
            j <= i0 ->
            Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
            set_lists xs1 vs1 (M.set f1 (Vfun f1 ρ1 w1 xs1 e1) ρ1) = Some ρ3 ->
            set_lists xs2 vs2 (M.set f2 (Vfun f2 ρ2 w2 xs2 e2) ρ2) = Some ρ4 ->
            E' V (i0 - (i0 - j)) ρ3 ρ4 e1 e2
      end
  | _, _ => False
  end.

Notation R := (R' V).

Notation E := (E' V).

(* Environment Relation *)
Definition G i ρ1 ρ2 :=
  forall x v1,
    M.get x ρ1 = Some v1 ->
    exists v2,
      M.get x ρ2 = Some v2 /\
      V i v1 v2.

Definition contextual_equivalent e1 e2 :=
  forall i ρ1 ρ2,
    G i ρ1 ρ2 ->
    E i ρ1 ρ2 e1 e2.

(* Environment Lemmas *)
Lemma G_set {i ρ1 ρ2}:
  G i ρ1 ρ2 ->
  forall {x v1 v2},
    V i v1 v2 ->
    G i (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  unfold G.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - rewrite M.gss in *.
    inv H1; eauto.
  - rewrite M.gso in *; auto.
Qed.

Lemma G_set_lists {i ρ1 ρ2}:
  G i ρ1 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 (V i) vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    G i ρ3 ρ4.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    inv H0; inv H1.
    eapply HG; eauto.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
    inv H; inv H0; inv H1.
    destruct (M.elt_eq x a); subst.
    + rewrite M.gss in *; eauto.
      inv H2; eauto.
    + rewrite M.gso in *; auto.
      eapply IHxs; eauto.
Qed.

Lemma G_get_list {i ρ1 ρ2} :
  G i ρ1 ρ2 ->
  forall {xs vs1},
    get_list xs ρ1 = Some vs1 ->
    exists vs2,
      get_list xs ρ2 = Some vs2 /\
      Forall2 (V i) vs1 vs2.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - inv H; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H.
    edestruct HG as [v2 [Heqv2 Vv]]; eauto.
    rewrite Heqv2.
    edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
    rewrite Heqvs2.
    exists (v2 :: vs2); split; auto.
Qed.

(* Monotonicity Lemmas *)
Lemma V_mono {v1 v2} i j:
  V i v1 v2 ->
  j <= i ->
  V j v1 v2.
Proof.
  intros.
  generalize dependent v1.
  generalize dependent v2.
  induction H0; simpl; intros; auto.
  apply IHle.
  destruct v1.
  - destruct v2; try contradiction.
    destruct m; simpl; auto; try contradiction.
    destruct H as [Hw [Hlen Hv]].
    repeat split; auto; intros.
    assert (Hj0 : m - (m - j0) = (S m - (S m - j0))). lia.
    rewrite Hj0 in *.
    eapply Hv; eauto.
  - destruct v2; try contradiction.
    subst.
    destruct m; simpl; eauto.
Qed.

Lemma ForallV_mono {vs1 vs2} i j :
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

Lemma E_mono {ρ1 ρ2 e1 e2} i j:
  E i ρ1 ρ2 e1 e2 ->
  j <= i ->
  E j ρ1 ρ2 e1 e2.
Proof.
  unfold E.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; auto.
  apply R_mono with (i - j1); try lia; auto.
Qed.

Lemma G_mono {ρ1 ρ2} i j:
  G i ρ1 ρ2 ->
  j <= i ->
  G j ρ1 ρ2.
Proof.
  unfold G.
  intros.
  edestruct H as [v2 [Heqv2 Vv]]; eauto.
  exists v2; split; auto.
  apply V_mono with i; eauto.
Qed.

(* Compatibility Lemmas *)
Lemma ret_compat x :
  contextual_equivalent (Eret x) (Eret x).
Proof.
  unfold contextual_equivalent, G, E, R.
  intros.
  inv H1.
  - exists 0, OOT; auto.
  - inv H2.
    edestruct H as [v2 [Heqv2 Vv]]; eauto.
    exists 1, (Res v2); split; auto.
    apply V_mono with i; try lia; auto.
Qed.

Lemma prim_val_compat {k} x p :
  contextual_equivalent k k ->
  contextual_equivalent (Eprim_val x p k) (Eprim_val x p k).
Proof.
  unfold contextual_equivalent, E.
  intros.

  assert (HG : G i (M.set x (Vprim p) ρ1) (M.set x (Vprim p) ρ2)).
  {
    apply G_set; auto.
    destruct i; simpl; auto.
  }
  specialize (H i (M.set x (Vprim p) ρ1) (M.set x (Vprim p) ρ2) HG).

  inv H2.
  - exists 0, OOT; split; simpl; auto.
  - inv H3.
    edestruct (H c r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    exists (S j2), r2; split; eauto.
    apply R_mono with (i - c); try lia; auto.
Qed.

Lemma Vfun_V {e} :
  contextual_equivalent e e ->
  forall {i ρ1 ρ2} f w xs,
    G i ρ1 ρ2 ->
    V i (Vfun f ρ1 w xs e) (Vfun f ρ2 w xs e).
Proof.
  unfold contextual_equivalent.
  intros He i.
  induction i; simpl; intros; auto.
  repeat split; auto; intros.
  apply (He (i - (i - j)) ρ3 ρ4).
  eapply G_set_lists; eauto.
  apply G_set; auto.
  - apply G_mono with (S i); auto; lia.
  - apply V_mono with i; try lia.
    apply IHi; auto.
    apply G_mono with (S i); auto; lia.
Qed.

Lemma fun_compat {e k} f w xs :
  contextual_equivalent e e ->
  contextual_equivalent k k ->
  contextual_equivalent (Efun f w xs e k) (Efun f w xs e k).
Proof.
  unfold contextual_equivalent, E.
  intros.
  inv H3.
  - exists 0, OOT; split; simpl; auto.
  - inv H4.
    edestruct (H0 (i - 1) (M.set f (Vfun f ρ1 w xs e) ρ1) (M.set f (Vfun f ρ2 w xs e) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + apply G_set.
      * apply G_mono with i; auto; lia.
      * eapply Vfun_V; eauto.
        apply G_mono with i; auto; lia.
    + exists (S j2), r2; split; auto.
      apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma app_compat f w xs :
  contextual_equivalent (Eapp f w xs) (Eapp f w xs).
Proof.
  unfold contextual_equivalent, G, E.
  intros.
  inv H1.
  - exists 0, OOT; split; simpl; auto.
  - inv H2.
    edestruct H as [v2 [Heqv2 Vv]]; eauto.
    destruct v2.
    + destruct i.
      inv H0.
      simpl in Vv.
      destruct Vv as [Hw [Hlen HVv]]; subst.
      destruct (G_get_list H H7) as [vs2 [Heqvs2 Vvs]]; eauto.
      destruct (set_lists_length3 (M.set v (Vfun v t w0 l e0) t) l vs2) as [ρ4 Heqρ4].
      rewrite <- (Forall2_length _ _ _ Vvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H10).
      symmetry; auto.

      assert (HE : E (i - (i - i)) ρ'' ρ4 e e0).
      {
        eapply (HVv i vs vs2); eauto.
        apply ForallV_mono with (S i); auto; lia.
      }
      apply (E_mono _ i) in HE; try lia.
      unfold E in HE.
      destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
      exists (S j2), r2; split; eauto.
    + destruct i; try contradiction.
Qed.

Lemma letapp_compat {k} x f w xs :
  contextual_equivalent k k ->
  contextual_equivalent (Eletapp x f w xs k) (Eletapp x f w xs k).
Proof.
  intros.
  specialize (app_compat f w xs); intros Ha.
  unfold contextual_equivalent, E in *.
  intros.
  specialize (Ha _ _ _ H0).
  inv H2.
  - exists 0, OOT; split; simpl; auto.
  - inv H3.
    + destruct (Ha (S c0) (Res v)) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      simpl in Rra.
      destruct ra; try contradiction.
      edestruct (H (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
      * apply G_set; auto.
        apply G_mono with i; try lia; auto.
      * exists (j1 + j2), r2; split.
        -- inv Hap.
           inv H2.
           assert ((S c + j2) = S (c + j2)). lia.
           rewrite H2.
           constructor.
           eauto.
        -- apply R_mono with (i - S c0 - c'); try lia; auto.
    + destruct (Ha (S c) OOT) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      exists j1, ra.
      destruct ra; try contradiction.
      split; auto.
      inv Hap; eauto.
      inv H2; eauto.
Qed.

Lemma if_compat {e t} x :
  contextual_equivalent t t ->
  contextual_equivalent e e ->
  contextual_equivalent (Eif x t e) (Eif x t e).
Proof.
  unfold contextual_equivalent, G, E.
  intros Ht He. intros.
  inv H1.
  - exists 0, OOT; simpl; eauto.
  - inv H2.
    + edestruct Ht with (j1 := c) as [j2 [r2 [Ht' Rr]]]; eauto; try lia.
      exists (S j2), r2; split; eauto.
      constructor; auto.
      apply BStep_if_true; auto.
      edestruct H as [v2 [Heqv2 Vv]]; eauto.
      destruct v2.
      destruct i; contradiction.
      destruct i; simpl in Vv; subst; auto.
      apply R_mono with (i - c); try lia; auto.
    + edestruct He with (j1 := c) as [j2 [r2 [He' Rr]]]; eauto; try lia.
      exists (S j2), r2; split; eauto.
      constructor; auto.
      apply BStep_if_false; auto.
      edestruct H as [v2 [Heqv2 Vv]]; eauto.
      destruct v2.
      destruct i; contradiction.
      destruct i; simpl in Vv; subst; auto.
      apply R_mono with (i - c); try lia; auto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {e} :
  contextual_equivalent e e.
Proof.
  induction e.
  - apply ret_compat.
  - apply app_compat.
  - apply letapp_compat; auto.
  - apply fun_compat; auto.
  - apply prim_val_compat; auto.
  - apply if_compat; auto.
Qed.

End Refl.

Module DPE.

Import ANF.

(* Map from web identifier to the live parameter list *)
Definition live_map : Type := M.t (list bool).

(* Apply bit mask to argument list *)
Fixpoint live_args {A} (ys : list A) (bs : list bool) : list A :=
  match bs, ys with
  | [], [] => ys
  | b :: bs', y :: ys' =>
    if b then y :: (live_args ys' bs')
    else live_args ys' bs'
  | _, _ => ys
  end.

(* DPE Specification *)
Parameter L : live_map.

Inductive elim_exp (Γ : Ensemble var) : exp -> exp -> Prop :=
| Elim_ret :
  forall {x},
    elim_exp Γ (Eret x) (Eret x)

| Elim_fun :
  forall {f w xs e k bs e' k'},
    elim_exp (FromList xs :|: (f |: Γ)) e e' ->
    elim_exp (f |: Γ) k k' ->

    M.get w L = Some bs ->
    length xs = length bs ->

    NoDup (f :: xs) ->
    Disjoint _ (FromList (f :: xs)) Γ ->
    elim_exp Γ (Efun f w xs e k) (Efun f w (live_args xs bs) e' k')

| Elim_app :
  forall {f w xs bs},
    M.get w L = Some bs ->
    length xs = length bs ->
    elim_exp Γ (Eapp f w xs) (Eapp f w (live_args xs bs))

| Elim_letapp :
  forall {x f w xs k bs k'},
    elim_exp (x |: Γ) k k' ->

    M.get w L = Some bs ->
    length xs = length bs ->

    elim_exp Γ (Eletapp x f w xs k) (Eletapp x f w (live_args xs bs) k')

| Elim_prim_val :
  forall {x p k k'},
    elim_exp (x |: Γ) k k' ->
    elim_exp Γ (Eprim_val x p k) (Eprim_val x p k')

| Elim_if :
  forall {x t e t' e'},
    elim_exp Γ t t' ->
    elim_exp Γ e e' ->
    elim_exp Γ (Eif x t e) (Eif x t' e').

Hint Constructors elim_exp : core.

(* Logical Relations *)
Definition R' (P : nat -> val -> val -> Prop) (i : nat) (r1 : res) (r2 : res) :=
  match r1, r2 with
  | OOT, OOT => True
  | Res v1, Res v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> val -> val -> Prop) (i : nat) (ρ1 : env) (e1 : exp) (ρ2 : env) (e2 : exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    bstep_fuel ρ1 e1 j1 r1 ->
    exists j2 r2,
      bstep_fuel ρ2 e2 j2 r2 /\
      R' P (i - j1) r1 r2.

Fixpoint V (i : nat) (v1 : val) (v2 : val) {struct i} : Prop :=
  match v1, v2 with
  | Vprim p1, Vprim p2 => p1 = p2
  | Vfun f1 ρ1 w1 xs1 e1, Vfun f2 ρ2 w2 xs2 e2 =>
      match i with
      | 0 => True
      | S i0 =>
          exists bs,
            w1 = w2 /\ (* web stay the same *)
            M.get w1 L = Some bs /\
            length xs1 = length bs /\
            xs2 = live_args xs1 bs /\
            forall j vs1 vs2 ρ3 ρ4,
              j <= i0 ->
              Forall2 (V (i0 - (i0 - j))) (live_args vs1 bs) vs2 -> (* only live args matter *)
              set_lists xs1 vs1 (M.set f1 (Vfun f1 ρ1 w1 xs1 e1) ρ1) = Some ρ3 ->
              set_lists xs2 vs2 (M.set f2 (Vfun f2 ρ2 w2 xs2 e2) ρ2) = Some ρ4 ->
              E' V (i0 - (i0 - j)) ρ3 e1 ρ4 e2
      end
  | _, _ => False
  end.

Notation R := (R' V).

Notation E := (E' V).

(* Environment Relation *)
Definition G i Γ ρ1 ρ2 :=
  forall x,
    (x \in Γ) ->
    exists v1,
      M.get x ρ1 = Some v1 /\
      forall v2,
        M.get x ρ2 = Some v2 ->
        V i v1 v2.

Definition elim_correct Γ e1 e2 :=
  forall i ρ1 ρ2,
    (occurs_free e2) \subset (Dom_map ρ2) ->
    (Dom_map ρ2) \subset Γ ->
    G i Γ ρ1 ρ2 ->
    E i ρ1 e1 ρ2 e2.

(* Monotonicity Lemmas *)
Lemma V_mono {v1 v2} i j:
  V i v1 v2 ->
  j <= i ->
  V j v1 v2.
Proof.
  intros.
  generalize dependent v1.
  generalize dependent v2.
  induction H0; simpl; intros; auto.
  apply IHle.
  destruct v1.
  - destruct v2; try contradiction.
    destruct H as [bs [Heqw [Heqbs [Hlen [Hl0 Hfv]]]]]; subst.
    destruct m; simpl; auto; try contradiction.
    exists bs; repeat split; auto; intros.
    assert (Hj0 : m - (m - j0) = (S m - (S m - j0))). lia.
    rewrite Hj0 in *.
    eapply Hfv; eauto.
  - destruct v2; try contradiction.
    subst.
    destruct m; simpl; eauto.
Qed.

Lemma ForallV_mono {vs1 vs2} i j :
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

Lemma E_mono {ρ1 ρ2 e1 e2} i j:
  E i ρ1 ρ2 e1 e2 ->
  j <= i ->
  E j ρ1 ρ2 e1 e2.
Proof.
  unfold E.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; auto.
  apply R_mono with (i - j1); try lia; auto.
Qed.

Lemma G_mono {Γ ρ1 ρ2} i j:
  G i Γ ρ1 ρ2 ->
  j <= i ->
  G j Γ ρ1 ρ2.
Proof.
  unfold G.
  intros.
  edestruct H as [v1 [Heqv1 Hv2]]; eauto.
  exists v1; split; auto; intros.
  apply V_mono with i; eauto.
Qed.

(* Lemmas about [live_args] *)
Lemma live_args_incl {A xs bs} :
  incl (@live_args A xs bs) xs.
Proof.
  revert bs.
  induction xs; intros.
  - destruct bs; simpl; apply incl_nil_l.
  - destruct bs; simpl.
    + apply incl_refl.
    + destruct b.
      * apply incl_cons.
        apply in_eq.
        apply incl_tl.
        auto.
      * apply incl_tl.
        auto.
Qed.

Lemma live_args_In : forall {A xs bs a}, In a (@live_args A xs bs) -> In a xs.
Proof.
  intros.
  eapply live_args_incl; eauto.
Qed.

Lemma live_args_not_In : forall {A xs a} bs, ~ In a xs -> ~ In a (@live_args A xs bs).
Proof.
  intros.
  intro Hc.
  apply H.
  eapply live_args_In; eauto.
Qed.

Lemma live_args_length {A B} xs ys bs :
  length xs = length ys ->
  length (@live_args A xs bs) = length (@live_args B ys bs).
Proof.
  revert ys bs. induction xs; intros; eauto.
  - destruct ys; try (simpl in * ; congruence).
    destruct bs; reflexivity.
  - simpl.
    destruct ys; try (simpl in * ; congruence). inv H.
    destruct bs. simpl. congruence.
    destruct b0; simpl; eauto.
Qed.

(* Environment Lemmas *)
Lemma G_set {Γ i ρ1 ρ2}:
  G i Γ ρ1 ρ2 ->
  forall {x v1 v2},
    V i v1 v2 ->
    G i (x |: Γ) (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  unfold G.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss in *.
    eexists; split; eauto; intros.
    inv H1; inv H2; eauto.
  - rewrite M.gso in *; auto.
    inv H1.
    + unfold Ensembles.In in H2.
      inv H2; contradiction.
    + edestruct H as [v1' [Heqv1' Hv2]]; eauto.
      eexists; split; eauto; intros.
      rewrite M.gso in *; auto.
Qed.

Lemma Disjoint_FromList_cons {A} : forall {xs a S},
  Disjoint A (FromList (a :: xs)) S ->
  Disjoint A (FromList xs) S.
Proof.
  intros.
  inv H; constructor; intros x Hc.
  apply (H0 x).
  unfold Ensembles.In, FromList in *.
  inv Hc.
  constructor; auto.
  unfold Ensembles.In.
  apply in_cons; auto.
Qed.

Lemma G_set_lists {i Γ ρ1 ρ2}:
  G i Γ ρ1 ρ2 ->
  (Dom_map ρ2) \subset Γ ->
  forall {xs vs1 vs2 ρ3 ρ4 bs},
    length xs = length bs ->
    Forall2 (V i) (live_args vs1 bs) vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists (live_args xs bs) vs2 ρ2 = Some ρ4 ->
    NoDup xs ->
    Disjoint _ (FromList xs) Γ ->
    G i (FromList xs :|: Γ) ρ3 ρ4.
Proof.
  unfold G.
  intros HG HS xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct bs; try discriminate.
    simpl in *.
    destruct vs2; try discriminate.
    inv H0; inv H1; inv H2; inv H3.
    eapply HG; eauto.
    inv H5; auto.
    inv H0.
  - destruct vs1; try discriminate.
    destruct bs; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    inv H; inv H1; inv H3.
    destruct b; simpl in *.
    + destruct vs2; try discriminate.
      destruct (set_lists (live_args xs bs) vs2 ρ2) eqn:Heq2; try discriminate.
      inv H2; inv H0.
      destruct (M.elt_eq x a); subst.
      * repeat rewrite M.gss in *; eauto.
        eexists; split; eauto; intros.
        inv H; auto.
      * rewrite M.gso in *; auto.
        rewrite M.gso in *; auto.
        eapply IHxs; eauto.
        eapply Disjoint_FromList_cons; eauto.
        unfold Ensembles.In in *.
        inv H5.
        inv H; try contradiction.
        apply Union_introl; auto.
        apply Union_intror; auto.
    + destruct (M.elt_eq x a); subst.
      * rewrite M.gss in *; eauto.
        eexists; split; eauto; intros.
        exfalso.
        inv H4.
        apply (H1 a).
        unfold Ensembles.In, FromList.
        constructor.
        -- unfold Ensembles.In in *.
           apply in_eq.
        -- apply live_args_not_In with bs in H6.
           erewrite <- set_lists_not_In in H; eauto.
           unfold Ensembles.Included, Ensembles.In, Dom_map in HS.
           eauto.
      * rewrite M.gso in *; auto.
        eapply IHxs; eauto.
        eapply Disjoint_FromList_cons; eauto.
        inv H5.
        -- inv H; try contradiction.
           apply Union_introl; auto.
        -- apply Union_intror; auto.
Qed.

Lemma G_get_list {i Γ ρ1 ρ2} :
  G i Γ ρ1 ρ2 ->
  (Dom_map ρ2) \subset Γ ->
  forall xs bs vs1,
    length xs = length bs ->
    get_list xs ρ1 = Some vs1 ->
    (FromList (live_args xs bs)) \subset (Dom_map ρ2) ->
    exists vs2,
      get_list (live_args xs bs) ρ2 = Some vs2 /\
      Forall2 (V i) (live_args vs1 bs) vs2.
Proof.
  unfold G.
  intros HG HS xs.
  induction xs; simpl; intros.
  - inv H0.
    destruct bs; simpl in *; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H0.
    destruct bs; inv H.
    destruct b; simpl in *.
    + unfold Ensembles.Included, Ensembles.In, Dom_map, FromList in *.
      destruct (H1 a) as [v2 Heqv2].
      apply in_eq.
      rewrite Heqv2.
      edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
      intros.
      apply H1.
      apply in_cons; auto.
      rewrite Heqvs2.
      exists (v2 :: vs2); split; auto.
      constructor; auto.
      destruct (HG a) as [v1' [Heqv1' Hv2']].
      apply HS; eauto.
      rewrite Heq1 in Heqv1'; inv Heqv1'.
      apply Hv2'; auto.
    + eapply IHxs; eauto.
Qed.

(* Compatibility Lemmas *)
Lemma ret_compat Γ x:
  elim_correct Γ (Eret x) (Eret x).
Proof.
  unfold elim_correct, G, E, Ensembles.Included, Ensembles.In, Dom_map.
  intros.
  inv H3.
  - exists 0, OOT; simpl; split; eauto.
  - inv H4.
    edestruct (H x) as [v2 Heqv2]; eauto.
    exists 1, (Res v2); split; auto.
    unfold R.
    destruct (H1 x) as [v1 [Heqv1 Hv2]]; eauto.
    rewrite Heqv1 in H6; inv H6.
    specialize (Hv2 _ Heqv2).
    eapply V_mono with i; try lia; eauto.
Qed.

Lemma prim_val_compat {Γ x p k k'} :
  elim_correct (x |: Γ) k k' ->
  elim_correct Γ (Eprim_val x p k) (Eprim_val x p k').
Proof.
  unfold elim_correct, E.
  intros.
  inv H4.
  - exists 0, OOT; split; simpl; auto.
  - inv H5.
    edestruct (H i (M.set x (Vprim p) ρ1) (M.set x (Vprim p) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk' Rr]]]; eauto.
    + apply Included_trans with (x |: occurs_free (Eprim_val x p k')).
      apply free_prim_val_k_subset.
      apply Included_trans with (x |: (Dom_map ρ2)).
      apply Included_Union_compat; auto.
      apply Included_refl.
      apply Dom_map_set.
    + apply Included_trans with (x |: (Dom_map ρ2)).
      apply Dom_map_set.
      apply Included_Union_compat; auto.
      apply Included_refl.
    + apply G_set; auto.
      destruct i; simpl; eauto.
    + lia.
    + exists (S j2), r2; split; eauto.
      apply R_mono with (i - c); try lia; auto.
Qed.

Lemma Vfun_V {f xs Γ e e'} :
  elim_correct (FromList xs :|: (f |: Γ)) e e' ->
  NoDup (f :: xs) ->
  Disjoint _ (FromList (f :: xs)) Γ ->
  forall {i ρ1 ρ2 bs} w,
    L ! w = Some bs ->
    length xs = length bs ->
    G i Γ ρ1 ρ2 ->
    occurs_free e' \subset (FromList (live_args xs bs) :|: (f |: Dom_map ρ2)) ->
    (Dom_map ρ2) \subset Γ ->
    V i (Vfun f ρ1 w xs e) (Vfun f ρ2 w (live_args xs bs) e').
Proof.
  unfold elim_correct.
  intros He Hn Hd i.
  induction i; simpl; intros; auto.
  exists bs; repeat split; auto; intros.
  inv Hn.
  apply (He (i - (i - j)) ρ3 ρ4).
  - apply Included_trans with (FromList (live_args xs bs) :|: (Dom_map (M.set f (Vfun f ρ2 w (live_args xs bs) e') ρ2))).
    apply Included_trans with (FromList (live_args xs bs) :|: (f |: Dom_map ρ2)); auto.
    apply Included_Union_compat; auto.
    apply Included_refl.
    apply Dom_map_set.
    eapply Dom_map_set_lists; eauto.
  - apply Included_trans with (FromList (live_args xs bs) :|: (Dom_map (M.set f (Vfun f ρ2 w (live_args xs bs) e') ρ2))).
    eapply Dom_map_set_lists; eauto.
    apply Included_Union_compat.
    apply live_args_incl.
    apply Included_trans with (f |: (Dom_map ρ2)).
    apply Dom_map_set.
    apply Included_Union_compat; auto.
    apply Included_refl.
  - eapply G_set_lists; eauto.
    apply G_set; auto.
    + apply G_mono with (S i); auto; lia.
    + apply V_mono with i; try lia.
      apply IHi; auto.
      apply G_mono with (S i); auto; lia.
    + apply Included_trans with (f |: (Dom_map ρ2)).
      apply Dom_map_set.
      apply Included_Union_compat; auto.
      apply Included_refl.
    + constructor; intros x Hc.
      inv Hc; inv Hd.
      apply (H12 x).
      inv H9.
      inv H13; contradiction.
      constructor; auto.
      unfold Ensembles.In, FromList in *.
      apply in_cons; auto.
Qed.

Lemma fun_compat {Γ e e' bs k k'} f w xs :
  elim_correct (FromList xs :|: (f |: Γ)) e e' ->
  elim_correct (f |: Γ) k k' ->
  M.get w L = Some bs ->
  length xs = length bs ->
  NoDup (f :: xs) ->
  Disjoint _ (FromList (f :: xs)) Γ ->
  elim_correct Γ (Efun f w xs e k) (Efun f w (live_args xs bs) e' k').
Proof.
  unfold elim_correct, E.
  intros.
  inv H9.
  - exists 0, OOT; split; simpl; eauto.
  - inv H10.
    edestruct (H0 (i - 1) (M.set f (Vfun f ρ1 w xs e) ρ1) (M.set f (Vfun f ρ2 w (live_args xs bs) e') ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + apply Included_trans with (f |: occurs_free (Efun f w (live_args xs bs) e' k')).
      apply free_fun_k_subset.
      apply Included_trans with (f |: (Dom_map ρ2)).
      apply Included_Union_compat; auto.
      apply Included_refl.
      apply Dom_map_set.
    + apply Included_trans with (f |: (Dom_map ρ2)).
      apply Dom_map_set.
      apply Included_Union_compat; auto.
      apply Included_refl.
    + apply G_set.
      * apply G_mono with i; auto; lia.
      * eapply Vfun_V; eauto.
        apply G_mono with i; auto; lia.
        apply Included_trans with (FromList (live_args xs bs) :|: (f |: (occurs_free (Efun f w (live_args xs bs) e' k')))).
        apply free_fun_e_subset.
        apply Included_Union_compat.
        apply Included_refl.
        apply Included_Union_compat; auto.
        apply Included_refl.
    + exists (S j2), r2; split; auto.
      apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma app_compat {xs bs} Γ f w :
  M.get w L = Some bs ->
  length xs = length bs ->
  elim_correct Γ (Eapp f w xs) (Eapp f w (live_args xs bs)).
Proof.
  unfold elim_correct, G, E.
  intros.
  inv H5.
  - exists 0, OOT; split; simpl; auto.
  - inv H6.
    unfold Ensembles.Included, Ensembles.In, Dom_map in *.
    destruct (H1 f) as [fv2 Heqfv2]; eauto.
    destruct (H3 f) as [fv1 [Heqfv1 Hfv2]]; eauto.
    rewrite Heqfv1 in H9; inv H9.
    specialize (Hfv2 _ Heqfv2).
    destruct fv2.
    + destruct i.
      inv H4.
      simpl in Hfv2.
      destruct Hfv2 as [bs' [Heqw [Heqbs' [Hlen [Heql HVv]]]]]; subst.
      rewrite Heqbs' in H; inv H.

      edestruct (G_get_list H3 H2 xs bs) as [vs2 [Heqvs2 Vvs]]; eauto.
      {
        unfold Ensembles.Included, Ensembles.In, FromList, Dom_map.
        intros.
        eapply H1.
        apply Free_app2; auto.
      }

      destruct (set_lists_length3 (M.set v (Vfun v t w0 (live_args xs' bs) e0) t) (live_args xs' bs) vs2) as [ρ4 Heqρ4].
      rewrite <- (Forall2_length _ _ _ Vvs).
      apply live_args_length.
      rewrite <- (set_lists_length_eq _ _ _ _ H14); auto.

      assert (HE : E (i - (i - i)) ρ'' e ρ4 e0).
      {
        eapply (HVv i vs vs2); eauto.
        apply ForallV_mono with (S i); auto; lia.
      }

      apply (E_mono _ i) in HE; try lia.
      unfold E in HE.
      destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
      exists (S j2), r2; split; eauto.
    + destruct i; try contradiction.
Qed.

Lemma letapp_compat {Γ k k' w bs xs} x f :
  elim_correct (x |: Γ) k k' ->
  M.get w L = Some bs ->
  length xs = length bs ->
  elim_correct Γ (Eletapp x f w xs k) (Eletapp x f w (live_args xs bs) k').
Proof.
  intros.
  specialize (app_compat Γ f w H0 H1); intros Ha.
  unfold elim_correct, E in *.
  intros.
  assert (HFa : occurs_free (Eapp f w (live_args xs bs)) \subset Dom_map ρ2).
  {
    apply Included_trans with (occurs_free (Eletapp x f w (live_args xs bs) k')); auto.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H7; auto.
  }
  specialize (Ha _ _ _ HFa H3 H4).
  inv H6.
  - exists 0, OOT; split; simpl; auto.
  - inv H7.
    + destruct (Ha (S c0) (Res v)) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      simpl in Rra.
      destruct ra; try contradiction.
      edestruct (H (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
      * apply Included_trans with (x |: (occurs_free (Eletapp x f w (live_args xs bs) k'))).
        apply free_letapp_k_subset.
        apply Included_trans with (x |: (Dom_map ρ2)).
        apply Included_Union_compat; auto.
        apply Included_refl.
        apply Dom_map_set.
      * apply Included_trans with (x |: (Dom_map ρ2)).
        apply Dom_map_set.
        apply Included_Union_compat; auto.
        apply Included_refl.
      * apply G_set; auto.
        apply G_mono with i; try lia; auto.
      * exists (j1 + j2), r2; split.
        -- inv Hap.
           inv H6.
           assert ((S c + j2) = S (c + j2)). lia.
           rewrite H6.
           constructor.
           eauto.
        -- apply R_mono with (i - S c0 - c'); try lia; auto.
    + destruct (Ha (S c) OOT) as [j1 [ra [Hap Rra]]]; try lia; eauto.
      exists j1, ra.
      destruct ra; try contradiction.
      split; auto.
      inv Hap; eauto.
      inv H6; eauto.
Qed.

Lemma if_compat {Γ e e' t t'} x :
  elim_correct Γ t t' ->
  elim_correct Γ e e' ->
  elim_correct Γ (Eif x t e) (Eif x t' e').
Proof.
  unfold elim_correct, G, E, Ensembles.Included, Ensembles.In, Dom_map.
  intros Ht He. intros.
  inv H3.
  - exists 0, OOT; simpl; eauto.
  - inv H4.
    + edestruct Ht with (j1 := c) as [j2 [r2 [Ht' Rr]]]; eauto; try lia.
      exists (S j2), r2; split; eauto.
      constructor; auto.
      apply BStep_if_true; auto.
      destruct (H x) as [v2 Heqv2]; eauto.
      destruct (H1 x) as [v1 [Heqv1 Hv2]]; eauto.
      rewrite Heqv1 in H10; inv H10.
      specialize (Hv2 _ Heqv2).
      destruct v2.
      destruct i; contradiction.
      destruct i; simpl in Hv2; subst; auto.
      apply R_mono with (i - c); try lia; auto.
    + edestruct He with (j1 := c) as [j2 [r2 [He' Rr]]]; eauto; try lia.
      exists (S j2), r2; split; eauto.
      constructor; auto.
      apply BStep_if_false; auto.
      destruct (H x) as [v2 Heqv2]; eauto.
      destruct (H1 x) as [v1 [Heqv1 Hv2]]; eauto.
      rewrite Heqv1 in H10; inv H10.
      specialize (Hv2 _ Heqv2).
      destruct v2.
      destruct i; contradiction.
      destruct i; simpl in Hv2; subst; auto.
      apply R_mono with (i - c); try lia; auto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {Γ e e'} :
  elim_exp Γ e e' -> elim_correct Γ e e'.
Proof.
  intro H.
  induction H.
  - apply ret_compat; auto.
  - eapply fun_compat; eauto.
  - eapply app_compat; eauto.
  - eapply letapp_compat; eauto.
  - eapply prim_val_compat; eauto.
  - apply if_compat; auto.
Qed.

End DPE.

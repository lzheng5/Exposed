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
Inductive trans (Γ : A0.vars) : label -> A0.exp -> label -> A1.exp -> Prop :=
| Trans_ret :
  forall {x l0},
    (x \in Γ) ->
    trans Γ l0 (A0.Eret x) l0 (A1.Eret x)

| Trans_fun :
  forall l2 {f xs e0 k0 e1 k1 l0 l1 l3},
    l1 = next_label l0 ->
    trans (FromList xs :|: (f |: Γ)) l1 e0 l2 e1 ->
    trans (f |: Γ) l2 k0 l3 k1 ->
    trans Γ l0 (A0.Efun f xs e0 k0) l3 (A1.Efun f l0 xs e1 k1)

| Trans_app :
  forall {f xs l0 l1},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    l1 = next_label l0 ->
    trans Γ l0 (A0.Eapp f xs) l1 (A1.Eapp f l0 xs)

| Trans_letapp :
  forall {x f xs k0 k1 l0 l1 l2},
    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    l1 = next_label l0 ->
    trans (x |: Γ) l1 k0 l2 k1 ->
    trans Γ l0 (A0.Eletapp x f xs k0) l2 (A1.Eletapp x f l0 xs k1)

| Trans_constr :
  forall {x t xs k0 k1 l0 l1 l2},
    (FromList xs \subset Γ) ->
    l1 = next_label l0 ->
    trans (x |: Γ) l1 k0 l2 k1 ->
    trans Γ l0 (A0.Econstr x t xs k0) l2 (A1.Econstr x l0 t xs k1)

| Trans_proj :
  forall {x y k0 k1 n l0 l1 l2},
    (y \in Γ) ->
    l1 = next_label l0 ->
    trans (x |: Γ) l1 k0 l2 k1 ->
    trans Γ l0 (A0.Eproj x n y k0) l2 (A1.Eproj x l0 n y k1)

| Trans_case :
  forall l2 {x cl0 cl1 l0 l1},
    (x \in Γ) ->
    l1 = next_label l0 ->
    trans_case Γ l1 cl0 l2 cl1 ->
    trans Γ l0 (A0.Ecase x cl0) l2 (A1.Ecase x l0 cl1)

with trans_case (Γ : A0.vars) : label -> list (A0.ctor_tag * A0.exp) -> label -> list (A1.ctor_tag * A1.exp) -> Prop :=
| Trans_case_nil :
  forall {l0},
    trans_case Γ l0 [] l0 []

| Trans_case_cons :
  forall l1 {l0 l2 e0 e1 t cl0 cl1},
    trans Γ l0 e0 l1 e1 ->
    trans_case Γ l1 cl0 l2 cl1 ->
    trans_case Γ l0 ((t, e0) :: cl0) l2 ((t, e1) :: cl1).

Hint Constructors trans : core.
Hint Constructors trans_case : core.

Scheme trans_mut := Induction for trans Sort Prop
with trans_case_mut := Induction for trans_case Sort Prop.

Lemma trans_le Γ l1 e1 l2 e2 :
  trans Γ l1 e1 l2 e2 ->
  Pos.le l1 l2.
Proof.
  intro H.
  induction H using trans_mut with (P0 := fun Γ l0 cl0 l1 cl1 tr =>
                                            Pos.le l0 l1);
    simpl; intros;
    try Pos.order;
    try (pose proof (next_label_le l0); subst l1; eauto;
         Pos.order).
Qed.

Lemma trans_case_le Γ l1 cl1 l2 cl2 :
  trans_case Γ l1 cl1 l2 cl2 ->
  Pos.le l1 l2.
Proof.
  intro H.
  induction H; simpl; intros; eauto;
    try Pos.order.
  eapply trans_le in H; eauto.
  Pos.order.
Qed.

Lemma has_label_case cl:
  forall l0 l x,
    has_label (Ecase x l0 cl) l ->
    (l0 = l \/
     Exists (fun '(_, e) => l \in (has_label e)) cl).
Proof.
  induction cl; simpl; intros.
  - inv H.
    left; auto.
  - inv H.
    + left; auto.
    + right; auto.
    + eapply IHcl in H5; eauto.
      inv H5.
      * left; eauto.
      * right.
        apply Exists_cons.
        right; auto.
Qed.

Lemma trans_inv Γ l1 e1 l2 e2 :
  trans Γ l1 e1 l2 e2 ->
  forall l,
    (l \in has_label e2) ->
    (Pos.le l1 l /\ Pos.lt l l2).
Proof.
  intro H.
  induction H using trans_mut with (P0 := fun Γ l0 cl0 l1 cl1 tr =>
                                            forall l,
                                              Exists (fun '(t, e) => (l \in has_label e)) cl1 ->
                                              (Pos.le l0 l /\ Pos.lt l l1));
  simpl; intros.
  - inv H.
  - inv H1;
      apply trans_le in H;
      apply trans_le in H0.
    + split; try (eapply Pos.le_refl; eauto).
      pose proof (next_label_lt l).
      Pos.order.
    + pose proof (next_label_lt l0).
      split;
        eapply IHtrans1 in H8; eauto; inv H8;
        Pos.order.
    + pose proof (next_label_lt l0).
      split;
        eapply IHtrans2 in H8; eauto; inv H8;
        Pos.order.
  - inv H.
    split; try Pos.order.
    eapply next_label_lt; eauto.
  - eapply trans_le in H; eauto.
    inv H0.
    + split; try Pos.order.
      pose proof (next_label_lt l).
      Pos.order.
    + eapply IHtrans in H7; eauto; inv H7.
      pose proof (next_label_lt l0).
      split; Pos.order.
  - eapply trans_le in H; eauto.
    inv H0.
    + split; try Pos.order.
      pose proof (next_label_lt l).
      Pos.order.
    + eapply IHtrans in H7; eauto; inv H7.
      pose proof (next_label_lt l0).
      split; Pos.order.
  - eapply trans_le in H; eauto.
    inv H0.
    + split; try Pos.order.
      pose proof (next_label_lt l).
      Pos.order.
    + eapply IHtrans in H7; eauto; inv H7.
      pose proof (next_label_lt l0).
      split; Pos.order.
  - inv H.
    + split; try Pos.order.
      eapply trans_case_le in t; eauto.
      pose proof (next_label_lt l).
      Pos.order.
    + assert (Hl : (next_label l0 <= l < l2)%positive) by (eapply IHtrans; eauto).
      inv Hl.
      pose proof (next_label_lt l0).
      split; Pos.order.
    + eapply has_label_case in H4; eauto.
      inv H4.
      * split; try (eapply Pos.le_refl; eauto).
        eapply trans_case_le in t; eauto.
        eapply Pos.lt_le_trans; eauto.
        eapply next_label_lt; eauto.
      * assert (Hl : (next_label l0 <= l < l2)%positive) by (eapply IHtrans; eauto).
        inv Hl.
        split; auto.
        eapply Pos.le_trans; eauto.
        eapply next_label_le; eauto.
  - apply Exists_nil in H; inv H.
  - inv H0.
    + apply IHtrans in H2; inv H2.
      split; auto.
      eapply Pos.lt_le_trans; eauto.
      eapply trans_case_le; eauto.
    + apply IHtrans0 in H2; inv H2.
      split; auto.
      eapply Pos.le_trans; eauto.
      eapply trans_le; eauto.
Qed.

Lemma trans_case_inv Γ l1 cl1 l2 cl2 :
  trans_case Γ l1 cl1 l2 cl2 ->
  forall l,
    Exists (fun '(_, e) => (l \in has_label e)) cl2 ->
    (Pos.le l1 l /\ Pos.lt l l2).
Proof.
  intros H.
  induction H; simpl; intros; eauto.
  - inv H.
  - inv H1.
    + eapply trans_inv in H; eauto; inv H.
      eapply trans_case_le in H0; eauto.
      split; Pos.order.
    + eapply IHtrans_case in H3; eauto; inv H3.
      split; auto.
      eapply trans_le in H; eauto.
      Pos.order.
Qed.

Lemma trans_case_unique_label_case_inv Γ l1 cl1 l2 cl2:
  trans_case Γ l1 cl1 l2 cl2 ->
  forall L,
    unique_label_case cl2 L ->
    forall l,
      (l \in L) ->
      (Pos.le l1 l /\ Pos.lt l l2).
Proof.
  intro H.
  induction H; simpl; intros.
  - inv H.
    inv H0.
  - inv H1.
    inv H2.
    + eapply trans_inv in H; eauto; inv H.
      eapply trans_case_le in H0; eauto.
      split; Pos.order.
    + assert (Hl : (l1 <= l < l2)%positive) by (eapply IHtrans_case; eauto).
      inv Hl.
      apply trans_le in H; eauto.
      split; Pos.order.
Qed.

Theorem trans_unique_label Γ l1 e1 l2 e2 :
  trans Γ l1 e1 l2 e2 ->
  unique_label e2.
Proof.
  intro H.
  induction H using trans_mut with (P0 := fun Γ l0 cl0 l1 cl1 tr =>
                                            exists L,
                                              unique_label_case cl1 L);
  simpl; intros; auto.
  - econstructor; eauto.
    + intro Hc.
      eapply trans_inv in H; eauto; inv H.
      pose proof (next_label_lt l0).
      Pos.order.
    + intros Hc.
      eapply trans_inv in H0; eauto; inv H0.
      pose proof (next_label_lt l0).
      eapply trans_le in H.
      Pos.order.
    + constructor; intros.
      intros Hc.
      inv Hc.
      eapply trans_inv in H; eauto; inv H.
      eapply trans_inv in H0; eauto; inv H0.
      Pos.order.
  - econstructor; eauto.
    intros Hc.
    eapply trans_inv in H; eauto; inv H.
    pose proof (next_label_lt l0).
    Pos.order.
  - econstructor; eauto.
    intros Hc.
    eapply trans_inv in H; eauto; inv H.
    pose proof (next_label_lt l0).
    Pos.order.
  - econstructor; eauto.
    intros Hc.
    eapply trans_inv in H; eauto; inv H.
    pose proof (next_label_lt l0).
    Pos.order.
  - destruct IHtrans as [L HU].
    econstructor; eauto.
    intros Hc.
    eapply trans_case_unique_label_case_inv in t; eauto; inv t.
    pose proof (next_label_lt l0); Pos.order.
  - eexists; eauto.
  - destruct IHtrans0 as [L HU].
    exists ((has_label e1) :|: L).
    econstructor; eauto.
    constructor; intros; intro Hc.
    inv Hc.
    eapply trans_inv in H; eauto; inv H.
    eapply trans_case_unique_label_case_inv in t0; eauto; inv t0.
    Pos.order.
Qed.

Lemma trans_exp_inv {Γ l e l' e'} :
  trans Γ l e l' e' ->
  (A1.occurs_free e') \subset (A0.occurs_free e).
Proof.
  intros H.
  induction H using trans_mut with (P0 := fun Γ l0 cl0 l1 cl1 tr =>
                                            (A1.occurs_free_case cl1) \subset (A0.occurs_free_case cl0));
    unfold Ensembles.Included, Ensembles.In in *;
    simpl; intros; auto.
  - inv H; auto.
  - inv H1; auto.
  - inv H; auto.
  - inv H0; auto.
  - inv H0; auto.
  - inv H0; auto.
  - inv H; auto.
    + inv t.
      assert (A0.occurs_free_case ((c, e1) :: cl1) x0).
      {
        eapply IHtrans; simpl; eauto.
        eapply Union_introl; eauto.
      }
      eapply A0.occurs_free_case_compat; eauto.
    + inv t.
      eapply A1.occurs_free_case_inv in H4; eauto.
      inv H4; subst; auto.
      assert (A0.occurs_free_case ((c, e1) :: cl1) x0).
      {
        eapply IHtrans; simpl; eauto.
        eapply Union_intror; eauto.
      }
      eapply A0.occurs_free_case_compat; eauto.
  - inv H0.
    + eapply IHtrans in H1; eauto.
      left; auto.
    + eapply IHtrans0 in H1; eauto.
      right; auto.
Qed.

(* Alternative Simpler Specification
   Note this is directly based on `unique_label` *)
Inductive trans' (Γ : A0.vars) : A0.exp -> A1.exp -> Prop :=
| Trans'_ret :
  forall {x},
    (x \in Γ) ->
    trans' Γ (A0.Eret x) (A1.Eret x)

| Trans'_fun :
  forall {f xs e0 k0 e1 k1 l},
    (~ l \in has_label e1) ->
    (~ l \in has_label k1) ->
    Disjoint _ (has_label e1) (has_label k1) ->
    trans' (FromList xs :|: (f |: Γ)) e0 e1 ->
    trans' (f |: Γ) k0 k1 ->
    trans' Γ (A0.Efun f xs e0 k0) (A1.Efun f l xs e1 k1)

| Trans'_app :
  forall {f xs l},
    trans' Γ (A0.Eapp f xs) (A1.Eapp f l xs)

| Trans'_letapp :
  forall {x f xs k0 k1 l},
    (~ l \in has_label k1) ->
    (FromList xs \subset Γ) ->
    trans' (x |: Γ) k0 k1 ->
    trans' Γ (A0.Eletapp x f xs k0) (A1.Eletapp x f l xs k1)

| Trans'_constr :
  forall {x t xs k0 k1 l},
    (~ l \in has_label k1) ->
    (FromList xs \subset Γ) ->
    trans' (x |: Γ) k0 k1 ->
    trans' Γ (A0.Econstr x t xs k0) (A1.Econstr x l t xs k1)

| Trans'_proj :
  forall {x y k0 k1 n l},
    (~ l \in has_label k1) ->
    (y \in Γ) ->
    trans' (x |: Γ) k0 k1 ->
    trans' Γ (A0.Eproj x n y k0) (A1.Eproj x l n y k1)

| Trans'_case :
  forall {x cl0 cl1 l L},
    (~ l \in L) ->
    (x \in Γ) ->
    trans_case' Γ cl0 cl1 L ->
    trans' Γ (A0.Ecase x cl0) (A1.Ecase x l cl1)

with trans_case' (Γ : A0.vars) : list (A0.ctor_tag * A0.exp) -> list (A1.ctor_tag * A1.exp) -> labels -> Prop :=
| Trans_case'_nil :
  trans_case' Γ [] [] (Empty_set _)

| Trans_case'_cons :
  forall {e0 e1 c cl0 cl1 L},
    Disjoint _ (has_label e1) L ->
    trans' Γ e0 e1 ->
    trans_case' Γ cl0 cl1 L ->
    trans_case' Γ ((c, e0) :: cl0) ((c, e1) :: cl1) ((has_label e1) :|: L).

Hint Constructors trans' : core.
Hint Constructors trans_case' : core.

Scheme trans'_mut := Induction for trans' Sort Prop
with trans_case'_mut := Induction for trans_case' Sort Prop.

Lemma trans_case_trans_case'_inv Γ l1 cl1 l2 cl2:
  trans_case Γ l1 cl1 l2 cl2 ->
  forall L,
    trans_case' Γ cl1 cl2 L ->
    forall l,
      (l \in L) ->
      (Pos.le l1 l /\ Pos.lt l l2).
Proof.
  intro H.
  induction H; simpl; intros.
  - inv H.
    inv H0.
  - inv H1.
    inv H2.
    + eapply trans_inv in H; eauto; inv H.
      eapply trans_case_le in H0; eauto.
      split; Pos.order.
    + assert (Hl : (l1 <= l < l2)%positive) by (eapply IHtrans_case; eauto).
      inv Hl.
      apply trans_le in H; eauto.
      split; Pos.order.
Qed.

Lemma trans_trans' Γ l0 e0 l1 e1 :
  trans Γ l0 e0 l1 e1 ->
  trans' Γ e0 e1.
Proof.
  intro H.
  induction H using trans_mut with (P0 := fun Γ l0 cl0 l1 cl1 tr =>
                                            exists L,
                                              trans_case' Γ cl0 cl1 L); eauto.
  - econstructor; eauto.
    + intro Hc.
      eapply trans_inv in H; eauto; inv H.
      pose proof (next_label_lt l0).
      Pos.order.
    + intros Hc.
      eapply trans_inv in H0; eauto; inv H0.
      pose proof (next_label_lt l0).
      eapply trans_le in H.
      Pos.order.
    + constructor; intros.
      intros Hc.
      inv Hc.
      eapply trans_inv in H; eauto; inv H.
      eapply trans_inv in H0; eauto; inv H0.
      Pos.order.
  - econstructor; eauto.
    intros Hc.
    eapply trans_inv in H; eauto; inv H.
    pose proof (next_label_lt l0).
    Pos.order.
  - econstructor; eauto.
    intros Hc.
    eapply trans_inv in H; eauto; inv H.
    pose proof (next_label_lt l0).
    Pos.order.
  - econstructor; eauto.
    intros Hc.
    eapply trans_inv in H; eauto; inv H.
    pose proof (next_label_lt l0).
    Pos.order.
  - destruct IHtrans as [L HU].
    econstructor; eauto.
    intros Hc.
    eapply trans_case_trans_case'_inv in t; eauto; inv t.
    pose proof (next_label_lt l0); Pos.order.
  - destruct IHtrans0 as [L HU].
    exists ((has_label e1) :|: L).
    econstructor; eauto.
    constructor; intros; intro Hc.
    inv Hc.
    eapply trans_inv in H; eauto; inv H.
    eapply trans_case_trans_case'_inv in t0; eauto; inv t0.
    Pos.order.
Qed.

Lemma trans'_unique_label Γ e0 e1 :
  trans' Γ e0 e1 ->
  unique_label e1.
Proof.
  intro H.
  induction H using trans'_mut with (P0 := fun Γ cl0 cl1 L tr =>
                                             unique_label_case cl1 L);
    intros; eauto.
Qed.

Theorem trans_unique_label' Γ l1 e1 l2 e2 :
  trans Γ l1 e1 l2 e2 ->
  unique_label e2.
Proof.
  intros.
  eapply trans'_unique_label; eauto.
  eapply trans_trans'; eauto.
Qed.

(* TODO: use trans' as default spec *)

(* Cross-language Logical Relations *)
Definition R' (P : nat -> A0.val -> A1.wval -> Prop) (i : nat) (r1 : A0.res) (r2 : A1.res) :=
  match r1, r2 with
  | A0.OOT, A1.OOT => True
  | A0.Res v1, A1.Res v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> A0.val -> A1.wval -> Prop) (i : nat) (ρ1 : A0.env) (e1 :A0.exp) (ρ2 : A1.env) (e2 : A1.exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    A0.bstep_fuel ρ1 e1 j1 r1 ->
    exists j2 r2,
      A1.bstep_fuel ρ2 e2 j2 r2 /\
      R' P (i - j1) r1 r2.

Fixpoint V (i : nat) (v1 : A0.val) (wv2 : A1.wval) {struct i} : Prop :=
  match wv2 with
  | A1.TAG _ l2 v2 =>
      match v1, v2 with
      | A0.Vconstr c1 vs1, A1.Vconstr c2 vs2 =>
        c1 = c2 /\
        match i with
        | 0 => length vs1 = length vs2
        | S i0 => Forall2 (V i0) vs1 vs2
        end

      | A0.Vfun f1 ρ1 xs1 e1, A1.Vfun f2 ρ2 xs2 e2 =>
          length xs1 = length xs2 /\
          match i with
          | 0 => True
          | S i0 =>
              forall j vs1 vs2 ρ3 ρ4,
                j <= i0 ->
                Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                set_lists xs1 vs1 (M.set f1 (A0.Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
                set_lists xs2 vs2 (M.set f2 (Tag l2 (A1.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                E' V (i0 - (i0 - j)) ρ3 e1 ρ4 e2
          end

      | _, _ => False
      end
  end.

Definition R := (R' V).

Definition E := (E' V).

(* Inversion Lemmas *)
Lemma R_res_inv_l i v1 r2 :
  R i (A0.Res v1) r2 ->
  exists v2, r2 = A1.Res v2 /\ V i v1 v2.
Proof.
  intros.
  destruct r2; simpl in *; try contradiction.
  eexists; split; eauto.
Qed.

(* Environment Relation *)
Definition G i Γ ρ1 ρ2 :=
  forall x,
    (x \in Γ) ->
    forall v1,
      M.get x ρ1 = Some v1 ->
      exists v2,
        M.get x ρ2 = Some v2 /\
        V i v1 v2.

(* Environment Lemmas *)
Lemma G_subset Γ1 Γ2 {i ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  Γ2 \subset Γ1 ->
  G i Γ2 ρ1 ρ2.
Proof.
  unfold G.
  intros; eauto.
Qed.

Lemma G_get {Γ1 i ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  forall x v1,
    (x \in Γ1) ->
    M.get x ρ1 = Some v1 ->
    exists v2,
      M.get x ρ2 = Some v2 /\
      V i v1 v2.
Proof.
  unfold G.
  intros.
  edestruct H as [Hr1 HG]; eauto.
Qed.

Lemma G_get_list {i Γ1 ρ1 ρ2} :
  G i Γ1 ρ1 ρ2 ->
  forall xs vs1,
    (FromList xs) \subset Γ1 ->
    get_list xs ρ1 = Some vs1 ->
    exists vs2,
      get_list xs ρ2 = Some vs2 /\
      Forall2 (V i) vs1 vs2.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - inv H0; eauto.
  - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
    inv H0.
    unfold Ensembles.Included, Ensembles.In, FromList in *.
    edestruct (G_get HG) as [v2 [Heqv2 HV]]; eauto.
    eapply (H a).
    apply in_eq.
    edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
    + intros.
      apply H.
      apply in_cons; auto.
    + rewrite Heqvs2.
      exists (v2 :: vs2); split; auto.
      rewrite Heqv2; auto.
Qed.

Lemma G_set {i Γ1 ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  forall {x v1 v2},
    V i v1 v2 ->
    G i (x |: Γ1) (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  unfold G.
  intros.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss in *.
    inv H2.
    eexists; split; eauto; intros.
  - rewrite M.gso in *; auto.
    inv H1.
    inv H3; try contradiction.
    edestruct H as [v1' [Heqv1' Hv2]]; eauto.
Qed.

Lemma G_set_lists {i Γ1 ρ1 ρ2}:
  G i Γ1 ρ1 ρ2 ->
  forall {xs vs1 vs2 ρ3 ρ4},
    Forall2 (V i) vs1 vs2 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists xs vs2 ρ2 = Some ρ4 ->
    G i (FromList xs :|: Γ1) ρ3 ρ4.
Proof.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    inv H0; inv H1.
    eapply G_subset; eauto.
    rewrite FromList_nil.
    erewrite Union_Empty_set_neut_l; eauto.
    apply Included_refl.
  - destruct vs1; try discriminate.
    destruct vs2; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
    inv H; inv H0; inv H1.
    unfold G.
    intros.
    destruct (M.elt_eq x a); subst.
    + repeat rewrite M.gss in *; eauto.
      inv H0.
      eexists; split; eauto.
    + rewrite M.gso in *; auto.
      eapply IHxs; eauto.
      eapply not_In_cons_Union; eauto.
Qed.

(* Monotonicity Lemmas *)
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

Lemma V_mono i :
  forall {j v1 v2},
    V i v1 v2 ->
    j <= i ->
    V j v1 v2.
Proof.
  induction i using lt_wf_rec; intros.
  destruct v2.
  destruct i; simpl in H0;
    destruct j; simpl; intros.
  - destruct v1; destruct v; try contradiction; eauto.
  - inv H1.
  - destruct v1; destruct v; try contradiction.
    + destruct H0.
      split; auto.
    + destruct H0 as [Hc HV]; subst.
      repeat split; auto.
      eapply Forall2_length; eauto.
  - repeat (split; auto).
    destruct v1; destruct v; try contradiction;
      destruct H0 as [Hlen HV]; subst.
    + split; auto; intros.
      specialize (HV j0 vs1 vs2 ρ3 ρ4).
      rewrite normalize_step in *; try lia.
      apply HV; eauto; lia.
    + repeat split; auto.
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

Lemma E_mono {ρ1 ρ2 e1 e2} i j:
  E i ρ1 e1 ρ2 e2 ->
  j <= i ->
  E j ρ1 e1 ρ2 e2.
Proof.
  unfold E, R, E', R'.
  intros.
  destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
  exists j2, r2; split; eauto.
  apply R_mono with (i - j1); try lia; auto.
Qed.

Lemma G_mono {Γ ρ1 ρ2} i j:
  G i Γ ρ1 ρ2 ->
  j <= i ->
  G j Γ ρ1 ρ2.
Proof.
  unfold G.
  intros.
  edestruct H as [v2 [Heqv2 HV]]; eauto.
  eexists; eexists; repeat split; eauto.
  apply V_mono with i; eauto.
Qed.

(* Compatibility Lemmas *)
Definition trans_correct Γ e1 e2 :=
  forall i ρ1 ρ2,
    G i Γ ρ1 ρ2 ->
    E i ρ1 e1 ρ2 e2.

Fixpoint trans_correct_case (Γ : A0.vars) (cl1 : list (A0.ctor_tag * A0.exp)) (cl2 : list (A1.ctor_tag * A1.exp)) :=
  match cl1, cl2 with
  | [], [] => True
  | ((c1, e1) :: cl1'), ((c2, e2) :: cl2') =>
      c1 = c2 /\
      trans_correct Γ e1 e2 /\
      trans_correct_case Γ cl1' cl2'
  | _, _ => False
  end.

Lemma ret_compat Γ x :
  (x \in Γ) ->
  trans_correct Γ (A0.Eret x) (A1.Eret x).
Proof.
  unfold trans_correct, G, E, E', R, R', Ensembles.Included, Ensembles.In, Dom_map.
  intros.
  inv H2.
  - exists 0, A1.OOT; split; auto.
  - inv H3.
    edestruct (G_get H0) as [v2 [Heqv2 HV]]; eauto.
    exists 1, (A1.Res v2); split; auto.
    apply V_mono with i; try lia; auto.
Qed.

Lemma Vfun_V Γ1 f l xs e e' :
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  forall {i ρ1 ρ2},
    G i Γ1 ρ1 ρ2 ->
    V i (A0.Vfun f ρ1 xs e) (Tag l (A1.Vfun f ρ2 xs e')).
Proof.
  unfold trans_correct.
  intros He i.
  induction i; simpl; intros; auto;
    repeat (split; auto); intros.

  apply (He (i - (i - j)) ρ3 ρ4); auto.
  eapply G_set_lists; eauto.
  eapply G_set; eauto.
  - apply G_mono with (S i); eauto; lia.
  - apply V_mono with i; try lia.
    eapply IHi; eauto.
    apply G_mono with (S i); eauto; lia.
Qed.

Lemma fun_compat Γ e e' l k k' f xs :
  trans_correct (FromList xs :|: (f |: Γ)) e e' ->
  trans_correct (f |: Γ) k k' ->
  trans_correct Γ (A0.Efun f xs e k) (A1.Efun f l xs e' k').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H3.
  - exists 0, A1.OOT; split; simpl; eauto.
  - inv H4.
    edestruct (H0 (i - 1) (M.set f (A0.Vfun f ρ1 xs e) ρ1) (M.set f (Tag l (A1.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    + eapply G_set; eauto.
      apply G_mono with i; eauto; lia.
      eapply Vfun_V; eauto.
      apply G_mono with i; eauto; lia.
    + exists (S j2), r2; split; auto.
      apply R_mono with ((i - 1) - c); try lia; auto.
Qed.

Lemma app_compat Γ xs f l :
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  trans_correct Γ (A0.Eapp f xs) (A1.Eapp f l xs).
Proof.
  unfold trans_correct, G, E, E'.
  intros.
  inv H3.
  - exists 0, A1.OOT; split; simpl; auto.
  - inv H4.
    edestruct (G_get H1 f) as [fv2 [Heqfv2 HV]]; eauto.
    destruct i.
    inv H2.
    destruct fv2; simpl in HV;
      destruct v; try contradiction.
    destruct HV as [Hlen HV].

    edestruct (G_get_list H1 xs vs) as [vs2 [Heqvs2 Vvs]]; eauto.

    destruct (set_lists_length3 (M.set v (Tag l0 (A1.Vfun v t l1 e0)) t) l1 vs2) as [ρ4 Heqρ4].
    unfold wval in *.
    rewrite <- (Forall2_length _ _ _ Vvs).
    rewrite <- (set_lists_length_eq _ _ _ _ H8); auto.

    assert (HE : E (i - (i - i)) ρ'' e ρ4 e0).
    {
      eapply (HV i vs vs2); eauto.
      apply V_mono_Forall with (S i); auto; lia.
    }

    apply (E_mono _ i) in HE; try lia.
    unfold E in HE.
    destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.

    exists (S j2), r2; split; eauto.
Qed.

Lemma letapp_compat Γ k k' l xs x f :
  (f \in Γ) ->
  (FromList xs \subset Γ) ->
  trans_correct (x |: Γ) k k' ->
  trans_correct Γ (A0.Eletapp x f xs k) (A1.Eletapp x f l xs k').
Proof.
  intros.
  specialize (app_compat Γ xs f l H H0); intros Ha.
  unfold trans_correct, E, E' in *.
  intros.

  inv H4.
  - exists 0, OOT; split; simpl; auto.
  - inv H5.
    + destruct (Ha i ρ1 ρ2) with (j1 := (S c0)) (r1 := (A0.Res v)) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
      * simpl in HR.
        destruct r2; try contradiction.
        rename w into v0.
        inv Hr1.
        edestruct (H1 (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
        -- eapply G_set; eauto.
           apply G_mono with i; try lia; eauto.

        -- exists ((S c) + j2), r2; split.
           ++ inv H4.
              assert (Hc : (S c + j2) = S (c + j2)) by lia.
              rewrite Hc.
              constructor; auto.
              eapply BStep_letapp_Res; eauto.
           ++ apply R_mono with (i - S c0 - c'); try lia; auto.
    + destruct (Ha i ρ1 ρ2) with (j1 := (S c)) (r1 := A0.OOT) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
      exists j2, r2.
      destruct r2; try contradiction.
      split; auto.
      inv Hr1; eauto.
      inv H4; eauto.
Qed.

Lemma constr_compat Γ x l t xs k k' :
  (FromList xs \subset Γ) ->
  trans_correct (x |: Γ) k k' ->
  trans_correct Γ (A0.Econstr x t xs k) (A1.Econstr x l t xs k').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H3.
  - exists 0, A1.OOT; split; simpl; auto.
  - inv H4.
    destruct (G_get_list H1 xs vs) as [vs' [Heqvs' Hvs]]; auto.
    assert (length vs = length vs').
    {
      unfold wval in *.
      rewrite <- (get_list_length_eq _ _ _ H10).
      rewrite <- (get_list_length_eq _ _ _ Heqvs'); auto.
    }

    edestruct (H0 i (M.set x (A0.Vconstr t vs) ρ1) (M.set x (Tag l (A1.Vconstr t vs')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk' Rr]]]; eauto; try lia.
    + eapply G_set; eauto.
      destruct i; simpl; repeat (split; eauto).
      eapply V_mono_Forall; eauto; lia.
    + exists (S j2), r2; split; eauto.
      apply R_mono with (i - c); try lia; auto.
Qed.

Lemma proj_compat Γ x i y l e e' :
  (y \in Γ) ->
  trans_correct (x |: Γ) e e' ->
  trans_correct Γ (A0.Eproj x i y e) (A1.Eproj x l i y e').
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H3.
  - exists 0, A1.OOT; split; simpl; auto.
  - inv H4.
    edestruct (G_get H1 y) as [v2 [Heqv2 HV]]; eauto.
    destruct i0.
    inv H2.
    destruct v2;
      simpl in HV;
      destruct v0; try contradiction.
    rename c0 into t'.
    destruct HV as [Heqt HFvs]; subst.
    destruct (Forall2_nth_error H11 HFvs) as [v' [Heqv' HFv]].
    edestruct (H0 i0 (M.set x v ρ1) (M.set x v' ρ2)) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
    + eapply G_set; eauto.
      eapply G_mono with (S i0); eauto; try lia.
    + exists (S j2), r2; split; eauto.
Qed.

Lemma case_nil_compat Γ x l0:
  (x \in Γ) ->
  trans_correct Γ (A0.Ecase x []) (A1.Ecase x l0 []).
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H2.
  - exists 0, A1.OOT; split; simpl; auto.
  - inv H3.
    inv H6.
Qed.

Lemma case_cons_compat Γ x l t e e' cl cl':
  (x \in Γ) ->
  trans_correct Γ e e' ->
  trans_correct Γ (A0.Ecase x cl) (A1.Ecase x l cl') ->
  trans_correct Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x l ((t, e') :: cl')).
Proof.
  unfold trans_correct, E, E'.
  intros.
  inv H4.
  - exists 0, OOT; split; simpl; eauto.
  - inv H5.
    edestruct (G_get H2) as [v2 [Heqv2 HV]]; eauto.
    destruct v2.
    destruct i.
    inv H3.
    destruct v; simpl in HV;
      subst; try contradiction.
    destruct HV as [Heqt HFvs]; subst.
    inv H8.
    + edestruct (H0 i ρ1 ρ2) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
      eapply G_mono; eauto.
      exists (S j2), r2; split; eauto.
    + edestruct (H1 (S i) ρ1 ρ2) with (j1 := S c) (r1 := r1) as [j2 [r2 [He' HR]]]; eauto; try lia.
      exists j2, r2; split; eauto.
      inv He'; auto.
      inv H4.
      rewrite Heqv2 in H9; inv H9; eauto.
Qed.

Lemma case_compat cl0:
  forall Γ x l0 cl1,
    (x \in Γ) ->
    trans_correct_case Γ cl0 cl1 ->
    trans_correct Γ (A0.Ecase x cl0) (A1.Ecase x l0 cl1).
Proof.
  induction cl0; simpl; intros.
  - destruct cl1; try contradiction.
    eapply case_nil_compat; eauto.
  - destruct a.
    destruct cl1; try contradiction.
    destruct p.
    rename c0 into c1, e0 into e1.
    rename c into c0, e into e0.
    destruct H0 as [Heqc [He Hcl]]; subst.
    eapply case_cons_compat; eauto.
Qed.

Lemma case_nil_compat' Γ:
  trans_correct_case Γ [] [].
Proof. simpl. auto. Qed.

Lemma case_cons_compat' cl0:
  forall Γ cl1 c e0 e1,
    trans_correct Γ e0 e1 ->
    trans_correct_case Γ cl0 cl1 ->
    trans_correct_case Γ ((c, e0) :: cl0) ((c, e1) :: cl1).
Proof.
  induction cl0; simpl; intros.
  - destruct cl1; try contradiction.
    repeat split; auto.
  - destruct a.
    destruct cl1; try contradiction.
    destruct p.
    destruct H0 as [Heqc [He Hcl]]; subst.
    repeat split; auto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {Γ l e l' e'}:
  trans Γ l e l' e' -> trans_correct Γ e e'.
Proof.
  intros H.
  induction H using trans_mut with (P0 := fun Γ l0 cl0 l1 cl1 tr =>
                                            trans_correct_case Γ cl0 cl1).
  - eapply ret_compat; auto.
  - eapply fun_compat; eauto.
  - eapply app_compat; eauto.
  - eapply letapp_compat; eauto.
  - eapply constr_compat; eauto.
  - eapply proj_compat; eauto.
  - eapply case_compat; eauto.
  - eapply case_nil_compat'; eauto.
  - eapply case_cons_compat'; eauto.
Qed.

(* Top Level *)
Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  Γ2 \subset Γ1 /\
  G i Γ1 ρ1 ρ2.

Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4 :
  G_top i Γ1 ρ1 Γ2 ρ2 ->
  Γ3 \subset Γ1 ->
  Γ4 \subset Γ3 ->
  G_top i Γ3 ρ1 Γ4 ρ2.
Proof.
  unfold G_top.
  intros.
  destruct H as [Hs HG].
  repeat (split; auto).
  eapply G_subset; eauto.
Qed.

Lemma G_top_G : forall {i Γ1 ρ1 Γ2 ρ2},
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    G i Γ1 ρ1 ρ2.
Proof.
  unfold G_top, G.
  intros.
  destruct H as [HΓ HG].
  unfold Ensembles.Included, Ensembles.In, Dom_map in *.
  edestruct HG as [v2 [Heqv2 HV]]; eauto.
Qed.

Definition trans_correct_top etop etop' :=
  A1.occurs_free etop' \subset A0.occurs_free etop /\
  forall i ρ1 ρ2,
    G_top i (A0.occurs_free etop) ρ1 (A1.occurs_free etop') ρ2 ->
    E i ρ1 etop ρ2 etop'.

Lemma trans_correct_top_subset e1 e2 :
  trans_correct_top e1 e2 ->
  A1.occurs_free e2 \subset A0.occurs_free e1.
Proof.
  unfold trans_correct_top.
  intros.
  inv H; auto.
Qed.

Theorem top l etop l' etop':
  trans (A0.occurs_free etop) l etop l' etop' ->
  trans_correct_top etop etop'.
Proof.
  unfold trans_correct_top.
  intros H.
  specialize (fundamental_property H);
    unfold trans_correct; intros.
  split; intros.
  - eapply trans_exp_inv; eauto.
  - eapply H0; eauto.
    eapply G_top_G; eauto.
Qed.

(* Cross-language Compositionality *)

(* Adequacy *)
Theorem adequacy e1 e2:
  trans_correct_top e1 e2 ->
  forall ρ1 ρ2,
    (forall k, G_top k (A0.occurs_free e1) ρ1 (A1.occurs_free e2) ρ2) ->
    forall j1 r1,
      A0.bstep_fuel ρ1 e1 j1 r1 ->
      exists j2 r2,
        A1.bstep_fuel ρ2 e2 j2 r2 /\
        (forall k, R k r1 r2).
Proof.
  intros.
  unfold trans_correct_top in H.
  destruct H as [HS HT].

  assert (HE : E j1 ρ1 e1 ρ2 e2) by (eapply (HT j1); eauto).
  edestruct (HE j1) as [j2 [r2 [Hstep2 HR]]]; eauto.
  eexists; eexists; split; eauto.

  intros.
  assert (HE' : E (j1 + k) ρ1 e1 ρ2 e2) by (eapply HT; eauto).
  edestruct (HE' j1) as [j2' [r2' [Hstep2' HR']]]; eauto; try lia.

  rewrite_math (j1 + k - j1 = k).
  rewrite_math (j1 - j1 = 0).

  destruct r2; destruct r2'; destruct r1;
    simpl in *; auto; try contradiction.

  edestruct (A1.bstep_fuel_deterministic w w0 Hstep2 Hstep2'); subst; eauto.
Qed.

(* Behavioral Refinement *)
Inductive val_ref_ : A0.val -> A1.wval -> Prop :=
| Ref_Vfun :
  forall f1 ρ1 xs1 e1 l0 f2 ρ2 xs2 e2,
    val_ref_ (A0.Vfun f1 ρ1 xs1 e1) (Tag l0 (A1.Vfun f2 ρ2 xs2 e2))

| Ref_Vconstr_nil :
  forall c l0,
    val_ref_ (A0.Vconstr c []) (Tag l0 (A1.Vconstr c []))

| Ref_Vconstr_cons :
  forall c v1 v2 l0 vs1 vs2,
    val_ref_ v1 v2 ->
    val_ref_ (A0.Vconstr c vs1) (Tag l0 (A1.Vconstr c vs2)) ->
    val_ref_ (A0.Vconstr c (v1 :: vs1)) (Tag l0 (A1.Vconstr c (v2 :: vs2))).

Hint Constructors val_ref_ : core.

Definition val_ref := val_ref_.

Hint Unfold val_ref : core.

Lemma val_ref_Vconstr c l0 vs1 vs2 :
  Forall2 val_ref vs1 vs2 ->
  val_ref (A0.Vconstr c vs1) (Tag l0 (A1.Vconstr c vs2)).
Proof.
  intros.
  induction H; simpl; auto.
Qed.

Theorem V_val_ref {v1 v2} :
  (forall i, V i v1 v2) ->
  val_ref v1 v2.
Proof.
  unfold val_ref.
  revert v2.
  induction v1 using val_ind'; intros; simpl.
  - specialize (H 0).
    destruct v2.
    rename H into HV.
    destruct v; try contradiction.
    destruct HV as [Hc Hlen]; subst.

    symmetry in Hlen.
    apply length_zero_iff_nil in Hlen; subst; auto.
  - destruct v2.
    pose proof (H 0) as H0; simpl in *.
    rename H0 into HV.
    destruct v; try contradiction.
    destruct HV as [Hc Hlen]; subst.

    destruct l1; simpl in *; inv Hlen.

    assert (HV' : forall i, V i v1 t /\ V i (A0.Vconstr c l) (Tag l0 (A1.Vconstr c l1))).
    {
      intros.
      specialize (H (S i)); simpl in *.
      destruct H as [_ HFV]; subst.
      inv HFV.
      split; auto.
      destruct i; simpl in *;
        repeat (split; auto);
        try (eapply V_mono_Forall with (S i); eauto).
    }

    assert (HV0 : forall i, V i v1 t) by (intros; destruct (HV' i); auto).
    assert (HV1 : forall i, V i (A0.Vconstr c l) (Tag l0 (A1.Vconstr c l1))) by (intros; destruct (HV' i); auto).

    auto.
  - specialize (H 0); simpl in *.
    destruct v2; try contradiction; auto.
    destruct v; try contradiction; auto.
Qed.

Corollary R_res_val_ref {v1 v2} :
  (forall i, R i (A0.Res v1) (A1.Res v2)) ->
  val_ref v1 v2.
Proof.
  intros; eapply V_val_ref; eauto.
Qed.

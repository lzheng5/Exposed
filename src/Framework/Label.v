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
  forall l1 l2 {l0 e0 e1 t cl0 cl1},
    trans Γ l0 e0 l1 e1 ->
    trans_case Γ l1 cl0 l2 cl1 ->
    trans_case Γ l0 ((t, e0) :: cl0) l2 ((t, e1) :: cl1).

Hint Constructors trans : core.
Hint Constructors trans_case : core.

Scheme trans_mut := Induction for trans Sort Prop
with trans_case_mut := Induction for trans_case Sort Prop.

Lemma trans_label_le Γ l1 e1 l2 e2 :
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

Lemma trans_case_label_le Γ l1 cl1 l2 cl2 :
  trans_case Γ l1 cl1 l2 cl2 ->
  Pos.le l1 l2.
Proof.
  intro H.
  induction H; simpl; intros; eauto;
    try Pos.order.
  eapply trans_label_le in H; eauto.
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

Lemma trans_label_inv Γ l1 e1 l2 e2 :
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
      apply trans_label_le in H;
      apply trans_label_le in H0.
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
  - eapply trans_label_le in H; eauto.
    inv H0.
    + split; try Pos.order.
      pose proof (next_label_lt l).
      Pos.order.
    + eapply IHtrans in H7; eauto; inv H7.
      pose proof (next_label_lt l0).
      split; Pos.order.
  - eapply trans_label_le in H; eauto.
    inv H0.
    + split; try Pos.order.
      pose proof (next_label_lt l).
      Pos.order.
    + eapply IHtrans in H7; eauto; inv H7.
      pose proof (next_label_lt l0).
      split; Pos.order.
  - eapply trans_label_le in H; eauto.
    inv H0.
    + split; try Pos.order.
      pose proof (next_label_lt l).
      Pos.order.
    + eapply IHtrans in H7; eauto; inv H7.
      pose proof (next_label_lt l0).
      split; Pos.order.
  - inv H.
    + split; try Pos.order.
      eapply trans_case_label_le in t; eauto.
      pose proof (next_label_lt l).
      Pos.order.
    + assert (Hl : (next_label l0 <= l < l2)%positive) by (eapply IHtrans; eauto).
      inv Hl.
      pose proof (next_label_lt l0).
      split; Pos.order.
    + eapply has_label_case in H4; eauto.
      inv H4.
      * split; try (eapply Pos.le_refl; eauto).
        eapply trans_case_label_le in t; eauto.
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
      eapply trans_case_label_le; eauto.
    + apply IHtrans0 in H2; inv H2.
      split; auto.
      eapply Pos.le_trans; eauto.
      eapply trans_label_le; eauto.
Qed.

Lemma trans_case_label_inv Γ l1 cl1 l2 cl2 :
  trans_case Γ l1 cl1 l2 cl2 ->
  forall l,
    Exists (fun '(_, e) => (l \in has_label e)) cl2 ->
    (Pos.le l1 l /\ Pos.lt l l2).
Proof.
  intros H.
  induction H; simpl; intros; eauto.
  - inv H.
  - inv H1.
    + eapply trans_label_inv in H; eauto; inv H.
      eapply trans_case_label_le in H0; eauto.
      split; Pos.order.
    + eapply IHtrans_case in H3; eauto; inv H3.
      split; auto.
      eapply trans_label_le in H; eauto.
      Pos.order.
Qed.

(*
Lemma trans_label_inv_r Γ l1 e1 l2 e2 :
  trans Γ l1 e1 l2 e2 ->
  forall l,
    (Pos.le l1 l /\ Pos.lt l l2) ->
    (l \in has_label e2).
Proof.
    intro H.
    induction H using trans_mut with (P0 := fun Γ l0 cl0 l1 cl1 tr =>
                                              forall l,
                                                (Pos.le l0 l /\ Pos.lt l l1) ->
                                                Exists (fun '(t, e) => (l \in has_label e)) cl1);
      simpl; intros.
    -
Admitted.
*)
(*
Lemma not_has_label_case cl l0 l x:
  l0 <> l ->
  Forall (fun '(_, e) => ~ (l \in (has_label e))) cl ->
  ~ (has_label (Ecase x l0 cl) l).
Proof.
  intros.
  generalize dependent l0.
  revert x.
  induction H0; simpl; intros; intros Hc; inv Hc; eauto.
  eapply IHForall; eauto.
Qed.

Lemma trans_label_inv Γ l1 e1 l2 e2 :
  trans Γ l1 e1 l2 e2 ->
  forall l,
    Pos.lt l l1 ->
    ~ (l \in has_label e2).
Proof.
  intro H.
  induction H using trans_mut with (P0 := fun Γ l0 cl0 l1 cl1 tr =>
                                            forall l,
                                              Pos.lt l l0 ->
                                              Forall (fun '(t, e) => ~ (l \in has_label e)) cl1);
  simpl; intros; eauto.
  - intros Hc.
    inv Hc.
  - intros Hc.
    inv Hc.
    + eapply Pos.lt_irrefl; eauto.
    + eapply (IHtrans1 l); eauto.
      eapply Pos.lt_trans; eauto.
      eapply next_label_lt; eauto.
    + eapply (IHtrans2 l); eauto.
      eapply Pos.lt_trans; eauto.
      apply trans_label_le in H.
      eapply Pos.lt_le_trans; eauto.
      eapply next_label_lt; eauto.
  - intro Hc.
    inv Hc.
    eapply Pos.lt_irrefl; eauto.
  - intros Hc.
    inv Hc.
    + eapply Pos.lt_irrefl; eauto.
    + eapply IHtrans; eauto.
      eapply Pos.lt_trans; eauto.
      eapply next_label_lt; eauto.
  - intros Hc.
    inv Hc.
    + eapply Pos.lt_irrefl; eauto.
    + eapply IHtrans; eauto.
      eapply Pos.lt_trans; eauto.
      eapply next_label_lt; eauto.
  - intros Hc.
    inv Hc.
    + eapply Pos.lt_irrefl; eauto.
    + eapply IHtrans; eauto.
      eapply Pos.lt_trans; eauto.
      eapply next_label_lt; eauto.
  - intros Hc.
    inv Hc.
    + eapply Pos.lt_irrefl; eauto.
    + assert (Hl: Pos.lt l l1).
      {
        eapply Pos.lt_trans; eauto.
        eapply next_label_lt; eauto.
      }
      eapply IHtrans in Hl; eauto.
      inv Hl.
      eapply H2; eauto.
    + assert (Hl: Pos.lt l l1).
      {
        eapply Pos.lt_trans; eauto.
        eapply next_label_lt; eauto.
      }
      eapply IHtrans in Hl; eauto.
      inv Hl.
      eapply not_has_label_case; eauto.
      intros Hc; subst.
      eapply Pos.lt_irrefl; eauto.
  - constructor; auto.
    eapply IHtrans0; eauto.
    eapply Pos.lt_le_trans; eauto.
    eapply trans_label_le; eauto.
Qed.
 *)

Lemma trans_unique_label Γ l1 e1 l2 e2 :
  trans Γ l1 e1 l2 e2 ->
  unique_label e2.
Proof.
  intro H.

  induction H using trans_mut with (P0 := fun Γ l0 cl0 l1 cl1 tr =>
                                            Forall (fun '(t, e) => unique_label e) cl1);
  simpl; intros; eauto.
  - econstructor; eauto.
    + intro Hc.
      eapply trans_label_inv in H; eauto; inv H.
      pose proof (next_label_lt l0).
      Pos.order.
    + intros Hc.
      eapply trans_label_inv in H0; eauto; inv H0.
      pose proof (next_label_lt l0).
      eapply trans_label_le in H.
      Pos.order.
    + constructor; intros.
      intros Hc.
      inv Hc.
      eapply trans_label_inv in H; eauto; inv H.
      eapply trans_label_inv in H0; eauto; inv H0.
      Pos.order.
  - econstructor; eauto.
    intros Hc.
    eapply trans_label_inv in H; eauto; inv H.
    pose proof (next_label_lt l0).
    Pos.order.
  - econstructor; eauto.
    intros Hc.
    eapply trans_label_inv in H; eauto; inv H.
    pose proof (next_label_lt l0).
    Pos.order.
  - econstructor; eauto.
    intros Hc.
    eapply trans_label_inv in H; eauto; inv H.
    pose proof (next_label_lt l0).
    Pos.order.
  - generalize dependent l0.
    induction t; intros; simpl; eauto.
    inv IHtrans.
    econstructor; eauto.
    + intros Hc.
      eapply trans_label_inv in H; eauto; inv H.
      pose proof (next_label_lt l3).
      Pos.order.
    + admit.
    + eapply IHt; eauto.
      subst.


    generalize dependent cl0.
    revert l0 l1 l2 x i.
    induction IHtrans; intros; eauto.
    destruct x.
    econstructor; eauto.
    + intros Hc.
      eapply trans_case_label_inv in t; eauto; inv t.
      pose proof (next_label_lt l0); subst l1.
      Pos.order.
    + admit.
    + inv t.
      eapply IHIHtrans; eauto.
      inv t.
Abort.

        assert (Hl : ~ (l0 <= l < l1)%positive).
        {
          intros Hc.
          apply H1.
          eapply trans_label_inv_r; eauto.
        }
        split; auto.


        assert (Hl' : ~ (l0 <= l)%positive).
        {
          intros Hc.
          apply Hl.
          split; auto.

        }

        split; auto.


      }
      inv Hl.
      split; auto.
      eapply Pos.le_trans; eauto.
      eapply next_label_le; eauto.
    +
Abort.

      eapply trans_label_le in t; eauto.
      eapply Pos.lt_le_trans; eauto.
      eapply next_label_lt; eauto.
    + eapply IHtrans in H7; eauto.
      inv H7.
      split; auto.
      eapply Pos.le_trans; eauto.
      eapply next_label_le; eauto.
  -

(*
(* Note this is directly based on `unique_label`
   However, this isn't sufficient to show linking compat *)
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
*)

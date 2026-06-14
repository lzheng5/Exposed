From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

Require Import UntypedExposed.Util.
Require Import UntypedExposed.ANF.
(* Require Import UntypedExposed.Refl. *)

Module Type ExposedParam.
  Parameter elt : Type.
  Parameter L : M.t elt.
  Parameter V_ : ((nat) -> (val) -> (val) -> Prop) ->
                 ((nat -> val -> val -> Prop) -> (web) -> (nat) -> (env) -> (exp) -> (env) -> (exp) -> Prop)
                 -> (nat) -> (val) -> (val) -> Prop.
End ExposedParam.

Module ExposedFunctor (M : ExposedParam).

  Notation elt := M.elt.
  Notation L := M.L.
  Notation V_ := M.V_.

Definition live_map_inv := (forall w, w \in Exposed -> L ! w = None).

(* Logical Relations *)
Definition R' (P : nat -> val -> val -> Prop) (i : nat) (r1 : res) (r2 : res) :=
  match r1, r2 with
  | OOT, OOT => True
  | Res v1, Res v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> val -> val -> Prop) (w : Prop) (i : nat) (ρ1 : env) (e1 : exp) (ρ2 : env) (e2 : exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    bstep_fuel true ρ1 e1 j1 r1 ->
    exists j2 r2,
      bstep_fuel true ρ2 e2 j2 r2 /\
      R' P (i - j1) r1 r2.

Fixpoint V (i : nat) (v1 : val) (v2 : val) {struct i} : Prop :=
  match v1, v2 with
  | Vprim p1, Vprim p2 => p1 = p2
  | Vfun f1 ρ1 w1 xs1 e1, Vfun f2 ρ2 w2 xs2 e2 =>
      w1 = w2 /\ (* web stay the same *)
      match i with
      | 0 => True
      | S i0 =>
          match M.get w1 L with
          | None => (* reflexively related *)
              length xs1 = length xs2 /\
              forall j vs1 vs2 ρ3 ρ4,
                j <= i0 ->
                (w1 \in Exposed -> Forall exposed vs1 /\ Forall exposed vs2) -> (* web can be either exposed or non-exposed *)
                Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                set_lists xs1 vs1 (M.set f1 (Vfun f1 ρ1 w1 xs1 e1) ρ1) = Some ρ3 ->
                set_lists xs2 vs2 (M.set f2 (Vfun f2 ρ2 w2 xs2 e2) ρ2) = Some ρ4 ->
                E' V (w1 \in Exposed) (i0 - (i0 - j)) ρ3 e1 ρ4 e2

          (* TODO: stupid shit *)
          | None => V_refl (fun j v1 v2 => (j <= i0) -> (exposed v1) /\ V (i0 - (i0 - j)) v1 v2) (E' true) i (Vfun f1 ρ1 w1 xs1 e1) (Vfun f2 ρ2 w2 xs2 e2)
          | Some elt => V_ (fun j v1 v2 => (j <= i0) -> V (i0 - (i0 - j)) v1 v2) E' i (Vfun f1 ρ1 w1 xs1 e1) (Vfun f2 ρ2 w2 xs2 e2)
          end
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

Definition G_top i Γ ρ1 ρ2 :=
  Γ <--> (Dom_map ρ1) /\
  (Dom_map ρ1) <--> (Dom_map ρ2) /\
  forall x,
    (x \in Γ) ->
    exists v1 v2,
      M.get x ρ1 = Some v1 /\
      M.get x ρ2 = Some v2 /\
      exposed v1 /\
      V i v1 v2.

Lemma G_top_G : forall {i Γ ρ1 ρ2},
    G_top i Γ ρ1 ρ2 ->
    G i Γ ρ1 ρ2.
Proof.
  unfold G_top, G.
  intros.
  destruct H as [HΓ [Hρ HG]].
  edestruct HG as [v1 [v2 [Heqv1 [Heqv2 [Hev1 HV]]]]]; eauto.
  eexists; split; eauto.
  intros.
  rewrite Heqv2 in H; inv H; auto.
Qed.

Lemma Forall2_exposed_V_relate: forall i j vs1 vs2,
    Forall exposed vs1 ->
    j <= i ->
    (forall n : nat, n < S i -> forall v1 v2 : val, exposed v1 -> V n v1 v2 <-> Refl.V n v1 v2) ->
    Forall2 (V j) vs1 vs2 <->
    Forall2 (Refl.V j) vs1 vs2.
Proof.
  intros.
  revert vs2 H1.
  induction vs1; intros.
  - split; intros; inv H2; auto.
  - inv H.
    split; intros; inv H; constructor; auto.
    + eapply H1; try lia; auto.
    + apply IHvs1; auto.
    + eapply H1; try lia; auto.
    + apply IHvs1; auto.
Qed.

Lemma exposed_V_relate :
  live_map_inv ->
  forall i v1 v2,
    exposed v1 ->
    V i v1 v2 <-> Refl.V i v1 v2.
Proof.
  intro HE.
  intro i.
  induction i using strong_induction; intros.
  destruct i.
  - unfold V, Refl.V.
    destruct v1; destruct v2; split; auto; destruct H2; auto.
  - split; simpl in *; intro.
    + destruct v1; destruct v2; auto.
      destruct H1.
      inv H0.
      erewrite (HE w0) in *; auto.
      destruct H2.
      repeat split; auto; intros.
      destruct H3; auto.

      assert (HE' : E' V (w0 \in Exposed) (i - (i - j)) ρ3 e ρ4 e0).
      {
        eapply H1 with (vs1 := vs1) (vs2 := vs2); try lia; eauto.
        eapply Forall2_exposed_V_relate; eauto.
        intros.
        eapply H; eauto; try lia.
      }

      unfold Refl.E', Refl.R', E', R' in *.
      intros.
      destruct (HE' _ _ H9 H10) as [j2 [r2 [bstep_e0 HR']]].
      exists j2; exists r2; split; auto.
      destruct r1; destruct r2; auto.
      eapply H; try lia; auto.
      inv H10.
      specialize (H12 H4).
      inv H12; auto.
    + destruct v1; destruct v2; auto.
      destruct H1.
      inv H0.
      erewrite (HE w0) in *; auto.
      destruct H2.
      repeat split; auto.
      intros.
      destruct H3; auto.

      assert (HE' : Refl.E' Refl.V (w0 \in Exposed) (i - (i - j)) ρ3 e ρ4 e0).
      {
        eapply H1 with (vs1 := vs1) (vs2 := vs2); try lia; eauto.
        eapply Forall2_exposed_V_relate; eauto.
        intros.
        eapply H; eauto; try lia.
      }

      unfold Refl.E', Refl.R', E', R' in *.
      intros.
      destruct (HE' _ _ H9 H10) as [j2 [r2 [bstep_e0 HR']]].
      exists j2; exists r2; split; auto.
      destruct r1; destruct r2; auto.
      eapply H; try lia; auto.
      inv H10.
      specialize (H12 H4).
      inv H12; auto.
Qed.

Lemma exposed_R_relate {i r1 r2}:
  live_map_inv ->
  exposed_res r1 ->
  R i r1 r2 <-> Refl.R i r1 r2.
Proof.
  intros HExp Hr1.
  unfold R, Refl.R.
  split; intros;
    destruct r1;
    destruct r2;
    auto; inv Hr1;
    apply exposed_V_relate; auto.
Qed.

Lemma exposed_E_relate {i ρ1 ρ2 e1 e2}:
  live_map_inv ->
  E True i ρ1 e1 ρ2 e2 <-> Refl.E True i ρ1 e1 ρ2 e2.
Proof.
  unfold E, Refl.E.
  intros HExp.
  split; intros;
    edestruct H as [j2 [r2 [He2 HR]]]; eauto;
    eexists; eexists; split; eauto;
    eapply exposed_R_relate; eauto;
    inv H1; auto.
Qed.

Lemma G_top_relate {i Γ ρ1 ρ2}:
  live_map_inv ->
  G_top i Γ ρ1 ρ2 <-> Refl.G_top i Γ ρ1 ρ2.
Proof.
  unfold G_top, Refl.G_top.
  intros HExp.
  split; intros (HΓ&Hρ&HG);
    split; auto;
    split; auto;
    intros;
    edestruct HG as [v1 [v2 [Heqv1 [Heqv2 [Hev1 HV]]]]]; eauto;
    exists v1, v2; repeat split; auto;
    apply exposed_V_relate; auto.
Qed.

Definition elim_correct_top etop etop' :=
  ((occurs_free etop) <--> (occurs_free etop')) ->
  forall i ρ1 ρ2,
    G_top i (occurs_free etop) ρ1 ρ2 ->
    E True i ρ1 etop ρ2 etop'.

Theorem top {etop etop'} :
  live_map_inv ->
  elim_correct_top etop etop' ->
  Refl.related_top etop etop'.
Proof.
  intros HExp HElim.
  unfold elim_correct_top, Refl.related_top in *.
  intros.
  eapply exposed_E_relate; eauto.
  eapply HElim; eauto.
  apply G_top_relate; auto.
Qed.

End ExposedFunctor.

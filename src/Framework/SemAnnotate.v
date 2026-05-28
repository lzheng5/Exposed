From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Util W0 ANF0 ANF1 ANF Label Checking Reify Annotate Erase RelComp.

Module AS := ANF0.
Module AI := ANF1.
Module AT := ANF.

Module L := Label.
Module C := Checking.
Module R := Reify.

(* Top-level Logical Relations *)
Definition R' (P : nat -> AS.val -> AT.wval -> Prop) (i : nat) (r1 : AS.res) (r2 : AT.res) :=
  match r1, r2 with
  | AS.OOT, AT.OOT => True
  | AS.Res v1, AT.Res v2 => P i v1 v2
  | _, _ => False
  end.

Definition E' (P : nat -> AS.val -> AT.wval -> Prop) (ex : bool) (i : nat) (ρ1 : AS.env) (e1 :AS.exp) (ρ2 : AT.env) (e2 : AT.exp) : Prop :=
  forall j1 r1,
    j1 <= i ->
    AS.bstep_fuel ρ1 e1 j1 r1 ->
    exists j2 r2,
      AT.bstep_fuel ex ρ2 e2 j2 r2 /\
        R' P (i - j1) r1 r2.

Fixpoint V_top (i : nat) (v1 : AS.val) (wv2 : AT.wval) {struct i} : Prop :=
  wf_val wv2 /\
    exposed wv2 /\
    match wv2 with
    | AT.TAG _ w2 v2 =>
        match v1, v2 with
        | AS.Vconstr c1 vs1, AT.Vconstr c2 vs2 =>
            c1 = c2 /\
              match i with
              | 0 => length vs1 = length vs2
              | S i0 => Forall2 (V_top i0) vs1 vs2
              end

        | AS.Vfun f1 ρ1 xs1 e1, AT.Vfun f2 ρ2 xs2 e2 =>
            (* note function arguments and result are always exposed regardless of whether a function is known or unknown *)
            length xs1 = length xs2 /\
              match i with
              | 0 => True
              | S i0 =>
                  forall j vs1 vs2 ρ3 ρ4,
                    j <= i0 ->
                    Forall exposed vs2 ->
                    Forall2 (V_top (i0 - (i0 - j))) vs1 vs2 ->
                    set_lists xs1 vs1 (M.set f1 (AS.Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
                    set_lists xs2 vs2 (M.set f2 (Tag w2 (AT.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                    E' V_top true (i0 - (i0 - j)) ρ3 e1 ρ4 e2
              end

        | _, _ => False
        end
    end.

Definition V i := Cross (fun v1 v2 => L.V i v1 v2)
                    (Cross (fun v1 v2 => C.V_top i v1 v2)
                       (fun v1 v2 => R.V_top i v1 v2)).

Lemma V_V_top_Forall :
  forall i,
    (forall m : nat,
        m < S i ->
        forall v1 v2,
          exposed v2 ->
          V m v1 v2 <-> V_top m v1 v2) ->
    forall j vs1 vs2,
      j <= i ->
      Forall exposed vs2 ->
      Forall2 (V j) vs1 vs2 <-> Forall2 (V_top j) vs1 vs2.
Proof.
  intros.
  revert vs1 j H0.
  induction H1; simpl; intros.
  - split; intros; inv H1; auto.
  - split; intros; inv H3; constructor; auto;
      solve [ eapply H; try lia; eauto |
              eapply IHForall; eauto ].
Qed.

(* This is not provable.
   The top-level environment will get into the way. *)
Parameter l0 : label.
Lemma V_V_top :
  forall i v1 v2,
    exposed v2 ->
    (V i v1 v2 <-> V_top i v1 v2).
Proof.
  intro i.
  induction i using lt_wf_rec; intros.
  unfold V, Cross.
  split; intros.
  - admit.
  - destruct i; simpl in *;
      destruct H1 as [Hwf [Hex HV]].
    + destruct v2; destruct v1;
        destruct v; try firstorder.
      * (* exists (AI.Tag l0 (AI.Vfun v t l1 e)). (* ? env? *) *)
Abort.

Definition R_top := (R' V_top).

Definition E_top := (E' V_top).

Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
  wf_env ρ2 /\
    Γ2 \subset Γ1 /\
    forall x,
      (x \in Γ1) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
          M.get x ρ2 = Some v2 /\
          V_top i v1 v2.

Definition trans_correct_top etop etop' :=
  AT.occurs_free etop' \subset AS.occurs_free etop /\
    forall i ρ1 ρ2,
      G_top i (AS.occurs_free etop) ρ1 (AT.occurs_free etop') ρ2 ->
      E_top true i ρ1 etop ρ2 etop'.

Definition T_top e1 e2 :=
  exists e3,
    L.trans_correct_top e1 e3 /\
      exists W,
        well_annotated_top W e3 /\
        R.trans_correct_top W e3 e2.

Lemma T_top_trans_correct_top e1 e2 :
  T_top e1 e2 ->
  trans_correct_top e1 e2.
Proof.
  unfold T_top, trans_correct_top, L.trans_correct_top, C.well_annotated_top, R.trans_correct_top.
  intros.
  destruct H as [e3 [HL [W [HC HR]]]].
  destruct HL as [HS1 HL].
  destruct HC as [HW HC].
  destruct HR as [HS2 HR].

  split; intros.
  eapply Included_trans; eauto.

  unfold E_top, E'; intros.
  unfold web_map_sound_top in HW.

  (* Still the top-level environments will get into the way *)
Abort.

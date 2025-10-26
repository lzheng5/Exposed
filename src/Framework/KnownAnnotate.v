From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF0 ANF Refl0 Refl Annotate Erase.

Module A0 := ANF0.
Module A1 := ANF.

(* Known Function Analysis With A Single Exposed Web Id *)

Module M <: Annotate.

  (* Similar to CertiCoq's `Known_exp` *)
  Inductive known_exp (S : Ensemble var) : A0.exp -> Prop :=
  | Known_Ret :
    forall x,
      (~ x \in S) ->
      known_exp S (A0.Eret x)

  | Known_App :
    forall f ys,
      Disjoint _ (FromList ys) S ->
      known_exp S (A0.Eapp f ys)

  | Known_LetApp :
    forall x f ys e,
      Disjoint _ (FromList ys) S ->
      known_exp S e ->
      known_exp S (A0.Eletapp x f ys e)

  | Known_Fun:
    forall f xs e k,
      known_exp S e ->
      known_exp S k ->
      known_exp S (A0.Efun f xs e k)

  | Known_Constr :
    forall x ys ct e,
      Disjoint _ (FromList ys) S ->
      known_exp S e ->
      known_exp S (A0.Econstr x ct ys e)

  | Known_Proj :
    forall x n y e,
      (~ y \in S) ->
      known_exp S e ->
      known_exp S (A0.Eproj x n y e)

  | Known_Case_nil:
    forall x,
      known_exp S (A0.Ecase x [])

  | Known_Case_hd:
    forall x c e ce,
      known_exp S e ->
      known_exp S (A0.Ecase x ce) ->
      known_exp S (A0.Ecase x ((c, e) :: ce)).

  Hint Constructors known_exp : core.

  Definition known_map := M.t web.

  Definition known_map_inv K :=
    forall f w,
      K ! f = Some w ->
      ~ (w \in Exposed).

  (* Outline: *)
  (* 1. build `K : known_map` for every function identifiers (assume unique names) in the program with nonexposed web ids (Note it is not necessary to require them to be distinct though) *)
  (* 2. follow `escape_fun_exp` as in CertiCoq to filter `K` so that its domain satisfies `known_exp` *)
  (* 3. rewrite based on `K` [this is the main step we are focusing on here] *)

  (* TODO: define `analyze` following `escape_fun_exp` in CertiCoq *)
  Parameter analyze : A0.exp -> known_map.

  Axiom analyze_sound :
    forall (e : A0.exp),
      let K := analyze e in
      known_exp (Dom_map K) e /\
      known_map_inv K.

  Parameter w0 : web.
  Axiom w0_exposed : w0 \in Exposed.
  Axiom Exposed_singleton : forall w, w \in Exposed -> w = w0.

  Theorem Exposed_nonempty : exists w, w \in Exposed.
  Proof. exists w0. apply w0_exposed. Qed.

  Section Spec.
    Variable K : known_map.

    (* Specification *)
    Inductive trans_ (Γ : A0.vars) : A0.exp -> A1.exp -> Prop :=
    | Trans_ret :
      forall x,
        K ! x = None ->

        (x \in Γ) ->
        trans_ Γ (A0.Eret x) (A1.Eret x)

    | Trans_fun_known :
      forall {f w xs e k e' k'},
        K ! f = Some w ->
        (~ w \in Exposed) ->

        trans_ (FromList xs :|: (f |: Γ)) e e' ->
        trans_ (f |: Γ) k k' ->
        trans_ Γ (A0.Efun f xs e k) (A1.Efun f w xs e' k')

    | Trans_fun_unknown :
      forall {f xs e k e' k'},
        K ! f = None ->

        trans_ (FromList xs :|: (f |: Γ)) e e' ->
        trans_ (f |: Γ) k k' ->
        trans_ Γ (A0.Efun f xs e k) (A1.Efun f w0 xs e' k')

    | Trans_app_known :
      forall {f w xs},
        K ! f = Some w ->
        (~ w \in Exposed) ->
        Disjoint _ (FromList xs) (Dom_map K) ->

        (f \in Γ) ->
        (FromList xs \subset Γ) ->
        trans_ Γ (A0.Eapp f xs) (A1.Eapp f w xs)

    | Trans_app_unknown :
      forall {f xs},
        K ! f = None ->
        Disjoint _ (FromList xs) (Dom_map K) ->

        (f \in Γ) ->
        (FromList xs \subset Γ) ->
        trans_ Γ (A0.Eapp f xs) (A1.Eapp f w0 xs)

    (* data webs are all exposed *)

    | Trans_constr :
      forall {x t xs k k'},
        Disjoint _ (FromList xs) (Dom_map K) ->

        (FromList xs \subset Γ) ->
        trans_ (x |: Γ) k k' ->
        trans_ Γ (A0.Econstr x t xs k) (A1.Econstr x w0 t xs k')

    | Trans_proj :
      forall {x y k k' n},
        K ! y = None ->

        (y \in Γ) ->
        trans_ (x |: Γ) k k' ->
        trans_ Γ (A0.Eproj x n y k) (A1.Eproj x w0 n y k')

    | Trans_case_nil :
      forall {x},
        (x \in Γ) ->
        trans_ Γ (A0.Ecase x []) (A1.Ecase x w0 [])

    | Trans_case_cons :
      forall {x e e' t cl cl'},
        (x \in Γ) ->
        trans_ Γ e e' ->
        trans_ Γ (A0.Ecase x cl) (A1.Ecase x w0 cl') ->
        trans_ Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x w0 ((t, e') :: cl')).

    Hint Constructors trans_ : core.

    Definition trans := trans_.

    Hint Unfold trans : core.

    (* Cross-language Logical Relations *)
    (* Note this is parameterized by known_map, `K` *)
    Definition R' (P : nat -> A0.val -> A1.wval -> Prop) (i : nat) (r1 : A0.res) (r2 : A1.res) :=
      match r1, r2 with
      | A0.OOT, A1.OOT => True
      | A0.Res v1, A1.Res v2 => P i v1 v2
      | _, _ => False
      end.

    Definition E' (P : nat -> A0.val -> A1.wval -> Prop) (ex : bool) (i : nat) (ρ1 : A0.env) (e1 :A0.exp) (ρ2 : A1.env) (e2 : A1.exp) : Prop :=
      forall j1 r1,
        j1 <= i ->
        A0.bstep_fuel ρ1 e1 j1 r1 ->
        exists j2 r2,
          A1.bstep_fuel ex ρ2 e2 j2 r2 /\
          R' P (i - j1) r1 r2.

    Fixpoint V (i : nat) (v1 : A0.val) (wv2 : A1.wval) {struct i} : Prop :=
      wf_val wv2 /\
      match wv2 with
      | A1.TAG _ w2 v2 =>
          match v1, v2 with
          | A0.Vconstr c1 vs1, A1.Vconstr c2 vs2 =>
              exposed wv2 /\
              c1 = c2 /\
              match i with
              | 0 => length vs1 = length vs2
              | S i0 => Forall2 (V i0) vs1 vs2
              end

          | A0.Vfun f1 ρ1 xs1 e1, A1.Vfun f2 ρ2 xs2 e2 =>
              length xs1 = length xs2 /\
              match K ! f1 with
              | None => (* unknown *)
                  exposed wv2 /\
                  match i with
                  | 0 => True
                  | S i0 =>
                      forall j vs1 vs2 ρ3 ρ4,
                        j <= i0 ->
                        Forall exposed vs2 ->
                        Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                        set_lists xs1 vs1 (M.set f1 (A0.Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
                        set_lists xs2 vs2 (M.set f2 (Tag w2 (A1.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                        E' V true (i0 - (i0 - j)) ρ3 e1 ρ4 e2
                  end
              | Some w1 => (* known *)
                  w1 = w2 /\
                  (~ w1 \in Exposed) /\
                  match i with
                  | 0 => True
                  | S i0 =>
                      forall j vs1 vs2 ρ3 ρ4,
                        j <= i0 ->
                        Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                        set_lists xs1 vs1 (M.set f1 (A0.Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
                        set_lists xs2 vs2 (M.set f2 (Tag w2 (A1.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                        E' V false (i0 - (i0 - j)) ρ3 e1 ρ4 e2
                  end
              end
          | _, _ => False
          end
      end.

    Definition R := (R' V).

    Definition E := (E' V).

    Lemma trans_exp_inv {Γ e e'} :
      trans Γ e e' ->
      (A1.occurs_free e') \subset (A0.occurs_free e).
    Proof.
      unfold Ensembles.Included, Ensembles.In.
      intros H.
      induction H; simpl; intros; auto.
      - inv H1; auto.
      - inv H3; auto.
      - inv H2; auto.
      - inv H4; auto.
      - inv H3; auto.
      - inv H2; auto.
      - inv H2; auto.
      - inv H0; auto.
      - inv H2; auto.
    Qed.

    Lemma trans_exp_weaken {Γ Γ' e e'} :
      trans Γ e e' ->
      Γ \subset Γ' ->
      trans Γ' e e'.
    Proof.
    Admitted.

    Theorem trans_complete :
      forall e,
        exists e',
          trans (A0.occurs_free e) e e'.
    Proof.
    Admitted.

    Lemma Erase_Annotate_id e1 e2 e1' :
      trans (A0.occurs_free e1) e1 e1' ->
      Erase.trans (A1.occurs_free e1') e1' e2 ->
      e1 = e2.
    Proof.
    Admitted.

    (* Lemmas about [wf_val], [wf_res], and [wf_env] *)
    Lemma V_wf_val_r {i v1 v2}:
      V i v1 v2 ->
      wf_val v2.
    Proof.
      intros HV.
      destruct i; simpl in *;
        destruct HV as [Hv2 _]; auto.
    Qed.

    Lemma V_wf_val_Forall_r {i vs1 vs2} :
      Forall2 (V i) vs1 vs2 ->
      Forall wf_val vs2.
    Proof.
      intros.
      induction H; auto.
      constructor; auto.
      eapply V_wf_val_r; eauto.
    Qed.

    Lemma V_wf_res_r {i v1 v2}:
      V i v1 v2 ->
      wf_res (Res v2).
    Proof.
      intros HV.
      constructor.
      eapply V_wf_val_r; eauto.
    Qed.

    Lemma R_wf_res_l {i r1 r2} :
      R i r1 r2 ->
      wf_res r2.
    Proof.
      unfold R.
      intros.
      destruct r1; destruct r2; try contradiction; auto.
      constructor.
      eapply V_wf_val_r; eauto.
    Qed.

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
    Definition G i Γ1 ρ1 Γ2 ρ2 :=
      wf_env ρ2 /\
      forall x,
        (x \in Γ1) ->
        forall v1,
          M.get x ρ1 = Some v1 ->
          ((x \in Γ2) ->
          exists v2,
            M.get x ρ2 = Some v2 /\
            V i v1 v2).

    Definition trans_correct Γ e1 e2 :=
      forall ex i ρ1 ρ2,
        G i Γ ρ1 (A1.occurs_free e2) ρ2 ->
        E ex i ρ1 e1 ρ2 e2.

    (* Environment Lemmas *)
    Lemma G_wf_env_r {i Γ1 ρ1 Γ2 ρ2}:
      G i Γ1 ρ1 Γ2 ρ2 ->
      wf_env ρ2.
    Proof.
      unfold G.
      intros H; destruct H; auto.
    Qed.

    Lemma G_get {Γ1 Γ2 i ρ1 ρ2}:
      G i Γ1 ρ1 Γ2 ρ2 ->
      forall x v1,
        (x \in Γ1) ->
        (x \in Γ2) ->
        M.get x ρ1 = Some v1 ->
        exists v2,
          M.get x ρ2 = Some v2 /\
          V i v1 v2.
    Proof.
      unfold G.
      intros.
      destruct H as [Hr1 HG].
      eapply HG; eauto.
    Qed.

    Lemma G_get_list {i Γ1 ρ1 Γ2 ρ2} :
      G i Γ1 ρ1 Γ2 ρ2 ->
      forall xs vs1,
        (FromList xs) \subset Γ1 ->
        (FromList xs) \subset Γ2 ->
        get_list xs ρ1 = Some vs1 ->
        exists vs2,
          get_list xs ρ2 = Some vs2 /\
          Forall2 (V i) vs1 vs2.
    Proof.
      unfold G.
      intros HG xs.
      induction xs; simpl; intros.
      - inv H1; eauto.
      - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
        destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
        inv H1.
        unfold Ensembles.Included, Ensembles.In, FromList in *.
        edestruct (G_get HG) as [v2 [Heqv2 HV]]; eauto.
        eapply (H a).
        apply in_eq.
        apply H0.
        apply in_eq.
        edestruct IHxs as [vs2 [Heqvs2 Vvs]]; eauto.
        + intros.
          apply H.
          apply in_cons; auto.
        + intros.
          apply H0.
          apply in_cons; auto.
        + rewrite Heqvs2.
          exists (v2 :: vs2); split; auto.
          rewrite Heqv2; auto.
    Qed.

    Lemma G_set {i Γ1 ρ1 Γ2 ρ2}:
      G i Γ1 ρ1 Γ2 ρ2 ->
      forall {x v1 v2},
        V i v1 v2 ->
        G i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
    Proof.
      unfold G.
      intros.

      inv H.
      split.
      eapply wf_env_set; eauto.
      eapply V_wf_val_r; eauto.

      intros.
      destruct (M.elt_eq x0 x); subst.
      - repeat rewrite M.gss in *.
        inv H3.
        eexists; split; eauto; intros.
      - rewrite M.gso in *; auto.
        inv H.
        inv H5; try contradiction.
        inv H4.
        inv H; try contradiction.
        edestruct H2 as [v1' [Heqv1' Hv2]]; eauto.
    Qed.

    Lemma G_set_lists {i Γ1 ρ1 Γ2 ρ2}:
      G i Γ1 ρ1 Γ2 ρ2 ->
      forall {xs vs1 vs2 ρ3 ρ4},
        Forall2 (V i) vs1 vs2 ->
        set_lists xs vs1 ρ1 = Some ρ3 ->
        set_lists xs vs2 ρ2 = Some ρ4 ->
        G i (FromList xs :|: Γ1) ρ3 (FromList xs :|: Γ2) ρ4.
    Proof.
      intros HG xs.
      induction xs; simpl; intros.
      - destruct vs1; try discriminate.
        destruct vs2; try discriminate.
        inv H0; inv H1.
        unfold G.
        split; intros.
        eapply G_wf_env_r; eauto.

        eapply (G_get HG); eauto.
        inv H0; auto.
        inv H3.

        inv H2; auto.
        inv H3.
      - destruct vs1; try discriminate.
        destruct vs2; try discriminate.
        destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
        destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
        inv H; inv H0; inv H1.
        unfold G.

        split.
        eapply wf_env_set; eauto.
        eapply (wf_env_set_lists ρ2) with (xs := xs) (vs := vs2); eauto.

        eapply G_wf_env_r; eauto.
        eapply V_wf_val_Forall_r; eauto.
        eapply V_wf_val_r; eauto.

        intros.
        destruct (M.elt_eq x a); subst.
        + repeat rewrite M.gss in *; eauto.
          inv H0.
          eexists; split; eauto.
        + rewrite M.gso in *; auto.
          eapply IHxs; eauto.
          eapply not_In_cons_Union; eauto.
          eapply not_In_cons_Union; eauto.
    Qed.

    Lemma G_subset Γ1 Γ2 {i ρ1 Γ3 ρ2 Γ4}:
      G i Γ1 ρ1 Γ2 ρ2 ->
      Γ3 \subset Γ1 ->
      Γ4 \subset Γ2 ->
      G i Γ3 ρ1 Γ4 ρ2.
    Proof.
      unfold G.
      intros.
      inv H; split; auto.
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
        destruct j; simpl; intros;
        destruct H0 as [Hv1 HV]; subst.
      - repeat (split; auto).
      - inv H1.
      - repeat (split; auto).
        destruct v1; destruct v; try contradiction.
        + destruct HV.
          destruct (K ! v0) eqn:HeqK.
          * destruct H2 as [Heqw [Hex HV]]; subst.
            repeat (split; eauto).
          * destruct H2 as [Hex HV].
            repeat (split; eauto).
        + destruct HV as [Hex [Hc HV]]; subst.
          repeat split; auto.
          eapply Forall2_length; eauto.
      - repeat (split; auto).
        destruct v1; destruct v; try contradiction;
          destruct HV as [Hlen HV]; subst.
        + destruct (K ! v0) eqn:HeqK.
          * destruct HV as [Heqw [Hex HV]]; subst.
            repeat (split; eauto); intros.
            specialize (HV j0 vs1 vs2 ρ3 ρ4).
            rewrite normalize_step in *; try lia.
            apply HV; eauto; lia.
          * destruct HV as [Hex HV]; subst.
            repeat split; auto; intros.
            specialize (HV j0 vs1 vs2 ρ3 ρ4).
            rewrite normalize_step in *; try lia.
            eapply HV; eauto; lia.
        + destruct HV as [Heqc HV]; subst.
          repeat split; auto.
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

    Lemma E_mono {ex ρ1 ρ2 e1 e2} i j:
      E ex i ρ1 e1 ρ2 e2 ->
      j <= i ->
      E ex j ρ1 e1 ρ2 e2.
    Proof.
      unfold E, R, E', R'.
      intros.
      destruct (H j1 r1) as [j2 [r2 [Hr2 HR]]]; auto; try lia.
      exists j2, r2; split; eauto.
      apply R_mono with (i - j1); try lia; auto.
    Qed.

    Lemma G_mono {Γ1 Γ2 ρ1 ρ2} i j:
      G i Γ1 ρ1 Γ2 ρ2 ->
      j <= i ->
      G j Γ1 ρ1 Γ2 ρ2.
    Proof.
      unfold G.
      intros.
      inv H.
      split; auto; intros.
      edestruct H2 as [v2 [Heqv2 HV]]; eauto.
      eexists; eexists; repeat split; eauto.
      apply V_mono with i; eauto.
    Qed.

    (* Fundamental Property *)
    Lemma fundamental_property {Γ e e'}:
      trans Γ e e' -> trans_correct Γ e e'.
    Proof.
      intros H.
      induction H.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
    Admitted.

    (* Top Level *)
    Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
      wf_env ρ2 /\
      Γ2 \subset Γ1 /\
      forall x,
        (x \in Γ1) ->
        exists v1 v2,
          M.get x ρ1 = Some v1 /\
          M.get x ρ2 = Some v2 /\
          exposed v2 /\
          V i v1 v2.

    Lemma G_top_wf_env_r i Γ1 ρ1 Γ2 ρ2 :
      G_top i Γ1 ρ1 Γ2 ρ2 ->
      wf_env ρ2.
    Proof.
      unfold G_top.
      intros; tauto.
    Qed.

    Lemma G_top_subset i Γ1 ρ1 Γ2 ρ2 Γ3 Γ4 :
      G_top i Γ1 ρ1 Γ2 ρ2 ->
      Γ3 \subset Γ1 ->
      Γ4 \subset Γ3 ->
      G_top i Γ3 ρ1 Γ4 ρ2.
    Proof.
      unfold G_top.
      intros.
      destruct H as [Hr [Hs HG]].
      repeat (split; auto).
    Qed.

    Lemma G_top_G : forall {i Γ1 ρ1 Γ2 ρ2},
        G_top i Γ1 ρ1 Γ2 ρ2 ->
        G i Γ1 ρ1 Γ2 ρ2.
    Proof.
      unfold G_top, G.
      intros.
      destruct H as [HΓ [Hρ HG]].
      unfold Ensembles.Included, Ensembles.In, Dom_map in *.
      split; auto; intros.
      edestruct HG as [v1' [v2 [Heqv1 [Heqv2 [Hex HV]]]]]; eauto.
      rewrite Heqv1 in H0; inv H0; eauto.
    Qed.

  End Spec.

  Definition trans_correct_top etop etop' :=
    A1.occurs_free etop' \subset A0.occurs_free etop /\
    forall i ρ1 ρ2,
      let K := analyze etop in
      G_top K i (A0.occurs_free etop) ρ1 (A1.occurs_free etop') ρ2 ->
      E K true i ρ1 etop ρ2 etop'.

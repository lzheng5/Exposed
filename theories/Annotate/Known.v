From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From LambdaANF Require Import ANF.
From LambdaWeb Require Import ANF UniqueExposed Erase.
From Annotate Require Import Annotate.

(* Known Function Analysis With A Single Exposed Web Id *)

(* Outline: *)
(* 1. run `analyze` to build `K : known_map` for every function identifiers (assume unique names) in the program with nonexposed web ids (Note it is not necessary to require them to be distinct though) *)
(* 2. follow `escaping_fun_exp` as in CertiCoq [https://github.com/CertiCoq/certicoq/blob/master/theories/LambdaANF/dead_param_elim.v] to filter `K` so that its domain satisfies `known_fun` *)
(* 3. rewrite based on `K` *)

(* Step 3 is the main step we are establishing here *)

Module A0 := LambdaANF.ANF.
Module A1 := LambdaWeb.ANF.

Definition known_map := M.t web.

Parameter analyze : A0.exp -> known_map.

(* Specification for the *result* of `analyze`, or `K` *)
(* Similar to CertiCoq's `Known_exp` [https://github.com/CertiCoq/certicoq/blob/master/theories/LambdaANF/dead_param_elim_util.v] *)
Inductive known_fun (S : Ensemble var) : A0.exp -> Prop :=
| Known_Ret :
  forall x,
    (~ x \in S) ->
    known_fun S (A0.Eret x)

| Known_App :
  forall f ys,
    Disjoint _ (FromList ys) S ->
    known_fun S (A0.Eapp f ys)

| Known_LetApp :
  forall x f ys e,
    (~ x \in S) -> (* intermediate result shouldn't be known fun *)
    Disjoint _ (FromList ys) S ->
    known_fun S e ->
    known_fun S (A0.Eletapp x f ys e)

| Known_Fun:
  forall f xs e k,
    Disjoint _ (FromList xs) S ->
    known_fun S e ->
    known_fun S k ->
    known_fun S (A0.Efun f xs e k)

| Known_Constr :
  forall x ys ct e,
    (~ x \in S) -> (* constructors are not known functions, but they can still be known exp *)
    Disjoint _ (FromList ys) S ->
    known_fun S e ->
    known_fun S (A0.Econstr x ct ys e)

| Known_Proj :
  forall x n y e,
    (~ x \in S) ->
    (~ y \in S) ->
    known_fun S e ->
    known_fun S (A0.Eproj x n y e)

| Known_Case_nil:
  forall x,
    (~ x \in S) ->
    known_fun S (A0.Ecase x [])

| Known_Case_hd:
  forall x c e ce,
    (~ x \in S) ->
    known_fun S e ->
    known_fun S (A0.Ecase x ce) ->
    known_fun S (A0.Ecase x ((c, e) :: ce)).

Hint Constructors known_fun : core.

Definition known_map_inv K :=
  forall f w,
    K ! f = Some w ->
    ~ (w \in Exposed).

Definition analysis_spec (K : known_map) e :=
  known_fun (Dom_map K) e.

Definition analyze_spec K e :=
  analysis_spec K e /\
    known_map_inv K /\
    Disjoint _ (A0.occurs_free e) (Dom_map K).

Parameter analyze_sound :
  forall (e : A0.exp),
    analyze_spec (analyze e) e.

Section Trans.

  Variable K : known_map.

  (* Specification based on `known_fun` but incorporate unknown cases *)
  Inductive trans (Γ : vars) : A0.exp -> A1.exp -> Prop :=
  | Trans_ret :
    forall x,
      K ! x = None ->
      (x \in Γ) ->
      trans Γ (A0.Eret x) (A1.Eret x)

  | Trans_fun_known :
    forall {f w xs e k e' k'},
      K ! f = Some w ->
      (~ w \in Exposed) ->
      Disjoint _ (FromList xs) (Dom_map K) ->

      trans (FromList xs :|: (f |: Γ)) e e' ->
      trans (f |: Γ) k k' ->
      trans Γ (A0.Efun f xs e k) (A1.Efun f w xs e' k')

  | Trans_fun_unknown :
    forall {f xs e k e' k'},
      K ! f = None ->
      Disjoint _ (FromList xs) (Dom_map K) ->

      trans (FromList xs :|: (f |: Γ)) e e' ->
      trans (f |: Γ) k k' ->
      trans Γ (A0.Efun f xs e k) (A1.Efun f w0 xs e' k')

  | Trans_app_known :
    forall {f w xs},
      K ! f = Some w ->
      (~ w \in Exposed) ->
      Disjoint _ (FromList xs) (Dom_map K) ->

      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans Γ (A0.Eapp f xs) (A1.Eapp f w xs)

  | Trans_app_unknown :
    forall {f xs},
      K ! f = None ->
      Disjoint _ (FromList xs) (Dom_map K) ->

      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans Γ (A0.Eapp f xs) (A1.Eapp f w0 xs)

  | Trans_letapp_known :
    forall {x f w xs k k'},
      K ! f = Some w ->
      (~ w \in Exposed) ->
      Disjoint _ (FromList xs) (Dom_map K) ->
      K ! x = None ->

      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w xs k')

  | Trans_letapp_unknown :
    forall {x f xs k k'},
      K ! f = None ->
      Disjoint _ (FromList xs) (Dom_map K) ->
      K ! x = None ->

      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w0 xs k')

  (* data webs are all exposed *)

  | Trans_constr :
    forall {x t xs k k'},
      K ! x = None ->
      Disjoint _ (FromList xs) (Dom_map K) ->

      (FromList xs \subset Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (A0.Econstr x t xs k) (A1.Econstr x w0 t xs k')

  | Trans_proj :
    forall {x y k k' n},
      K ! x = None ->
      K ! y = None ->

      (y \in Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (A0.Eproj x n y k) (A1.Eproj x w0 n y k')

  | Trans_case_nil :
    forall {x},
      K ! x = None ->
      (x \in Γ) ->
      trans Γ (A0.Ecase x []) (A1.Ecase x w0 [])

  | Trans_case_cons :
    forall {x e e' t cl cl'},
      K ! x = None ->
      (x \in Γ) ->
      trans Γ e e' ->
      trans Γ (A0.Ecase x cl) (A1.Ecase x w0 cl') ->
      trans Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x w0 ((t, e') :: cl')).

  Hint Constructors trans : core.

  Lemma known_fun_trans e :
    known_map_inv K ->
    known_fun (Dom_map K) e ->
    forall Γ,
      (A0.occurs_free e) \subset Γ ->
      exists e', trans Γ e e'.
  Proof.
    unfold known_map_inv.
    intros HK H.
    induction H; simpl; intros.
    - exists (A1.Eret x); auto.
    - destruct (K ! f) eqn:HKf.
      + exists (A1.Eapp f w ys); econstructor; eauto.
        eapply A0.free_app_xs_inv; eauto.
      + exists (A1.Eapp f w0 ys); eapply Trans_app_unknown; eauto.
        eapply A0.free_app_xs_inv; eauto.
    - destruct (IHknown_fun (x |: Γ)) as [e' He']; auto.
      eapply A0.free_letapp_k_inv; eauto.
      destruct (K ! f) eqn:HKf.
      + exists (A1.Eletapp x f w ys e'); econstructor; eauto.
        eapply A0.free_letapp_xs_inv; eauto.
      + exists (A1.Eletapp x f w0 ys e'); eapply Trans_letapp_unknown; eauto.
        eapply A0.free_letapp_xs_inv; eauto.
    - destruct (IHknown_fun1 (FromList xs :|: (f |: Γ))) as [e' He']; auto.
      eapply A0.free_fun_e_inv; eauto.
      destruct (IHknown_fun2 (f |: Γ)) as [k' Hk']; auto.
      eapply A0.free_fun_k_inv; eauto.
      destruct (K ! f) eqn:Hkf.
      + exists (A1.Efun f w xs e' k'); econstructor; eauto.
      + exists (A1.Efun f w0 xs e' k'); eapply Trans_fun_unknown; eauto.
    - destruct (IHknown_fun (x |: Γ)) as [e' He']; auto.
      eapply A0.free_constr_k_inv; eauto.
      exists (A1.Econstr x w0 ct ys e'); econstructor; eauto.
      eapply A0.free_constr_xs_inv; eauto.
    - destruct (IHknown_fun (x |: Γ)) as [e' He']; auto.
      eapply A0.free_proj_k_inv; eauto.
      exists (A1.Eproj x w0 n y e'); econstructor; eauto.
    - exists (A1.Ecase x w0 []); econstructor; eauto.
    - destruct (IHknown_fun1 Γ) as [e' He']; auto.
      eapply A0.free_case_hd_inv; eauto.
      destruct (IHknown_fun2 Γ) as [c' Hc']; auto.
      eapply A0.free_case_tl_inv; eauto.
      inv Hc'.
      + exists (A1.Ecase x w0 [(c, e')]); econstructor; eauto.
      + exists (A1.Ecase x w0 ((c, e') :: (t, e'0) :: cl')); econstructor; eauto.
  Qed.

  Theorem trans_total e :
    known_map_inv K ->
    analysis_spec K e ->
    exists e', trans (A0.occurs_free e) e e'.
  Proof.
    intros.
    eapply known_fun_trans; eauto.
    apply Included_refl.
  Qed.

  Lemma trans_exp_inv {Γ e e'} :
    trans Γ e e' ->
    (A1.occurs_free e') \subset (A0.occurs_free e).
  Proof.
    unfold Ensembles.Included, Ensembles.In.
    intros H.
    induction H; simpl; intros; auto.
    - inv H1; auto.
    - inv H4; auto.
    - inv H3; auto.
    - inv H4; auto.
    - inv H3; auto.
    - inv H6; auto.
    - inv H5; auto.
    - inv H3; auto.
    - inv H3; auto.
    - inv H1; auto.
    - inv H3; auto.
  Qed.

  Theorem trans_erase e1 e2 e1' :
    trans (A0.occurs_free e1) e1 e1' ->
    Erase.trans (A1.occurs_free e1') e1' e2 ->
    e1 = e2.
  Proof.
    intro H.
    revert e2.
    induction H; simpl; intros.
    - inv H1; auto.
    - inv H4; auto.
      erewrite IHtrans1 with (e2 := e'0); eauto.
      + erewrite IHtrans2 with (e2 := k'0); eauto.
        eapply Erase.trans_exp_strengthen; eauto.
        eapply A1.free_fun_k_subset; eauto.
      + eapply Erase.trans_exp_strengthen; eauto.
        eapply A1.free_fun_e_subset; eauto.
    - inv H3; auto.
      erewrite IHtrans1 with (e2 := e'0); eauto.
      + erewrite IHtrans2 with (e2 := k'0); eauto.
        eapply Erase.trans_exp_strengthen; eauto.
        eapply A1.free_fun_k_subset; eauto.
      + eapply Erase.trans_exp_strengthen; eauto.
        eapply A1.free_fun_e_subset; eauto.
    - inv H4; auto.
    - inv H3; auto.
    - inv H6; auto.
      erewrite IHtrans with (e2 := k'0); eauto.
      eapply Erase.trans_exp_strengthen; eauto.
      eapply A1.free_letapp_k_subset; eauto.
    - inv H5; auto.
      erewrite IHtrans with (e2 := k'0); eauto.
      eapply Erase.trans_exp_strengthen; eauto.
      eapply A1.free_letapp_k_subset; eauto.
    - inv H3; auto.
      erewrite IHtrans with (e2 := k'0); eauto.
      eapply Erase.trans_exp_strengthen; eauto.
      eapply A1.free_constr_k_subset; eauto.
    - inv H3; auto.
      erewrite IHtrans with (e2 := k'0); eauto.
      eapply Erase.trans_exp_strengthen; eauto.
      eapply A1.free_proj_k_subset; eauto.
    - inv H1; auto.
    - inv H3; auto.
      erewrite IHtrans1 with (e2 := e'0); eauto.
      assert (A0.Ecase x cl = A0.Ecase x cl'0).
      {
        erewrite IHtrans2 with (e2 := (A0.Ecase x cl'0)); eauto.
        eapply Erase.trans_exp_strengthen; eauto.
        eapply A1.free_case_tl_subset; eauto.
      }
      inv H3; auto.
      eapply Erase.trans_exp_strengthen; eauto.
      eapply A1.free_case_hd_subset; eauto.
  Qed.

End Trans.

(* Cross-language Logical Relations *)

Module VKnownM <: VAnn.

  Definition web_map := known_map.

  Definition V_ann0
    (K : web_map) (v1 : A0.val) (w2 : web) (v2 : A1.val) : Prop :=
    match v1, v2 with
    | A0.Vconstr c1 vs1, A1.Vconstr c2 vs2 => exposed (Tag w2 v2) /\ c1 = c2 /\ length vs1 = length vs2

    | A0.Vfun f1 ρ1 xs1 e1, A1.Vfun f2 ρ2 xs2 e2 => length xs1 = length xs2 /\ f1 = f2 /\ K ! f1 = Some w2

    | _, _ => False
    end.

  Definition V_ann
    (V' : nat -> A0.val -> A1.wval -> Prop)
    (E' : bool -> nat -> A0.env -> A0.exp -> A1.env -> A1.exp -> Prop)
    (K : web_map) (i0 : nat) (v1 : A0.val) (w2 : web) (v2 : A1.val) :=
    match v1, v2 with
    | A0.Vconstr c1 vs1, A1.Vconstr c2 vs2 =>
        (* data constructors are all exposed *)
        exposed (Tag w2 v2) /\
        c1 = c2 /\
        Forall2 (V' i0) vs1 vs2

    | A0.Vfun f1 ρ1 xs1 e1, A1.Vfun f2 ρ2 xs2 e2 => (* known *)
        (* note function arguments and result are always exposed regardless of whether a function is known or unknown *)
        length xs1 = length xs2 /\
        f1 = f2 /\
        K ! f1 = Some w2 /\
        forall j vs1 vs2 ρ3 ρ4,
          j <= i0 ->
          Forall exposed vs2 ->
          Forall2 (V' j) vs1 vs2 ->
          set_lists xs1 vs1 (M.set f1 (A0.Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
          set_lists xs2 vs2 (M.set f2 (Tag w2 (A1.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
          E' true j ρ3 e1 ρ4 e2

    | _, _ => False
    end.

    Lemma V_ann_V_ann0 :
      forall V E W i v1 w2 v2,
        V_ann V E W i v1 w2 v2 ->
        V_ann0 W v1 w2 v2.
    Proof.
      unfold V_ann, V_ann0.
      intros.
      destruct v1; destruct v2; try contradiction.
      - fcrush.
      - destruct H as [Hex [Heqc HVs]]; subst.
        repeat (split; eauto).
        eapply Forall2_length; eauto.
    Qed.

    Lemma V_ann_mono V E W i j v1 w2 v2 :
      (forall k : nat,
          k < S i ->
          forall (j : nat) (v1 : A0.val) (v2 : A1.wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
      V_ann (fun i' => V (i - (i - i'))) (fun b i' => E b (i - (i - i'))) W i v1 w2 v2 ->
      j <= i ->
      V_ann (fun j' => V (j - (j - j'))) (fun b j' => E b (j - (j - j'))) W j v1 w2 v2.
    Proof.
      unfold V_ann. intros.
      intros.
      destruct v1; destruct v2; try contradiction.
      - destruct H0 as [Hlen [Heqv [HWv HV]]]; subst.
        repeat (split; eauto); intros.
        specialize (HV j0 vs1 vs2 ρ3 ρ4).
        rewrite normalize_step in *; try lia.
        eapply HV; eauto; lia.
      - destruct H0 as [Hex [Heqc HVs]]; subst.
        repeat (split; eauto).
        rewrite normalize_step in *; try lia.
        eapply V_mono_Forall_aux; eauto.
    Qed.

End VKnownM.

Module VM := AnnotateV VKnownM.
Import VM.

Section Compat.
  (* Note we allow the following definitions to be customizable
     depending on the invariants we want to enforce. *)

  Variable K : known_map.

  (* Environment Relation *)
  Definition same_id x wv2 :=
    match wv2 with
    | A1.TAG _ w2 v2 =>
        match v2 with
        | A1.Vfun f2 ρ2 xs2 e2 => f2 = x
        | A1.Vconstr c2 vs2 => True
        end
    end.

  Lemma same_id_fun f w f1 t l e:
    same_id f (TAG val w (Vfun f1 t l e)) -> f1 = f.
  Proof. unfold same_id; simpl; auto. Qed.

  Definition binding_inv x v :=
    match K ! x with
    | Some w => same_id x v /\ ~ exposed v
    | None => exposed v
    end.

  Lemma binding_inv_exposed x v :
    (K ! x = None) ->
    exposed v ->
    binding_inv x v.
  Proof.
    unfold binding_inv.
    fcrush.
  Qed.

  Lemma binding_inv_exposed_Forall xs :
    forall vs,
      Disjoint _ (FromList xs) (Dom_map K) ->
      length xs = length vs ->
      Forall exposed vs ->
      Forall2 binding_inv xs vs.
  Proof.
    induction xs; simpl; intros;
      destruct vs; try discriminate; auto.
    inv H1.
    apply Disjoint_FromList_cons_inv in H.
    inv H.
    constructor; auto.
    apply binding_inv_exposed; auto.
  Qed.

  Lemma binding_inv_known_fun f w ρ xs e :
    K ! f = Some w ->
    ~ (w \in Exposed) ->
    binding_inv f (Tag w (A1.Vfun f ρ xs e)).
  Proof.
    unfold binding_inv.
    intros.
    fcrush.
  Qed.

  Definition G i Γ1 ρ1 Γ2 ρ2 :=
    wf_env ρ2 /\
      forall x,
        (x \in Γ1) ->
        forall v1,
          M.get x ρ1 = Some v1 ->
          ((x \in Γ2) ->
           exists v2,
             M.get x ρ2 = Some v2 /\
             binding_inv x v2 /\
             V K i v1 v2).

  (* Transformation Relation *)
  Definition trans_correct Γ e1 e2 :=
    forall i ρ1 ρ2,
      known_map_inv K ->
      G i Γ ρ1 (A1.occurs_free e2) ρ2 ->
      E K true i ρ1 e1 ρ2 e2.

  (* Environment Lemmas *)
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
          binding_inv x v2 /\
          V K i v1 v2.
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
      Disjoint _ (FromList xs) (Dom_map K) ->
      get_list xs ρ1 = Some vs1 ->
      exists vs2,
        get_list xs ρ2 = Some vs2 /\
        Forall exposed vs2 /\
        Forall2 (V K i) vs1 vs2.
  Proof.
    intros HG xs.
    induction xs; simpl; intros.
    - inv H2; eauto.
    - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
      destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
      inv H2.
      unfold Ensembles.Included, Ensembles.In in *.
      edestruct (G_get HG) as [v2 [Heqv2 [Hbinv HV]]]; eauto.
      eapply (H a).
      apply in_eq.
      apply H0.
      apply in_eq.
      edestruct IHxs as [vs2 [Heqvs2 [Hexvs2 Vvs]]]; eauto.
      + intros.
        apply H.
        apply in_cons; auto.
      + intros.
        apply H0.
        apply in_cons; auto.
      + eapply Disjoint_FromList_cons_l; eauto.
      + rewrite Heqvs2.
        exists (v2 :: vs2); split; auto.
        rewrite Heqv2; auto.
        split; auto.
        constructor; auto.
        apply Disjoint_FromList_cons_inv in H1.
        inv H1.
        apply not_Dom_map_eq in H2; auto.
        unfold binding_inv in *.
        fcrush.
  Qed.

  Lemma G_set {i Γ1 ρ1 Γ2 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall {x v1 v2},
      V K i v1 v2 ->
      binding_inv x v2 ->
      G i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
  Proof.
    intro HG.
    pose proof HG as HG'.
    unfold G in HG.
    intros.

    inv HG.
    split.
    eapply wf_env_set; eauto.
    eapply V_wf_val_r; eauto.

    intros.
    destruct (M.elt_eq x0 x); subst.
    - repeat rewrite M.gss in *.
      inv H4.
      eexists; repeat (split; intros; eauto).
    - rewrite M.gso in *; auto.
      eapply G_get; eauto.

      inv H3; auto.
      inv H6; try contradiction; auto.
      inv H5; auto.
      inv H6; try contradiction; auto.
  Qed.

  Lemma G_set_lists {i Γ1 ρ1 Γ2 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall {xs vs1 vs2 ρ3 ρ4},
      Forall2 (V K i) vs1 vs2 ->
      Forall2 binding_inv xs vs2 ->
      set_lists xs vs1 ρ1 = Some ρ3 ->
      set_lists xs vs2 ρ2 = Some ρ4 ->
      G i (FromList xs :|: Γ1) ρ3 (FromList xs :|: Γ2) ρ4.
  Proof.
    intros HG xs.
    induction xs; simpl; intros.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      inv H1; inv H2.
      eapply G_subset; eauto; normalize_sets;
        rewrite Union_Empty_set_neut_l; eauto;
        apply Included_refl.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
      destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
      inv H; inv H0; inv H1; inv H2.
      eapply G_subset with (Γ1 := (a |: (FromList xs :|: Γ1))) (Γ2 := (a |: (FromList xs :|: Γ2))); eauto;
        try (normalize_sets;
             rewrite Union_assoc;
             apply Included_refl).
      eapply G_set; eauto.
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
    edestruct H2 as [v2 [Heqv2 [Hbinv HV]]]; eauto.
    eexists; eexists; repeat split; eauto.
    apply V_mono with i; eauto.
  Qed.

  (* Compatibility Lemmas *)
  Lemma ret_compat Γ x :
    (x \in Γ) ->
    K ! x = None ->
    trans_correct Γ (A0.Eret x) (A1.Eret x).
  Proof.
    unfold trans_correct, E, E', R, R', Ensembles.Included, Ensembles.In, Dom_map.
    intros; simpl.
    inv H4.
    - exists 0, A1.OOT; split; auto.
    - inv H5.
      edestruct (G_get H2) as [v2 [Heqv2 [Hbinv HV]]]; eauto.
      unfold binding_inv in *.
      rewrite H0 in Hbinv.
      exists 1, (A1.Res v2); split; simpl; eauto.
      apply V_mono with i; try lia; auto.
  Qed.

  Lemma Vfun_V_known Γ1 f w xs e e' :
    known_map_inv K ->
    K ! f = Some w ->
    Disjoint _ (FromList xs) (Dom_map K) ->
    trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
    forall {i Γ2 ρ1 ρ2},
      wf_env ρ2 ->
      G i Γ1 ρ1 Γ2 ρ2 ->
      A1.occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
      V K i (A0.Vfun f ρ1 xs e) (Tag w (A1.Vfun f ρ2 xs e')).
  Proof.
    unfold trans_correct.
    intros HK HKf HKxs He i.
    assert (~ Ensembles.In web Exposed w) by (eapply HK; eauto).
    assert (exposedb w = false) by (destruct (exposed_reflect w); try contradiction; auto).
    induction i; simpl; intros; auto;
      repeat (split; auto);
      rewrite H0; intros; (repeat split; auto);
      intros.

    apply (He (i - (i - j)) ρ3 ρ4); auto.
    - eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))); eauto.
      eapply G_set_lists; eauto.
      eapply G_set; eauto.
      + eapply G_mono; eauto; lia.
      + eapply V_mono with i; try lia.
        eapply IHi with (Γ2 := Γ2); eauto.
        eapply G_mono; eauto; lia.
      + eapply binding_inv_known_fun; eauto.
      + eapply binding_inv_exposed_Forall; eauto.
        eapply set_lists_length_eq; eauto.
      + apply Included_refl.
  Qed.

  Lemma fun_known_compat Γ e e' k k' f w xs :
    K ! f = Some w ->
    Disjoint _ (FromList xs) (Dom_map K) ->

    trans_correct (FromList xs :|: (f |: Γ)) e e' ->
    trans_correct (f |: Γ) k k' ->
    trans_correct Γ (A0.Efun f xs e k) (A1.Efun f w xs e' k').
  Proof.
    unfold trans_correct, E, E'.
    intros HKf HKxs.
    intros.
    inv H4.
    - exists 0, A1.OOT; split; simpl; eauto.
    - inv H5.
      edestruct (H0 (i - 1) (M.set f (A0.Vfun f ρ1 xs e) ρ1) (M.set f (Tag w (A1.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + eapply G_subset with (Γ2 := (f |: A1.occurs_free (A1.Efun f w xs e' k'))).
        eapply G_set; eauto.
        eapply G_mono; eauto; lia.
        * eapply Vfun_V_known; eauto.
          -- eapply G_wf_env_r; eauto.
          -- eapply G_mono; eauto; lia.
          -- apply A1.free_fun_e_subset.
        * eapply binding_inv_known_fun; eauto.
        * apply Included_refl.
        * apply A1.free_fun_k_subset.
      + exists (S j2), r2; split; auto.
        * constructor; simpl; auto.
          eapply bstep_fuel_exposed_inv; eauto.
        * eapply R_mono; eauto; lia.
  Qed.

  Lemma Vfun_V_unknown Γ1 f xs e e' :
    known_map_inv K ->
    K ! f = None ->
    Disjoint _ (FromList xs) (Dom_map K) ->
    trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
    forall {i Γ2 ρ1 ρ2},
      wf_env ρ2 ->
      G i Γ1 ρ1 Γ2 ρ2 ->
      A1.occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
      V K i (A0.Vfun f ρ1 xs e) (Tag w0 (A1.Vfun f ρ2 xs e')).
  Proof.
    unfold trans_correct.
    intros HK HKf HKxs He i.

    induction i; simpl; intros; auto;
      repeat (split; auto);
      rewrite w0_exposedb;
      repeat (split; auto);
      try (constructor; apply w0_exposed);
      intros.

    apply (He (i - (i - j)) ρ3 ρ4); auto.
    - eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))); eauto.
      eapply G_set_lists; eauto.
      eapply G_set; eauto.
      + eapply G_mono; eauto; lia.
      + apply V_mono with i; try lia.
        eapply IHi with (Γ2 := Γ2); eauto.
        eapply G_mono; eauto; lia.
      + eapply binding_inv_exposed; eauto.
        constructor; apply w0_exposed.
      + eapply binding_inv_exposed_Forall; eauto.
        eapply set_lists_length_eq; eauto.
      + apply Included_refl.
  Qed.

  Lemma fun_unknown_compat Γ e e' k k' f xs :
    K ! f = None ->
    Disjoint _ (FromList xs) (Dom_map K) ->

    trans_correct (FromList xs :|: (f |: Γ)) e e' ->
    trans_correct (f |: Γ) k k' ->
    trans_correct Γ (A0.Efun f xs e k) (A1.Efun f w0 xs e' k').
  Proof.
    unfold trans_correct, E, E'.
    intros HKf HKxs.
    intros.
    inv H4.
    - exists 0, A1.OOT; split; simpl; eauto.
    - inv H5.
      edestruct (H0 (i - 1) (M.set f (A0.Vfun f ρ1 xs e) ρ1) (M.set f (Tag w0 (A1.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + eapply G_subset with (Γ2 := (f |: A1.occurs_free (A1.Efun f w0 xs e' k'))).
        eapply G_set; eauto.
        apply G_mono with i; eauto; lia.
        * eapply Vfun_V_unknown; eauto.
          -- eapply G_wf_env_r; eauto.
          -- eapply G_mono; eauto; lia.
          -- apply A1.free_fun_e_subset.
        * eapply binding_inv_exposed; eauto.
          constructor; apply w0_exposed.
        * apply Included_refl.
        * apply A1.free_fun_k_subset.
      + exists (S j2), r2; split; auto.
        * constructor; simpl; auto.
          eapply bstep_fuel_exposed_inv; eauto.
        * eapply R_mono; eauto; lia.
  Qed.

  Lemma app_known_compat Γ xs f w :
    (K ! f = Some w) ->
    (~ w \in Exposed) ->
    Disjoint _ (FromList xs) (Dom_map K) ->

    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct Γ (A0.Eapp f xs) (A1.Eapp f w xs).
  Proof.
    unfold trans_correct, E, E'.
    intros HKf Hw HKxs.
    intros; simpl.

    inv H4.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv H5.
      edestruct (G_get H2 f) as [fv2 [Heqfv2 [Hbinv HV]]]; eauto.
      destruct i.
      inv H3.
      destruct fv2; simpl in HV;
        destruct HV as [Hv1 HV].
      unfold binding_inv in *.
      rewrite HKf in Hbinv.
      inv Hbinv.
      destruct (exposed_reflect w0).
      exfalso; fcrush.

      destruct v; try contradiction.
      apply same_id_fun in H4; subst.

      destruct HV as [Hlen [Heqf [Hex HV]]]; subst.
      invc.

      edestruct (G_get_list H2 xs vs) as [vs2 [Heqvs2 [Hexvs Vvs]]]; eauto.
      eapply A1.free_app_xs_subset; eauto.

      destruct (set_lists_length3 (M.set f (Tag w0 (A1.Vfun f t l e0)) t) l vs2) as [ρ4 Heqρ4].
      unfold wval in *.
      rewrite <- (Forall2_length _ _ _ Vvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H9); auto.

      assert (HE : E K true (i - (i - i)) ρ'' e ρ4 e0).
      {
        eapply (HV i vs vs2); eauto.
        apply V_mono_Forall with (S i); auto; lia.
      }

      apply (E_mono _ i) in HE; try lia.
      unfold E in HE.
      destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
      exists (S j2), r2; split; eauto.
      constructor; auto.
      + econstructor; eauto.
        destruct (exposed_reflect w0); try contradiction; auto.
        * pose proof He0 as Hr2.
          apply bstep_fuel_exposed_inv in Hr2.
          eapply bstep_fuel_exposed; eauto.
        * intros; contradiction.
      + eapply bstep_fuel_exposed_inv; eauto.
  Qed.

  Lemma app_unknown_compat Γ xs f :
    (K ! f = None) ->
    Disjoint _ (FromList xs) (Dom_map K) ->

    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct Γ (A0.Eapp f xs) (A1.Eapp f w0 xs).
  Proof.
    unfold trans_correct, E, E'.
    intros HKf HKxs.
    intros.
    inv H4.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv H5.
      edestruct (G_get H2 f) as [fv2 [Heqfv2 [Hbinv HV]]]; eauto.
      destruct i.
      inv H3.
      destruct fv2; simpl in HV;
        destruct HV as [Hv1 HV].
      unfold binding_inv in *.
      rewrite HKf in Hbinv.
      destruct (exposed_reflect w); try contradiction.
      2 : { inv Hbinv; fcrush. }
      destruct v; try contradiction.
      2 : { fcrush. }

      destruct HV as [Hex [Hlen HV]]; subst.

      assert (Hw : w = w0) by (apply Exposed_singleton; eauto); subst.

      edestruct (G_get_list H2 xs vs) as [vs2 [Heqvs2 [Hexvs Vvs]]]; eauto.
      eapply A1.free_app_xs_subset; eauto.

      destruct (set_lists_length3 (M.set v (Tag w0 (A1.Vfun v t l e0)) t) l vs2) as [ρ4 Heqρ4].
      unfold wval in *.
      rewrite <- (Forall2_length _ _ _ Vvs).
      rewrite <- (set_lists_length_eq _ _ _ _ H9); auto.

      assert (HE : E K true (i - (i - i)) ρ'' e ρ4 e0).
      {
        eapply (HV i vs vs2); eauto.
        apply V_mono_Forall with (S i); auto; lia.
      }

      apply (E_mono _ i) in HE; try lia.
      unfold E, E' in HE.
      destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
      assert (exposed_res r2) by (eapply bstep_fuel_exposed_inv; eauto).
      exists (S j2), r2; split; eauto; simpl.
      constructor; auto.
      econstructor; eauto.
      destruct (exposed_reflect w0); try contradiction; auto.
  Qed.

  Lemma letapp_known_compat Γ k k' xs x w f :
    K ! f = Some w ->
    (~ w \in Exposed) ->
    Disjoint _ (FromList xs) (Dom_map K) ->
    K ! x = None ->

    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct (x |: Γ) k k' ->
    trans_correct Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w xs k').
  Proof.
    intros HKf Hw HKxs HKx.
    intros.
    specialize (app_known_compat Γ xs f w HKf Hw HKxs H H0); intros Ha.
    unfold trans_correct, E, E' in *.
    intros.

    assert (HG' : G i Γ ρ1 (occurs_free (A1.Eapp f w xs)) ρ2).
    {
      eapply G_subset with (Γ2 := (occurs_free (A1.Eletapp x f w xs k'))); eauto.
      apply Included_refl.
      eapply free_app_letapp; eauto.
    }

    inv H5.
    - exists 0, OOT; split; simpl; auto.
    - inv H6.
      + destruct (Ha i ρ1 ρ2) with (j1 := (S c0)) (r1 := (A0.Res v)) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
        * simpl in HR.
          destruct r2; try contradiction.
          rename w0 into v0.
          inv Hr1.

          edestruct (H1 (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
          -- eapply G_subset with (Γ2 := (x |: (A1.occurs_free (A1.Eletapp x f w xs k')))).
             eapply G_set; eauto.
             apply G_mono with i; try lia; eauto.
             eapply binding_inv_exposed; eauto.
             inv H6; auto.
             apply Included_refl.
             apply free_letapp_k_subset.
          -- exists ((S c) + j2), r2; split.
             ++ inv H5.
                rewrite_math ((S c + j2) = S (c + j2)).
                constructor; auto.
                ** eapply BStep_letapp_Res; eauto.
                   intros.
                   destruct H21; auto.
                   inv H8.
                   split; auto.
                ** eapply bstep_fuel_exposed_inv; eauto.
             ++ apply R_mono with (i - S c0 - c'); try lia; auto.
      + eexists; eexists; repeat split; eauto.
        simpl; auto.
  Qed.

  Lemma letapp_unknown_compat Γ k k' xs x f :
    K ! f = None ->
    Disjoint _ (FromList xs) (Dom_map K) ->
    K ! x = None ->

    (f \in Γ) ->
    (FromList xs \subset Γ) ->
    trans_correct (x |: Γ) k k' ->
    trans_correct Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w0 xs k').
  Proof.
    intros HKf HKxs HKx.
    intros.
    specialize (app_unknown_compat Γ xs f HKf HKxs H H0); intros Ha.
    unfold trans_correct, E, E' in *.
    intros.

    assert (HG' : G i Γ ρ1 (occurs_free (A1.Eapp f w0 xs)) ρ2).
    {
      eapply G_subset with (Γ2 := (occurs_free (A1.Eletapp x f w0 xs k'))); eauto.
      apply Included_refl.
      eapply free_app_letapp; eauto.
    }

    inv H5.
    - exists 0, OOT; split; simpl; auto.
    - inv H6.
      + destruct (Ha i ρ1 ρ2) with (j1 := (S c0)) (r1 := (A0.Res v)) as [j2 [r2 [Hr1 HR]]]; try lia; eauto.
        * simpl in HR.
          destruct r2; try contradiction.
          rename w into v0.
          inv Hr1.

          edestruct (H1 (i - (S c0)) (M.set x v ρ1) (M.set x v0 ρ2)) with (j1 := c') as [j2 [r2 [Hk Rr]]]; eauto; try lia.
          -- eapply G_subset with (Γ2 := (x |: (A1.occurs_free (A1.Eletapp x f w0 xs k')))).
             eapply G_set; eauto.
             apply G_mono with i; try lia; eauto.
             eapply binding_inv_exposed; eauto.
             inv H6; auto.
             apply Included_refl.
             apply free_letapp_k_subset.
          -- exists ((S c) + j2), r2; split.
             ++ inv H5.
                rewrite_math ((S c + j2) = S (c + j2)).
                constructor; auto.
                ** eapply BStep_letapp_Res; eauto.
                   intros.
                   destruct H21; auto.
                   inv H8.
                   split; auto.
                ** eapply bstep_fuel_exposed_inv; eauto.
             ++ apply R_mono with (i - S c0 - c'); try lia; auto.
      + eexists; eexists; repeat split; eauto.
        simpl; auto.
  Qed.

  Lemma constr_compat Γ x t xs k k' :
    K ! x = None ->
    Disjoint _ (FromList xs) (Dom_map K) ->

    (FromList xs \subset Γ) ->
    trans_correct (x |: Γ) k k' ->
    trans_correct Γ (A0.Econstr x t xs k) (A1.Econstr x w0 t xs k').
  Proof.
    unfold trans_correct, E, E'.
    intros.
    inv H6.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv H7.
      destruct (G_get_list H4 xs vs) as [vs' [Heqvs' Hvs]]; auto.
      + eapply A1.free_constr_xs_subset; eauto.
      + inv Hvs.
        assert (wf_val (Tag w0 (A1.Vconstr t vs'))).
        {
          apply wf_val_Vconstr; auto.
          eapply V_wf_val_Forall_r; eauto.
        }

        assert (exposed (Tag w0 (A1.Vconstr t vs'))).
        {
          constructor; auto.
          apply w0_exposed.
        }

        assert (length vs = length vs').
        {
          unfold wval in *.
          rewrite <- (get_list_length_eq _ _ _ H13).
          rewrite <- (get_list_length_eq _ _ _ Heqvs'); auto.
        }

        edestruct (H2 i (M.set x (A0.Vconstr t vs) ρ1) (M.set x (Tag w0 (A1.Vconstr t vs')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk' Rr]]]; eauto; try lia.
        * eapply G_subset with (Γ2 := (x |: (A1.occurs_free (A1.Econstr x w0 t xs k')))).
          eapply G_set; eauto.
          -- destruct i; simpl;
               rewrite w0_exposedb;
               repeat (split; eauto).
             eapply V_mono_Forall; eauto; lia.
          -- eapply binding_inv_exposed; eauto.
          -- apply Included_refl.
          -- apply A1.free_constr_k_subset.
        * exists (S j2), r2; split; eauto.
          -- econstructor.
             econstructor; eauto.
             eapply bstep_fuel_exposed_inv in Hk'; eauto.
          -- apply R_mono with (i - c); try lia; auto.
  Qed.

  Lemma proj_compat Γ x i y e e' :
    K ! x = None ->
    K ! y = None ->

    (y \in Γ) ->
    trans_correct (x |: Γ) e e' ->
    trans_correct Γ (A0.Eproj x i y e) (A1.Eproj x w0 i y e').
  Proof.
    unfold trans_correct, E, E'.
    intros.
    inv H6.
    - exists 0, A1.OOT; split; simpl; auto.
    - inv H7.
      edestruct (G_get H4 y) as [v2 [Heqv2 HV]]; eauto.
      destruct i0.
      inv H5.
      destruct v2; simpl in HV;
        destruct HV as [Hb [Hv HV]]; subst.
      destruct (exposed_reflect w); try contradiction.
      2 : { fcrush. }
      destruct v0.
      fcrush.

      rename l into vs'.
      rename c0 into t'.
      destruct HV as [Hex [Heqt HFvs]]; subst.
      destruct (Forall2_nth_error H14 HFvs) as [v' [Heqv' HFv]].
      edestruct (H2 i0 (M.set x v ρ1) (M.set x v' ρ2)) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
      + eapply G_subset with (Γ2 := (x |: (A1.occurs_free (A1.Eproj x w0 i y e')))).
        eapply G_set; eauto.
        eapply G_mono with (S i0); eauto; try lia.
        eapply V_mono; eauto; lia.
        eapply binding_inv_exposed; eauto.
        eapply Forall_nth_error; eauto.
        inv Hex; auto.
        apply Included_refl.
        apply A1.free_proj_k_subset.
      + assert (Hw : w = w0).
        {
          inv Hex.
          apply Exposed_singleton; eauto.
        }
        subst.

        exists (S j2), r2; split; eauto.
        constructor.
        econstructor; eauto.
        eapply bstep_fuel_exposed_inv; eauto.
  Qed.

  Lemma case_nil_compat Γ x:
    K ! x = None ->
    (x \in Γ) ->
    trans_correct Γ (A0.Ecase x []) (A1.Ecase x w0 []).
  Proof.
    unfold trans_correct, E, E'.
    intros.
    inv H4.
    - exists 0, A1.OOT; split; simpl; auto.
    - fcrush.
  Qed.

  Lemma case_cons_compat Γ x t e e' cl cl':
    K ! x = None ->
    (x \in Γ) ->
    trans_correct Γ e e' ->
    trans_correct Γ (A0.Ecase x cl) (A1.Ecase x w0 cl') ->
    trans_correct Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x w0 ((t, e') :: cl')).
  Proof.
    unfold trans_correct, E, E'.
    intros.
    inv H6.
    - exists 0, OOT; split; simpl; eauto.
    - inv H7.
      edestruct (G_get H4) as [v2 [Heqv2 HV]]; eauto.
      destruct v2.
      destruct i.
      inv H5.
      destruct v; simpl in HV;
        destruct HV as [Hb [Hv2 HV]]; subst;
        destruct (exposed_reflect w); try contradiction.
      fcrush.
      2 : { fcrush. }

      destruct HV as [Hex [Heqt HFvs]]; subst.
      assert (Hw : w = w0).
      {
        inv Hex.
        apply Exposed_singleton; eauto.
      }
      subst.

      inv H10.
      + edestruct (H1 i ρ1 ρ2) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
        eapply G_subset with (Γ2 := (A1.occurs_free (A1.Ecase x w0 ((c0, e') :: cl')))); eauto.
        eapply G_mono; eauto.
        apply Included_refl.
        apply A1.free_case_hd_subset.

        exists (S j2), r2; split; eauto.
        econstructor; eauto.
        eapply bstep_fuel_exposed_inv; eauto.
      + edestruct (H2 (S i) ρ1 ρ2) with (j1 := S c) (r1 := r1) as [j2 [r2 [He' HR]]]; eauto; try lia.
        eapply G_subset; eauto.
        apply Included_refl.
        apply A1.free_case_tl_subset; auto.

        exists j2, r2; split; eauto.
        inv He'; auto.
        inv H6.
        invc; eauto.
  Qed.

  (* Fundamental Property *)
  Lemma fundamental_property {Γ e e'}:
    trans K Γ e e' -> trans_correct Γ e e'.
  Proof.
    intros.
    induction H; intros.
    - eapply ret_compat; eauto.
    - eapply fun_known_compat; eauto.
    - eapply fun_unknown_compat; eauto.
    - eapply app_known_compat; eauto.
    - eapply app_unknown_compat; eauto.
    - eapply letapp_known_compat; eauto.
    - eapply letapp_unknown_compat; eauto.
    - eapply constr_compat; eauto.
    - eapply proj_compat; eauto.
    - eapply case_nil_compat; eauto.
    - eapply case_cons_compat; eauto.
  Qed.

End Compat.

(* Top-level Theorems *)

Module AM := AnnotateTop.
Module VV := AnnotateVVTop VKnownM.
Import VV.

Section Top.

  (* G_top is stronger than G *)
  Lemma G_top_G :
    forall {i K Γ1 ρ1 Γ2 ρ2},
      AM.G i Γ1 ρ1 Γ2 ρ2 ->
      Disjoint _ Γ1 (Dom_map K) ->
      G K i Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold AM.G, G.
    intros.
    destruct H as [HΓ [Hρ HG]].
    unfold Ensembles.Included, Ensembles.In, Dom_map in *.
    split; auto; intros.
    edestruct HG as [v1' [v2 [Heqv1 [Heqv2 HV]]]]; eauto.
    invc.
    eexists; split; eauto.
    assert (exposed v2) by (eapply AM.V_exposed_r; eauto).
    split; auto.
    eapply binding_inv_exposed; eauto.
    eapply not_Dom_map_eq; eauto.
    inv H0.
    fcrush.
    eapply exposed_V_relate; eauto.
  Qed.

  Lemma G_G_top K i Γ1 ρ1 Γ2 ρ2 :
    G K i Γ1 ρ1 Γ2 ρ2 ->
    Γ2 \subset Γ1 ->
    AM.G i Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold G, AM.G.
    intros.
    destruct H as [Hρ HG].
    repeat (split; auto); intros.
  Abort.

  (* [trans_correct] is stronger than [trans_correct_top] due to [G_top] *)
  Lemma trans_correct_trans_correct_top K e1 e2 :
    A1.occurs_free e2 \subset A0.occurs_free e1 ->
    known_map_inv K ->
    Disjoint _ (A0.occurs_free e1) (Dom_map K) ->
    trans_correct K (A0.occurs_free e1) e1 e2 ->
    AM.trans_correct e1 e2.
  Proof.
    unfold AM.trans_correct, trans_correct.
    intros.
    split; auto; intros.
    unfold AM.E, AM.VM.E, E, E' in *.
    intros.
    edestruct H2 as [j2 [r2 [Hstep HR]]]; eauto.
    eapply G_top_G; eauto.
    eexists; eexists; split; eauto.
    eapply exposed_R_relate; eauto.
    eapply bstep_fuel_exposed_inv; eauto.
  Qed.

  Lemma trans_correct_top_trans_correct K e1 e2 :
    AM.trans_correct e1 e2 ->
    trans_correct K (A0.occurs_free e1) e1 e2.
  Proof.
    unfold trans_correct_top, trans_correct.
    intros.
    destruct H as [HS H].
  Abort.

  (* Top-level correctness for the analysis *)
  Theorem top K etop etop':
    known_map_inv K ->
    Disjoint _ (A0.occurs_free etop) (Dom_map K) ->
    trans K (A0.occurs_free etop) etop etop' ->
    AM.trans_correct etop etop'.
  Proof.
    intros HK HD H.
    specialize (fundamental_property _ H).
    eapply trans_correct_trans_correct_top; eauto.
    eapply trans_exp_inv; eauto.
  Qed.

  Corollary top' K etop etop':
    analyze_spec K etop ->
    trans K (A0.occurs_free etop) etop etop' ->
    AM.trans_correct etop etop'.
  Proof.
    intros HA H.
    destruct HA  as [Hk [HK HD]].
    eapply top; eauto.
  Qed.

End Top.

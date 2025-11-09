From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF0 ANF Annotate Erase.

Module A0 := ANF0.
Module A1 := ANF.

(* Known Function Analysis With A Single Exposed Web Id *)

(* Outline: *)
(* 1. build `K : known_map` for every function identifiers (assume unique names) in the program with nonexposed web ids (Note it is not necessary to require them to be distinct though) *)
(* 2. follow `escape_fun_exp` as in CertiCoq to filter `K` so that its domain satisfies `known_fun` *)
(* 3. rewrite based on `K` [this is the main result we are establishing here] *)

Definition known_map := M.t web.

Parameter analyze : A0.exp -> known_map.

(* Specification for `analyze` *)
(* Similar to CertiCoq's `Known_exp` *)
Inductive known_fun (S : Ensemble var) : A0.exp -> Prop :=
| Known_Ret :
  forall x,
    (~ x \in S) ->
    known_fun S (A0.Eret x)

| Known_App :
  forall f ys,
    (f \in S) ->
    Disjoint _ (FromList ys) S ->
    known_fun S (A0.Eapp f ys)

| Known_LetApp :
  forall x f ys e,
    (f \in S) ->
    (~ x \in S) -> (* intermediate result shouldn't be known fun *)
    Disjoint _ (FromList ys) S ->
    known_fun S e ->
    known_fun S (A0.Eletapp x f ys e)

| Known_Fun:
  forall f xs e k,
    (f \in S) ->
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

Definition known_map_bound (K : known_map) e :=
  (Dom_map K) \subset (A0.bound_var e).

Definition known_map_exclude (K : known_map) Γ :=
  Disjoint _ (Dom_map K) Γ.

Definition analyze_spec K e :=
  known_fun (Dom_map K) e /\
  known_map_inv K.

Axiom analyze_sound :
  forall (e : A0.exp),
    analyze_spec (analyze e) e.

Lemma known_fun_known_map_bound K e :
  known_fun (Dom_map K) e ->
  known_map_bound K e.
Proof.
Admitted.

Lemma known_fun_known_map_free K e :
  known_fun (Dom_map K) e ->
  known_map_exclude K (A0.occurs_free e).
Proof.
Admitted.

(*
Lemma analyze_Disjoint e1 e2 :
  Disjoint _ (A0.bound_var e1) (A0.bound_var e2) ->
  let K1 := analyze e1 in
  let K2 := analyze e2 in
  Disjoint _ (Dom_map K1) (Dom_map K2).
Proof.
  intros.
  destruct (analyze_sound e1) as [_ [_ He1]].
  destruct (analyze_sound e2) as [_ [_ He2]].
  unfold known_map_bound in *.
  subst K1; subst K2.
  eapply Disjoint_Included; eauto.
Qed.
 *)

Parameter join : known_map -> known_map -> known_map.

Definition join_spec (K1 K2 K3 : known_map) :=
  forall x,
    (forall w, K1 ! x = Some w -> K2 ! x = None -> K3 ! x = Some w) /\
    (forall w, K1 ! x = None -> K2 ! x = Some w -> K3 ! x = Some w) /\
    (K1 ! x = None -> K2 ! x = None -> K3 ! x = None).

Axiom join_sound :
  forall K1 K2,
    Disjoint _ (Dom_map K1) (Dom_map K2) ->
    join_spec K1 K2 (join K1 K2).

Lemma Disjoint_join_known_map_inv K1 K2 :
  Disjoint _ (Dom_map K1) (Dom_map K2) ->
  known_map_inv K1 ->
  known_map_inv K2 ->
  known_map_inv (join K1 K2).
Proof.
  intros HD HK1 HK2.
  pose proof (join_sound _ _ HD) as HJ.
  unfold join_spec, known_map_inv in *.
  intros.
  intros Hc.
  destruct (HJ f) as [Hf1 [Hf2 Hf3]].
  clear HJ.
  destruct (K1 ! f) eqn:HK1f;
    destruct (K2 ! f) eqn:HK2f;
    remember (join K1 K2) as K3.
  - inv HD.
    apply (H0 f).
    constructor; unfold Ensembles.In, Dom_map; eauto.
  - assert (K3 ! f = Some w0) by (eapply Hf1; eauto).
    rewrite H in H0; inv H0.
    eapply HK1; eauto.
  - assert (K3 ! f = Some w0) by (eapply Hf2; eauto).
    rewrite H in H0; inv H0.
    eapply HK2; eauto.
  - assert (K3 ! f = None) by (eapply Hf3; eauto).
    rewrite H in H0; inv H0.
Qed.

Parameter w0 : web.
Axiom w0_exposed : w0 \in Exposed.
Axiom Exposed_singleton : forall w, w \in Exposed -> w = w0.

Theorem Exposed_nonempty : exists w, w \in Exposed.
Proof. exists w0. apply w0_exposed. Qed.

Section Known.
  Variable K : known_map.

  (* Specification based on `known_fun` *)
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
      Disjoint _ (FromList xs) (Dom_map K) ->

      trans_ (FromList xs :|: (f |: Γ)) e e' ->
      trans_ (f |: Γ) k k' ->
      trans_ Γ (A0.Efun f xs e k) (A1.Efun f w xs e' k')

  | Trans_fun_unknown :
    forall {f xs e k e' k'},
      K ! f = None ->
      Disjoint _ (FromList xs) (Dom_map K) ->

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

  | Trans_letapp_known :
    forall {x f w xs k k'},
      K ! f = Some w ->
      (~ w \in Exposed) ->
      Disjoint _ (FromList xs) (Dom_map K) ->
      K ! x = None ->

      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans_ (x |: Γ) k k' ->
      trans_ Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w xs k')

  | Trans_letapp_unknown :
    forall {x f xs k k'},
      K ! f = None ->
      Disjoint _ (FromList xs) (Dom_map K) ->
      K ! x = None ->

      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans_ (x |: Γ) k k' ->
      trans_ Γ (A0.Eletapp x f xs k) (A1.Eletapp x f w0 xs k')

  (* data webs are all exposed *)

  | Trans_constr :
    forall {x t xs k k'},
      K ! x = None ->
      Disjoint _ (FromList xs) (Dom_map K) ->

      (FromList xs \subset Γ) ->
      trans_ (x |: Γ) k k' ->
      trans_ Γ (A0.Econstr x t xs k) (A1.Econstr x w0 t xs k')

  | Trans_proj :
    forall {x y k k' n},
      K ! x = None ->
      K ! y = None ->

      (y \in Γ) ->
      trans_ (x |: Γ) k k' ->
      trans_ Γ (A0.Eproj x n y k) (A1.Eproj x w0 n y k')

  | Trans_case_nil :
    forall {x},
      K ! x = None ->
      (x \in Γ) ->
      trans_ Γ (A0.Ecase x []) (A1.Ecase x w0 [])

  | Trans_case_cons :
    forall {x e e' t cl cl'},
      K ! x = None ->
      (x \in Γ) ->
      trans_ Γ e e' ->
      trans_ Γ (A0.Ecase x cl) (A1.Ecase x w0 cl') ->
      trans_ Γ (A0.Ecase x ((t, e) :: cl)) (A1.Ecase x w0 ((t, e') :: cl')).

  Hint Constructors trans_ : core.

  Definition trans := trans_.

  Hint Unfold trans : core.

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
    - apply Dom_map_eq in H.
      destruct H as [w Hw].
      exists (A1.Eapp f w ys); econstructor; eauto.
      eapply A0.free_app_xs_inv; eauto.
    - apply Dom_map_eq in H.
      destruct H as [w Hw].
      destruct (IHknown_fun (x |: Γ)) as [e' He']; auto.
      eapply A0.free_letapp_k_inv; eauto.
      exists (A1.Eletapp x f w ys e'); econstructor; eauto.
      eapply A0.free_letapp_xs_inv; eauto.
    - apply Dom_map_eq in H.
      destruct H as [w Hw].
      destruct (IHknown_fun1 (FromList xs :|: (f |: Γ))) as [e' He']; auto.
      eapply A0.free_fun_e_inv; eauto.
      destruct (IHknown_fun2 (f |: Γ)) as [k' Hk']; auto.
      eapply A0.free_fun_k_inv; eauto.
      exists (A1.Efun f w xs e' k'); econstructor; eauto.
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

  Corollary known_fun_trans_total e :
    known_map_inv K ->
    known_fun (Dom_map K) e ->
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

  Lemma Erase_Annotate_id e1 e2 e1' :
    trans (A0.occurs_free e1) e1 e1' ->
    Erase.trans (A1.occurs_free e1') e1' e2 ->
    e1 = e2.
  Proof.
  Admitted.

  (* Cross-language Logical Relations *)
  (* Note these are parameterized by the known_map, `K` *)
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
            (* note function arguments and result are always exposed regardless of whether a function is known or unknown *)
            f1 = f2 /\
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
                      Forall exposed vs2 ->
                      Forall2 (V (i0 - (i0 - j))) vs1 vs2 ->
                      set_lists xs1 vs1 (M.set f1 (A0.Vfun f1 ρ1 xs1 e1) ρ1) = Some ρ3 ->
                      set_lists xs2 vs2 (M.set f2 (Tag w2 (A1.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                      E' V true (i0 - (i0 - j)) ρ3 e1 ρ4 e2
                end
            end
        | _, _ => False
        end
    end.

  Definition R := (R' V).

  Definition E := (E' V).

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
    (forall w, K ! x = Some w -> same_id x v) /\
    (K ! x = None -> exposed v).

  Lemma binding_inv_exposed x v :
    (K ! x = None) ->
    exposed v ->
    binding_inv x v.
  Proof.
    unfold binding_inv.
    intros.
    split; intros; auto.
    rewrite H in H1; discriminate.
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
    binding_inv f (Tag w (A1.Vfun f ρ xs e)).
  Proof.
    intros.
    split; intros; simpl; auto.
    rewrite H in H0; discriminate.
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
           V i v1 v2).

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
      Disjoint _ (FromList xs) (Dom_map K) ->
      get_list xs ρ1 = Some vs1 ->
      exists vs2,
        get_list xs ρ2 = Some vs2 /\
        Forall exposed vs2 /\
        Forall2 (V i) vs1 vs2.
  Proof.
    intros HG xs.
    induction xs; simpl; intros.
    - inv H2; eauto.
    - destruct (ρ1 ! a) eqn:Heq1; try discriminate.
      destruct (get_list xs ρ1) eqn:Heq3; try discriminate.
      inv H2.
      unfold Ensembles.Included, Ensembles.In in *.
      edestruct (G_get HG) as [v2 [Heqv2 [[Hid HK] HV]]]; eauto.
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
  Qed.

  Lemma G_set {i Γ1 ρ1 Γ2 ρ2}:
    G i Γ1 ρ1 Γ2 ρ2 ->
    forall {x v1 v2},
      V i v1 v2 ->
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
      Forall2 (V i) vs1 vs2 ->
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
        * destruct H2 as [Hlen [Heqw [Hex HV]]]; subst.
          repeat (split; eauto).
        * destruct H2 as [Hlen [Hex HV]].
          repeat (split; eauto).
      + destruct HV as [Hex [Hc HV]]; subst.
        repeat split; auto.
        eapply Forall2_length; eauto.
    - repeat (split; auto).
      destruct v1; destruct v; try contradiction.
      + destruct HV as [Hf [Hlen HV]]; subst.
        repeat split; auto.
        destruct (K ! v) eqn:HeqK.
        * destruct HV as [Heqw [Hex HV]]; subst.
          repeat split; auto; intros.
          specialize (HV j0 vs1 vs2 ρ3 ρ4).
          rewrite normalize_step in *; try lia.
          apply HV; eauto; lia.
        * destruct HV as [Hex HV]; subst.
          repeat split; auto; intros.
          specialize (HV j0 vs1 vs2 ρ3 ρ4).
          rewrite normalize_step in *; try lia.
          eapply HV; eauto; lia.
      + destruct HV as [Hex [Heqc HV]]; subst.
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
    edestruct H2 as [v2 [Heqv2 [[Hid HK] HV]]]; eauto.
    eexists; eexists; repeat split; eauto.
    apply V_mono with i; eauto.
  Qed.

  (* Compatibility Lemmas *)
  Definition trans_correct Γ e1 e2 :=
    forall i ρ1 ρ2,
      known_map_inv K ->
      G i Γ ρ1 (A1.occurs_free e2) ρ2 ->
      E true i ρ1 e1 ρ2 e2.

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
      edestruct (G_get H2) as [v2 [Heqv2 [[Hid HK] HV]]]; eauto.
      exists 1, (A1.Res v2); split; simpl; auto.
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
      V i (A0.Vfun f ρ1 xs e) (Tag w (A1.Vfun f ρ2 xs e')).
  Proof.
    unfold trans_correct.
    intros HK HKf HKxs He i.
    assert (~ Ensembles.In web Exposed w) by (eapply HK; eauto).
    induction i; simpl; intros; auto;
      rewrite HKf;
      repeat (split; auto); intros.

    apply (He (i - (i - j)) ρ3 ρ4); auto.
    - eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))); eauto.
      eapply G_set_lists; eauto.
      eapply G_set; eauto.
      + apply G_mono with (S i); eauto; lia.
      + apply V_mono with i; try lia.
        eapply IHi with (Γ2 := Γ2); eauto.
        apply G_mono with (S i); eauto; lia.
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
        apply G_mono with i; eauto; lia.
        * eapply Vfun_V_known; eauto.
          -- eapply G_wf_env_r; eauto.
          -- apply G_mono with i; eauto; lia.
          -- apply A1.free_fun_e_subset.
        * eapply binding_inv_known_fun; eauto.
        * apply Included_refl.
        * apply A1.free_fun_k_subset.
      + exists (S j2), r2; split; auto.
        * constructor; simpl; auto.
          eapply bstep_fuel_exposed_inv; eauto.
        * apply R_mono with ((i - 1) - c); try lia; auto.
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
      V i (A0.Vfun f ρ1 xs e) (Tag w0 (A1.Vfun f ρ2 xs e')).
  Proof.
    unfold trans_correct.
    intros HK HKf HKxs He i.
    induction i; simpl; intros; auto;
      rewrite HKf;
      repeat (split; auto); intros;
      try (constructor; apply w0_exposed).

    apply (He (i - (i - j)) ρ3 ρ4); auto.
    - eapply G_subset with (Γ2 := (FromList xs :|: (f |: Γ2))); eauto.
      eapply G_set_lists; eauto.
      eapply G_set; eauto.
      + apply G_mono with (S i); eauto; lia.
      + apply V_mono with i; try lia.
        eapply IHi with (Γ2 := Γ2); eauto.
        apply G_mono with (S i); eauto; lia.
      + split; intros; simpl; auto.
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
          -- apply G_mono with i; eauto; lia.
          -- apply A1.free_fun_e_subset.
        * eapply binding_inv_exposed; eauto.
          constructor; apply w0_exposed.
        * apply Included_refl.
        * apply A1.free_fun_k_subset.
      + exists (S j2), r2; split; auto.
        * constructor; simpl; auto.
          eapply bstep_fuel_exposed_inv; eauto.
        * apply R_mono with ((i - 1) - c); try lia; auto.
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
      edestruct (G_get H2 f) as [fv2 [Heqfv2 [[Hid HK] HV]]]; eauto.
      destruct i.
      inv H3.
      destruct fv2; simpl in HV;
        destruct HV as [Hv1 HV];
        destruct v; try contradiction.
      specialize (Hid _ HKf).
      apply same_id_fun in Hid; subst.
      destruct HV as [Hfeq [Hlen HV]]; subst.
      destruct (K ! f) eqn:Heqk; try contradiction.
      + destruct HV as [Heqw [Hex HV]]; subst.
        inv HKf.
        clear HK Hex.

        edestruct (G_get_list H2 xs vs) as [vs2 [Heqvs2 [Hexvs Vvs]]]; eauto.
        eapply A1.free_app_xs_subset; eauto.

        destruct (set_lists_length3 (M.set f (Tag w (A1.Vfun f t l e0)) t) l vs2) as [ρ4 Heqρ4].
        unfold wval in *.
        rewrite <- (Forall2_length _ _ _ Vvs).
        rewrite <- (set_lists_length_eq _ _ _ _ H9); auto.

        assert (HE : E true (i - (i - i)) ρ'' e ρ4 e0).
        {
          eapply (HV i vs vs2); eauto.
          apply V_mono_Forall with (S i); auto; lia.
        }

        apply (E_mono _ i) in HE; try lia.
        unfold E in HE.
        destruct (HE c r1) as [j2 [r2 [He0 Rr]]]; try lia; auto.
        exists (S j2), r2; split; eauto.
        constructor; auto.
        * econstructor; eauto.
          destruct (exposed_reflect w); try contradiction; auto.
          -- pose proof He0 as Hr2.
             apply bstep_fuel_exposed_inv in Hr2.
             eapply bstep_fuel_exposed; eauto.
          -- intros; contradiction.
        * eapply bstep_fuel_exposed_inv; eauto.
      + destruct HV as [Hex HV].
        inv Hex.
        rewrite HKf in Heqk; discriminate.
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
      edestruct (G_get H2 f) as [fv2 [Heqfv2 [[Hid HK] HV]]]; eauto.
      destruct i.
      inv H3.
      destruct fv2; simpl in HV;
        destruct HV as [Hv1 HV];
        destruct v; try contradiction.
      destruct HV as [Hfeq [Hlen HV]]; subst.
      rename v into f'.
      destruct (K ! f') eqn:HeqKf'; try discriminate.
      + destruct HV as [Heqw [Hex HV]]; subst.
        specialize (HK HKf).
        inv HK; contradiction.
      + destruct HV as [Hex HV].
        inv Hex.
        assert (Hw : w = w0) by (apply Exposed_singleton; eauto); subst.

        edestruct (G_get_list H2 xs vs) as [vs2 [Heqvs2 [Hexvs Vvs]]]; eauto.
        eapply A1.free_app_xs_subset; eauto.

        destruct (set_lists_length3 (M.set f' (Tag w0 (A1.Vfun f' t l e0)) t) l vs2) as [ρ4 Heqρ4].
        unfold wval in *.
        rewrite <- (Forall2_length _ _ _ Vvs).
        rewrite <- (set_lists_length_eq _ _ _ _ H9); auto.

        assert (HE : E true (i - (i - i)) ρ'' e ρ4 e0).
        {
          eapply (HV i vs vs2); eauto.
          apply V_mono_Forall with (S i); auto; lia.
        }

        apply (E_mono _ i) in HE; try lia.
        unfold E in HE.
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
          rename w1 into v0.
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
          -- destruct i; simpl; repeat (split; eauto).
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
      destruct v2;
        simpl in HV;
        destruct HV as [Hb [Hv HV]]; subst;
        destruct v0; try contradiction.
      rename l into vs'.
      rename c0 into t'.
      destruct HV as [Hex [Heqt HFvs]]; subst.
      destruct (Forall2_nth_error H14 HFvs) as [v' [Heqv' HFv]].
      edestruct (H2 i0 (M.set x v ρ1) (M.set x v' ρ2)) with (j1 := c) as [j2 [r2 [He' HR]]]; eauto; try lia.
      + eapply G_subset with (Γ2 := (x |: (A1.occurs_free (A1.Eproj x w0 i y e')))).
        eapply G_set; eauto.
        eapply G_mono with (S i0); eauto; try lia.
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
    - inv H5.
      inv H8.
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
        subst; try contradiction.
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
        rewrite Heqv2 in H12; inv H12; eauto.
  Qed.

  (* Fundamental Property *)
  Lemma fundamental_property {Γ e e'}:
    trans Γ e e' -> trans_correct Γ e e'.
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

  (* Top Level *)
  Definition binding_inv_top x v :=
    K ! x = None /\ exposed v.

  Lemma binding_inv_top_exposed x v :
    K ! x = None ->
    exposed v ->
    binding_inv_top x v.
  Proof. intros. repeat (split; auto). Qed.

  Lemma binding_inv_top_exposed_Forall xs :
    forall vs,
      Disjoint _ (FromList xs) (Dom_map K) ->
      length xs = length vs ->
      Forall exposed vs ->
      Forall2 binding_inv_top xs vs.
  Proof.
    induction xs; simpl; intros;
      destruct vs; try discriminate; auto.
    inv H0; inv H1.
    apply Disjoint_FromList_cons_inv in H.
    inv H.
    constructor; auto.
    apply binding_inv_top_exposed; auto.
  Qed.

  Lemma binding_inv_top_binding_inv x v :
    binding_inv_top x v ->
    binding_inv x v.
  Proof.
    unfold binding_inv_top.
    intro H; inv H.
    eapply binding_inv_exposed; eauto.
  Qed.

  Definition G_top i Γ1 ρ1 Γ2 ρ2 :=
    wf_env ρ2 /\
    Γ2 \subset Γ1 /\
    forall x,
      (x \in Γ1) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
        M.get x ρ2 = Some v2 /\
        binding_inv_top x v2 /\
        V i v1 v2.

  Lemma G_top_wf_env_r i Γ1 ρ1 Γ2 ρ2 :
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    wf_env ρ2.
  Proof. unfold G_top. intros; tauto. Qed.

  Lemma G_top_subset_inv i Γ1 ρ1 Γ2 ρ2 :
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    Γ2 \subset Γ1.
  Proof. unfold G_top; intros; tauto. Qed.

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
    edestruct HG as [v1' [v2 [Heqv1 [Heqv2 [[HKx Hex] HV]]]]]; eauto.
    rewrite Heqv1 in H0; inv H0; eauto.
    eexists; split; eauto.
    split; auto.
    eapply binding_inv_exposed; eauto.
  Qed.

  Lemma G_G_top i Γ1 ρ1 Γ2 ρ2 :
    G i Γ1 ρ1 Γ2 ρ2 ->
    Γ2 \subset Γ1 ->
    G_top i Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold G, G_top.
    intros.
    destruct H as [Hρ HG].
    repeat (split; auto); intros.
  Abort.

  Definition trans_correct_top etop etop' :=
    A1.occurs_free etop' \subset A0.occurs_free etop /\
    forall i ρ1 ρ2,
      known_map_inv K ->
      G_top i (A0.occurs_free etop) ρ1 (A1.occurs_free etop') ρ2 ->
      E true i ρ1 etop ρ2 etop'.

  Lemma trans_correct_top_subset e1 e2 :
    trans_correct_top e1 e2 ->
    A1.occurs_free e2 \subset A0.occurs_free e1.
  Proof.
    unfold trans_correct_top.
    intros.
    inv H; auto.
  Qed.

  Lemma trans_correct_subset Γ1 Γ2 e1 e2 :
    trans_correct Γ1 e1 e2 ->
    Γ1 \subset Γ2 ->
    trans_correct Γ2 e1 e2.
  Proof.
    unfold trans_correct.
    intros.
    eapply H; eauto.
    eapply G_subset; eauto.
    apply Included_refl.
  Qed.

  Lemma trans_correct_top_trans_correct e1 e2 :
    trans_correct_top e1 e2 ->
    trans_correct (A0.occurs_free e1) e1 e2.
  Proof.
    unfold trans_correct_top, trans_correct.
    intros.
    destruct H as [HS H].
    eapply H; eauto.
    (* eapply G_G_top; eauto. *)
  Abort.

  (* [trans_correct] is stronger than [trans_correct_top] due to [G_top] *)
  Lemma trans_correct_trans_correct_top e1 e2 :
    A1.occurs_free e2 \subset A0.occurs_free e1 ->
    trans_correct (A0.occurs_free e1) e1 e2 ->
    trans_correct_top e1 e2.
  Proof.
    unfold trans_correct_top, trans_correct.
    intros.
    split; auto; intros.
    eapply H0; eauto.
    eapply G_top_G; eauto.
  Qed.

  Theorem top etop etop':
    trans (A0.occurs_free etop) etop etop' ->
    trans_correct_top etop etop'.
  Proof.
    intros H.
    specialize (fundamental_property H).
    eapply trans_correct_trans_correct_top; eauto.
    eapply trans_exp_inv; eauto.
  Qed.

  (* Cross-language Compositionality *)

  (* Adequacy *)
  Theorem adequacy e1 e2:
    known_map_inv K ->
    trans_correct_top e1 e2 ->
    forall ρ1 ρ2,
      wf_env ρ2 ->
      (forall k, G_top k (A0.occurs_free e1) ρ1 (A1.occurs_free e2) ρ2) ->
      forall j1 r1,
        A0.bstep_fuel ρ1 e1 j1 r1 ->
        exists j2 r2,
          A1.bstep_fuel true ρ2 e2 j2 r2 /\
          (forall k, R k r1 r2).
  Proof.
    intros HK; intros.
    unfold trans_correct_top in H.
    destruct H as [HS HT].

    assert (HE : E true j1 ρ1 e1 ρ2 e2) by (eapply (HT j1); eauto).
    edestruct (HE j1) as [j2 [r2 [Hstep2 HR]]]; eauto.
    eexists; eexists; split; eauto.

    intros.
    assert (HE' : E true (j1 + k) ρ1 e1 ρ2 e2) by (eapply HT; eauto).
    edestruct (HE' j1) as [j2' [r2' [Hstep2' HR']]]; eauto; try lia.

    rewrite_math (j1 + k - j1 = k).
    rewrite_math (j1 - j1 = 0).

    destruct r2; destruct r2'; destruct r1;
      simpl in *; auto; try contradiction.

    edestruct (A1.bstep_fuel_deterministic w w1 Hstep2 Hstep2'); subst; eauto.
  Qed.

  (* Behavioral Refinement *)
  Inductive val_ref_ : A0.val -> A1.wval -> Prop :=
  | Ref_Vfun :
    forall f1 ρ1 w xs1 e1 f2 ρ2 xs2 e2,
      val_ref_ (A0.Vfun f1 ρ1 xs1 e1) (Tag w (A1.Vfun f2 ρ2 xs2 e2))

  | Ref_Vconstr_nil :
    forall c,
      val_ref_ (A0.Vconstr c []) (Tag w0 (A1.Vconstr c []))

  | Ref_Vconstr_cons :
    forall c v1 v2 vs1 vs2,
      val_ref_ v1 v2 ->
      val_ref_ (A0.Vconstr c vs1) (Tag w0 (A1.Vconstr c vs2)) ->
      val_ref_ (A0.Vconstr c (v1 :: vs1)) (Tag w0 (A1.Vconstr c (v2 :: vs2))).

  Hint Constructors val_ref_ : core.

  Definition val_ref := val_ref_.

  Hint Unfold val_ref : core.

  Lemma val_ref_Vconstr c vs1 vs2 :
    Forall2 val_ref vs1 vs2 ->
    val_ref (A0.Vconstr c vs1) (Tag w0 (A1.Vconstr c vs2)).
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
      simpl in H.
      destruct H as [Hw HV].
      destruct v; try contradiction.
      destruct HV as [Hex [Hc Hlen]]; subst.
      destruct l; try discriminate.
      inv Hex.
      apply Exposed_singleton in H1; subst; auto.
    - destruct v2.
      pose proof (H 0) as H0; simpl in *.
      destruct H0 as [Hw HV].
      destruct v; try contradiction.
      destruct HV as [Hex [Hc Hlen]]; subst.

      destruct l0; simpl in *; inv Hlen.
      inv Hex.
      apply Exposed_singleton in H3; subst.

      assert (HV' : forall i, V i v1 t /\ V i (A0.Vconstr c l) (Tag w0 (A1.Vconstr c l0))).
      {
        intros.
        specialize (H (S i)); simpl in *.
        destruct H as [_ [He [Hc HFV]]]; subst.
        inv HFV.
        split; auto.

        assert (He' : exposed (Tag w0 (A1.Vconstr c l0))) by (inv He; inv H5; auto).

        assert (Hw' : wf_val (Tag w0 (A1.Vconstr c l0))).
        {
          constructor; intros; auto.
          inv Hw.
          inv H4; auto.
        }

        destruct i; simpl in *;
          repeat (split; auto);
          try (eapply V_mono_Forall with (S i); eauto).
      }

      assert (HV0 : forall i, V i v1 t) by (intros; destruct (HV' i); auto).
      assert (HV1 : forall i, V i (A0.Vconstr c l) (Tag w0 (A1.Vconstr c l0))) by (intros; destruct (HV' i); auto).

      auto.
    - specialize (H 0); simpl in *.
      destruct H as [Hw HV].
      destruct v2; try contradiction; auto.
      destruct v; try contradiction; auto.
  Qed.

  Corollary R_res_val_ref {v1 v2} :
    (forall i, R i (A0.Res v1) (A1.Res v2)) ->
    val_ref v1 v2.
  Proof.
    intros; eapply V_val_ref; eauto.
  Qed.

  (* Linking Compat Lemmas *)

  (* Top-level Environment Lemmas *)
  Lemma G_top_get {Γ1 Γ2 i ρ1 ρ2}:
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    forall x,
      (x \in Γ1) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
        M.get x ρ2 = Some v2 /\
        binding_inv_top x v2 /\
        V i v1 v2.
  Proof.
    unfold G.
    intros.
    destruct H as [Hr1 [HΓ HG]].
    eapply (HG x); eauto.
  Qed.

  Lemma G_top_get_list {i Γ1 ρ1 Γ2 ρ2} :
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    forall xs,
      (FromList xs) \subset Γ1 ->
      Disjoint _ (FromList xs) (Dom_map K) ->
      exists vs1 vs2,
        get_list xs ρ1 = Some vs1 /\
        get_list xs ρ2 = Some vs2 /\
        Forall exposed vs2 /\
        Forall2 binding_inv_top xs vs2 /\
        Forall2 (V i) vs1 vs2.
  Proof.
    intros HG xs.
    intros.
    induction xs; simpl; intros.
    - eexists; eexists; repeat split; eauto.
    - rewrite FromList_cons in H.
      edestruct (G_top_get HG) as [v1 [v2 [Heqv1 [Heqv2 [Hb HV]]]]]; eauto.
      eapply Disjoint_FromList_cons_inv in H0; inv H0; auto.

      edestruct IHxs as [vs1 [vs2 [Heqvs1 [Heqvs2 [Hexs [Hbs HVs]]]]]]; eauto.
      eapply Included_trans; eauto.
      apply Included_Union_r.

      rewrite Heqv1.
      rewrite Heqvs1.
      rewrite Heqv2.
      rewrite Heqvs2.
      exists (v1 :: vs1), (v2 :: vs2); repeat (split; auto).
      constructor; auto.
      inv Hb.
      inv H3; auto.
  Qed.

  Lemma G_top_set {i Γ1 ρ1 Γ2 ρ2}:
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    forall {x v1 v2},
      binding_inv_top x v2 ->
      V i v1 v2 ->
      G_top i (x |: Γ1) (M.set x v1 ρ1) (x |: Γ2) (M.set x v2 ρ2).
  Proof.
    intros.
    unfold G_top; intros.

    split.
    eapply wf_env_set; eauto.
    eapply G_top_wf_env_r; eauto.
    eapply V_wf_val_r; eauto.

    split.
    apply Included_Union_compat; auto.
    apply Included_refl.
    eapply G_top_subset_inv; eauto.

    intros.
    destruct (M.elt_eq x0 x); subst.
    - repeat rewrite M.gss.
      inv H0.
      eexists; eexists; repeat split; eauto.
    - repeat (rewrite M.gso; auto).
      eapply G_top_get; eauto.
      inv H2; auto.
      inv H3; contradiction.
  Qed.

  Lemma G_top_set_lists {i Γ1 ρ1 Γ2 ρ2}:
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    forall {xs vs1 vs2 ρ3 ρ4},
      Forall2 (V i) vs1 vs2 ->
      Forall2 binding_inv_top xs vs2 ->
      set_lists xs vs1 ρ1 = Some ρ3 ->
      set_lists xs vs2 ρ2 = Some ρ4 ->
      G_top i (FromList xs :|: Γ1) ρ3 (FromList xs :|: Γ2) ρ4.
  Proof.
    intros HG xs.
    assert (HΓ : Γ2 \subset Γ1) by (eapply G_top_subset_inv; eauto).
    induction xs; simpl; intros.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      inv H1; inv H2.
      eapply G_top_subset; eauto.
      normalize_sets.
      rewrite Union_Empty_set_neut_l; eauto.
      apply Included_refl.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
    - destruct vs1; try discriminate.
      destruct vs2; try discriminate.
      destruct (set_lists xs vs1 ρ1) eqn:Heq1; try discriminate.
      destruct (set_lists xs vs2 ρ2) eqn:Heq2; try discriminate.
      inv H; inv H0; inv H1; inv H2.
      eapply G_top_subset with (Γ1 := (a |: (FromList xs :|: Γ1))) (Γ2 := (a |: (FromList xs :|: Γ2))); eauto.
      eapply G_top_set; eauto.
      normalize_sets.
      rewrite Union_assoc.
      apply Included_refl.
      eapply Included_Union_compat; eauto.
      apply Included_refl.
  Qed.

  (* Monotonicity Lemma *)
  Lemma G_top_mono {Γ1 Γ2 ρ1 ρ2} i j:
    G_top i Γ1 ρ1 Γ2 ρ2 ->
    j <= i ->
    G_top j Γ1 ρ1 Γ2 ρ2.
  Proof.
    unfold G_top.
    intros.
    destruct H as [Hr2 [HS HG]].
    repeat (split; auto); intros.
    edestruct HG as [v1 [v2 [Heqv1 [Heqv2 [[Hk Hex] HV]]]]]; eauto.
    eexists; eexists; repeat split; eauto.
    apply V_mono with i; eauto.
  Qed.

  (* Compatibility Lemmas *)
  Lemma Vfun_V_top e e' :
    known_map_inv K ->
    trans_correct_top e e' ->
    forall i f xs Γ1 Γ2 ρ1 ρ2,
      K ! f = None ->
      Disjoint _ (FromList xs) (Dom_map K) ->

      G_top i Γ1 ρ1 Γ2 ρ2 ->
      A0.occurs_free e \subset (FromList xs :|: (f |: Γ1)) ->
      A1.occurs_free e' \subset (FromList xs :|: (f |: Γ2)) ->
      V i (A0.Vfun f ρ1 xs e) (Tag w0 (A1.Vfun f ρ2 xs e')).
  Proof.
    unfold trans_correct_top.
    intros HK [HS He] i.
    assert (Hw0 : w0 \in Exposed) by (apply w0_exposed).

    induction i; simpl; intros; auto;
      assert (Hρ2 : wf_env ρ2) by (eapply G_top_wf_env_r; eauto);
      repeat (split; auto); intros;
      destruct (K ! f) eqn:HKf; try discriminate;
      split; auto; intros.

    apply (He (i - (i - j)) ρ3 ρ4); auto.
    eapply G_top_subset with (Γ1 := FromList xs :|: (f |: Γ1)) (Γ2 := FromList xs :|: (f |: Γ2)); eauto.
    eapply G_top_set_lists; eauto.
    eapply G_top_set; eauto.
    eapply G_top_mono; eauto; try lia.
    eapply binding_inv_top_exposed; simpl; eauto.
    apply V_mono with i; try lia.
    eapply IHi with (Γ2 := Γ2); eauto.
    apply G_top_mono with (S i); eauto; lia.
    eapply binding_inv_top_exposed_Forall; eauto.
    eapply set_lists_length_eq; eauto.
  Qed.

  Lemma free_fun_compat e e' f k k' xs :
    A1.occurs_free e' \subset A0.occurs_free e ->
    A1.occurs_free k' \subset A0.occurs_free k ->
    A1.occurs_free (A1.Efun f w0 xs e' k') \subset A0.occurs_free (A0.Efun f xs e k).
  Proof.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H1; auto.
  Qed.

  Lemma fun_compat_top e e' k k' f xs :
    K ! f = None ->
    Disjoint _ (FromList xs) (Dom_map K) ->

    trans_correct_top e e' ->
    trans_correct_top k k' ->
    trans_correct_top (A0.Efun f xs e k) (Efun f w0 xs e' k').
  Proof.
    unfold trans_correct_top, E, E'.
    intros HKf HKxs; intros.
    assert (Hw0 : w0 \in Exposed) by (apply w0_exposed).

    destruct H.
    destruct H0.
    split; intros.
    eapply free_fun_compat; eauto.

    inv H6.
    - exists 0, OOT; split; simpl; eauto.
    - inv H7.
      edestruct (H2 (i - 1) (M.set f (A0.Vfun f ρ1 xs e) ρ1) (M.set f (Tag w0 (A1.Vfun f ρ2 xs e')) ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
      + eapply G_top_subset with (Γ1 := (f |: (A0.occurs_free (A0.Efun f xs e k)))) (Γ2 := (f |: (A1.occurs_free (A1.Efun f w0 xs e' k')))); eauto.
        * eapply G_top_set; eauto.
          eapply G_top_mono; eauto; try lia.
          split; auto.

          eapply Vfun_V_top with (Γ1 := (A0.occurs_free (A0.Efun f xs e k))) (Γ2 := (A1.occurs_free (A1.Efun f w0 xs e' k'))); eauto.
          -- unfold trans_correct_top.
             split; auto.
          -- eapply G_top_mono; eauto; try lia.
          -- eapply A0.free_fun_e_subset; eauto.
          -- eapply A1.free_fun_e_subset; eauto.
        * eapply A0.free_fun_k_subset; eauto.
      + exists (S j2), r2; split; auto.
        * constructor; auto.
          eapply bstep_fuel_exposed_inv; eauto.
        * apply R_mono with ((i - 1) - c); try lia; auto.
  Qed.

  Lemma free_letapp_compat k k' f x xs :
    A1.occurs_free k' \subset A0.occurs_free k ->
    A1.occurs_free (A1.Eletapp x f w0 xs k') \subset A0.occurs_free (A0.Eletapp x f xs k).
  Proof.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H0; auto.
  Qed.

  Lemma letapp_compat_top k k' xs x f :
    K ! f = None ->
    Disjoint _ (FromList xs) (Dom_map K) ->
    K ! x = None ->

    trans_correct_top k k' ->
    trans_correct_top (A0.Eletapp x f xs k) (A1.Eletapp x f w0 xs k').
  Proof.
    unfold trans_correct_top, E, E'.
    intros HKf HKxs HKx; intros.
    destruct H.
    split; intros.
    eapply free_letapp_compat; eauto.

    inv H4.
    - exists 0, OOT; split; simpl; auto.
    - inv H5.
      + edestruct (G_top_get H2) as [fv1 [fv2 [Heqfv1 [Heqfv2 [[_ Hexfv] HVf]]]]]; eauto.
        rewrite Heqfv1 in H9; inv H9.
        destruct fv2.
        destruct i.
        inv H3.
        simpl in HVf.
        destruct HVf as [Hfv2 HV]; subst.
        destruct v0; try contradiction.
        destruct HV as [Heqf [Hlen HV]]; subst.
        rename v0 into f'.
        inv Hexfv.
        destruct (K ! f') eqn:HKf'.
        destruct HV as [Heqw [Hexw' _]]; subst; contradiction.

        destruct HV as [Hex HV].

        edestruct (G_top_get_list H2 xs) as [vs1 [vs2 [Heqvs1 [Heqvs2 [Hexs [Hbs HVvs]]]]]]; eauto.
        eapply A0.free_letapp_xs_subset; eauto.

        rewrite Heqvs1 in H10; inv H10.

        assert (Heqw : w = w0) by (eapply Exposed_singleton; eauto); inv Heqw.

        destruct (set_lists_length3 (M.set f' (Tag w0 (Vfun f' t l e0)) t) l vs2) as [ρ4 Heqρ4].
        unfold wval in *.
        rewrite <- (Forall2_length _ _ _ HVvs).
        rewrite <- (set_lists_length_eq _ _ _ _ H13); auto.

        unfold E' in HV.
        edestruct (HV i vs vs2 ρ'' ρ4) with (j1 := c0) as [j2 [r2 [He0 HR]]]; eauto; try lia.
        * eapply V_mono_Forall; eauto; lia.
        * destruct r2; simpl in HR; try contradiction.
          edestruct (H0 (i - c0) (M.set x v ρ1) (M.set x w ρ2)) with (j1 := c') as [j3 [r3 [He1 HR']]]; eauto; try lia.
          eapply G_top_subset with (Γ1 := x |: (A0.occurs_free (A0.Eletapp x f xs k))) (Γ2 := x |: (A1.occurs_free (A1.Eletapp x f w0 xs k'))); eauto.
          eapply G_top_set; eauto.
          eapply G_top_mono; eauto; lia.
          -- eapply binding_inv_top_exposed; eauto.
             assert (Hw : exposed_res (A1.Res w)) by (eapply bstep_fuel_exposed_inv; eauto); inv Hw; auto.
          -- eapply V_mono; eauto; try lia.
          -- eapply A0.free_letapp_k_subset; eauto.
          -- exists (S (j2 + j3)), r3; split; eauto.
             2 : { eapply R_mono; eauto; lia. }

             constructor; auto.
             eapply BStep_letapp_Res with (v := w); eauto.
             destruct (exposed_reflect w0); try contradiction; auto.

             intros.
             split; auto.
             assert (Hw : exposed_res (A1.Res w)) by (eapply bstep_fuel_exposed_inv; eauto); inv Hw; auto.

             eapply bstep_fuel_exposed_inv; eauto.
      + eexists; exists OOT; split; simpl; eauto.
  Qed.

  (* Linking Preservation *)
  Lemma preserves_linking f w x e1 e2 e1' e2' :
    K ! f = None ->
    K ! x = None ->
    (w \in Exposed) ->
    trans_correct_top e1 e2 ->
    trans_correct_top e1' e2' ->
    trans_correct_top (A0.link f x e1 e1') (A1.link f w x e2 e2').
  Proof.
    unfold A0.link, A1.link.
    intros.
    apply Exposed_singleton in H1; subst.
    eapply fun_compat_top; eauto.
    normalize_sets.
    eapply Disjoint_Empty_set_l; eauto.
    eapply letapp_compat_top; eauto.
    normalize_sets.
    eapply Disjoint_Empty_set_l; eauto.
  Qed.

End Known.

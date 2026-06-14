From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

(* miniλANF (without recursion) based on λANF in CertiCoq *)

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
| Vfun : M.t val -> web -> list var -> exp -> val
| Vprim : primitive -> val.

Hint Constructors val : core.

(* Environment *)
Definition env := M.t val.

(* Big-step Reduction *)
Inductive bstep : env -> exp -> val -> Prop :=
| BStep_ret :
  forall {x v ρ},
    M.get x ρ = Some v ->
    bstep ρ (Eret x) v

| BStep_fun :
  forall {ρ f w xs e k v},
    bstep (M.set f (Vfun ρ w xs e) ρ) k v ->
    bstep ρ (Efun f w xs e k) v

| BStep_app :
  forall {ρ f w xs ρ' xs' e vs ρ'' v},
    M.get f ρ = Some (Vfun ρ' w xs' e) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs ρ' = Some ρ'' ->
    bstep ρ'' e v ->
    bstep ρ (Eapp f w xs) v

| BStep_letapp :
  forall {ρ x f w xs k ρ' xs' e vs ρ'' v v'},
    M.get f ρ = Some (Vfun ρ' w xs' e) ->
    get_list xs ρ = Some vs ->
    set_lists xs' vs ρ' = Some ρ'' ->
    bstep ρ'' e v ->
    bstep (M.set x v ρ) k v' ->
    bstep ρ (Eletapp x f w xs k) v'

| BStep_prim_val :
  forall {ρ x p k v},
    bstep (M.set x (Vprim p) ρ) k v ->
    bstep ρ (Eprim_val x p k) v

| BStep_if_true :
  forall {ρ x t e v},
    M.get x ρ = Some (Vprim Ptrue) ->
    bstep ρ t v ->
    bstep ρ (Eif x t e) v

| BStep_if_false :
  forall {ρ x t e v},
    M.get x ρ = Some (Vprim Pfalse) ->
    bstep ρ e v ->
    bstep ρ (Eif x t e) v.

Hint Constructors bstep : core.

Theorem bstep_deterministic : forall {ρ e v v'},
    bstep ρ e v ->
    bstep ρ e v' ->
    v = v'.
Proof.
  intros ρ e v v' H.
  generalize dependent v'.
  induction H; intros v'' H'; inv H';
    repeat subst_exp; auto.

  specialize (IHbstep1 v0 H14).
  inv IHbstep1; subst.
  apply IHbstep2; assumption.
Qed.

(* Typing *)
Inductive ty : Type :=
| Tbool : ty
| Tfun : web -> list ty -> ty -> ty.

Definition listForallP {A : Type} {P : A -> Prop} (allP : forall a : A, P a)
  : forall xs : list A, List.Forall P xs :=
  fix f (xs : list A) : List.Forall P xs :=
    match xs with
    | nil => Forall_nil P
    | cons x xs => Forall_cons x (allP x) (f xs)
    end.

Fixpoint ty_ind_mut
  (P : ty -> Prop)
  (P_Tbool : P Tbool)
  (P_Tfun : forall w Ts T, List.Forall P Ts -> P T -> P (Tfun w Ts T))
  (T : ty) : P T :=
  match T with
  | Tbool => P_Tbool
  | Tfun w Ts T => P_Tfun w Ts T
                    (listForallP (ty_ind_mut P P_Tbool P_Tfun) Ts)
                    (ty_ind_mut P P_Tbool P_Tfun T)
  end.

Definition tenv := M.t ty.

Inductive has_type (Γ : tenv) : exp -> ty -> Prop :=
| HT_ret :
  forall {x T},
    M.get x Γ = Some T ->
    has_type Γ (Eret x) T

| HT_fun :
  forall Ts {f w xs e k Γ' T U},
    set_lists xs Ts Γ = Some Γ' ->
    has_type Γ' e T ->
    has_type (M.set f (Tfun w Ts T) Γ) k U ->
    has_type Γ (Efun f w xs e k) U

| HT_app :
  forall {f w xs Ts T},
    M.get f Γ = Some (Tfun w Ts T) ->
    get_list xs Γ = Some Ts ->
    has_type Γ (Eapp f w xs) T

| HT_letapp :
  forall {x f w xs k Ts T U},
    M.get f Γ = Some (Tfun w Ts T) ->
    get_list xs Γ = Some Ts ->
    has_type (M.set x T Γ) k U ->
    has_type Γ (Eletapp x f w xs k) U

| HT_prim_val :
  forall {x p k T},
    has_type (M.set x Tbool Γ) k T ->
    has_type Γ (Eprim_val x p k) T

| HT_if :
  forall {x t e T},
    M.get x Γ = Some Tbool ->
    has_type Γ t T ->
    has_type Γ e T ->
    has_type Γ (Eif x t e) T.

Hint Constructors has_type : core.

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

Inductive has_web_ty : ty -> Ensemble web :=
| Web_Tfun1 :
  forall w Ts T,
    has_web_ty (Tfun w Ts T) w

| Web_Tfun2 :
  forall w' w Ts T,
    has_web_ty T w' ->
    has_web_ty (Tfun w Ts T) w'

| Web_Tfun3 :
  forall w' w Ts T,
    has_web_tys Ts w' ->
    has_web_ty (Tfun w Ts T) w'

with has_web_tys : list ty -> Ensemble web :=
| Web_hd :
  forall T Ts w,
    has_web_ty T w ->
    has_web_tys (T :: Ts) w

| Web_tl :
  forall T Ts w,
    has_web_tys Ts w ->
    has_web_tys (T :: Ts) w.

Hint Constructors has_web_ty : core.
Hint Constructors has_web_tys : core.

Scheme has_web_ty_mut := Induction for has_web_ty Sort Prop
with has_web_tys_mut := Induction for has_web_tys Sort Prop.

End ANF.

Module Norm.

Import ANF.

(* Logical Relations *)
Definition E' (P : val -> Prop) (ρ : env) (e : exp) : Prop := exists v, bstep ρ e v /\ P v.

Fixpoint V (T : ty) (v : val) : Prop :=
  match T with
  | Tbool => exists p, v = Vprim p

  | Tfun w Ts U =>
      exists ρ' xs e,
        v = Vfun ρ' w xs e /\
        length xs = length Ts /\
        (* need local fix *)
        let fix Forall2_aux (Ts : list ty) (vs : list val) : Prop :=
          match Ts, vs with
          | [], [] => True
          | T :: Ts', v :: vs' => V T v /\ Forall2_aux Ts' vs'
          | _, _ => False
          end
        in forall us ρ'',
            Forall2_aux Ts us ->
            set_lists xs us ρ' = Some ρ'' ->
            E' (V U) ρ'' e
  end.

Definition ForallV Ts vs : Prop :=
  (fix Forall2_aux (Ts : list ty) (vs : list val) : Prop :=
     match Ts, vs with
     | [], [] => True
     | T :: Ts', v :: vs' => V T v /\ Forall2_aux Ts' vs'
     | _, _ => False
     end) Ts vs.

Notation E T := (E' (V T)).

(* Environment Relation *)
Definition G Γ ρ := forall x T, M.get x Γ = Some T ->
                           exists v, M.get x ρ = Some v /\ V T v.

Definition has_semantic_type Γ e T := forall ρ, G Γ ρ -> E T ρ e.

(* Environment Lemmas *)
Lemma G_set {Γ ρ}:
  G Γ ρ ->
  forall {x T v},
    V T v ->
    G (M.set x T Γ) (M.set x v ρ).
Proof.
  unfold G.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - rewrite M.gss in *.
    inv H1; eauto.
  - rewrite M.gso in *; auto.
Qed.

Lemma G_set_lists {Γ ρ}:
  G Γ ρ ->
  forall {xs Ts us Γ' ρ'},
    ForallV Ts us ->
    set_lists xs Ts Γ = Some Γ' ->
    set_lists xs us ρ = Some ρ' ->
    G Γ' ρ'.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct Ts; destruct us; try discriminate.
    inv H0; inv H1; auto.
  - destruct Ts; destruct us; try discriminate.
    destruct (set_lists xs Ts Γ) eqn:Heq1;
      destruct (set_lists xs us ρ) eqn:Heq2;
      try discriminate.
    inv H0; inv H1.
    destruct H.
    destruct (M.elt_eq x a); subst.
    + rewrite M.gss in *.
      inv H2; eauto.
    + rewrite M.gso in *; eauto.
Qed.

Lemma G_get_list {Γ ρ} :
  G Γ ρ ->
  forall {xs Ts},
    get_list xs Γ = Some Ts ->
    exists vs,
      get_list xs ρ = Some vs /\
      ForallV Ts vs.
Proof.
  unfold G.
  intros H xs.
  induction xs; simpl; intros.
  - inv H0.
    eexists; split; eauto; simpl; eauto.
  - destruct (Γ ! a) eqn:Heq1; try discriminate.
    destruct (H a t) as [v [Hv Vv]]; auto.
    destruct (get_list xs Γ); inv H0.
    destruct (IHxs l) as [vs [Heqvs Hvs]]; auto.
    exists (v :: vs).
    rewrite Hv.
    rewrite Heqvs.
    split; simpl; eauto.
Qed.

(* Compatibility Lemmas *)
Lemma ret_compat {Γ x T}:
  M.get x Γ = Some T ->
  has_semantic_type Γ (Eret x) T.
Proof.
  unfold has_semantic_type, G, E.
  intros.
  destruct (H0 _ _ H) as [v [Heqv Vv]]; eauto.
Qed.

Lemma fun_compat {Γ Γ' f w xs e T Ts U k} :
  set_lists xs Ts Γ = Some Γ' ->
  has_semantic_type Γ' e T ->
  has_semantic_type (M.set f (Tfun w Ts T) Γ) k U ->
  has_semantic_type Γ (Efun f w xs e k) U.
Proof.
  unfold has_semantic_type.
  intros.
  destruct (H1 (M.set f (Vfun ρ w xs e) ρ)) as [v [kv Vv]].
  - apply G_set; auto.
    simpl.
    exists ρ; exists xs; exists e; repeat split; auto.
    + eapply set_lists_length_eq; eauto.
    + intros.
      apply H0.
      eapply G_set_lists; eauto.
  - unfold E; eauto.
Qed.

Lemma app_compat {Γ f w xs Ts T} :
  M.get f Γ = Some (Tfun w Ts T) ->
  get_list xs Γ = Some Ts ->
  has_semantic_type Γ (Eapp f w xs) T.
Proof.
  unfold has_semantic_type.
  intros.
  unfold G in H1.
  destruct (H1 _ _ H) as [fv [Heqfv Vfv]].
  destruct Vfv as [ρ' [xs' [e' [Heqfv' [Hlen HF]]]]]; subst.
  destruct (G_get_list H1 H0) as [vs [Heqvs Hvs]].
  destruct (set_lists_length3 ρ' xs' vs) as [ρ'' Heqρ''].
  {
    rewrite <- (get_list_length_eq _ _ _ H0) in Hlen.
    rewrite <- (get_list_length_eq _ _ _ Heqvs).
    auto.
  }
  destruct (HF vs ρ'') as [u [e'u Vu]]; auto.
  exists u; split; eauto.
Qed.

Lemma letapp_compat {Γ x f w xs k U Ts T}:
  M.get f Γ = Some (Tfun w Ts T) ->
  get_list xs Γ = Some Ts ->
  has_semantic_type (M.set x T Γ) k U ->
  has_semantic_type Γ (Eletapp x f w xs k) U.
Proof.
  intros.
  specialize (app_compat H H0); intros.
  unfold has_semantic_type in *.
  intros.
  destruct (H2 _ H3) as [v [Rv Vv]].
  destruct (H1 (M.set x v ρ)) as [u [ku Vu]].
  - apply G_set; auto.
  - inv Rv.
    exists u; split; auto.
    econstructor; eauto.
Qed.

Lemma prim_val_compat {Γ T x p k} :
  has_semantic_type (M.set x Tbool Γ) k T ->
  has_semantic_type Γ (Eprim_val x p k) T.
Proof.
  unfold has_semantic_type, E.
  intros.
  destruct (H (M.set x (Vprim p) ρ)) as [v [kv Vv]]; eauto.
  apply G_set; simpl; eauto.
Qed.

Lemma if_compat {Γ T x e t} :
  M.get x Γ = Some Tbool ->
  has_semantic_type Γ t T ->
  has_semantic_type Γ e T ->
  has_semantic_type Γ (Eif x t e) T.
Proof.
  unfold has_semantic_type, E, G.
  intros.
  destruct (H2 x Tbool) as [v [Heqv Vv]]; auto.
  destruct Vv as [p Heqp]; subst.
  destruct p.
  - destruct (H0 _ H2) as [u [Hequ Vu]]; eauto.
  - destruct (H1 _ H2) as [u [Hequ Vu]]; eauto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {Γ e T} :
  has_type Γ e T -> has_semantic_type Γ e T.
Proof.
  intros.
  induction H.
  - apply ret_compat; auto.
  - eapply fun_compat; eauto.
  - eapply app_compat; eauto.
  - eapply letapp_compat; eauto.
  - apply prim_val_compat; auto.
  - apply if_compat; auto.
Qed.

Theorem normalization {e T} :
    has_type (M.empty ty) e T -> exists v, bstep (M.empty val) e v.
Proof.
  intros.

  assert (G' : G (M.empty ty) (M.empty val)).
  unfold G; intros x U Heq; inv Heq.

  destruct (fundamental_property H (M.empty val) G') as [u [ev uV]]; eauto.
Qed.

End Norm.

Module Refl.

Import ANF.

(* Logical Relations *)
Definition E' (P : val -> val -> Prop) (ρ1 : env) (e1 : exp) (ρ2 : env) (e2 : exp) : Prop :=
  exists v1 v2,
    bstep ρ1 e1 v1 /\
    bstep ρ2 e2 v2 /\
    P v1 v2.

Fixpoint V (T : ty) (v1 : val) (v2 : val) : Prop :=
  match T with
  | Tbool =>
      exists p,
        v1 = Vprim p /\
        v2 = Vprim p

  | Tfun w Ts U =>
      exists ρ1' xs1 e1
        ρ2' xs2 e2,
        v1 = Vfun ρ1' w xs1 e1 /\
        v2 = Vfun ρ2' w xs2 e2 /\
        length Ts = length xs1 /\
        length Ts = length xs2 /\
        (* need local fix *)
        let fix ForallV (Ts : list ty) (vs1 : list val) (vs2 : list val) : Prop :=
          match Ts, vs1, vs2 with
          | [], [], [] => True
          | T :: Ts', v1 :: vs1', v2 :: vs2' => V T v1 v2 /\ ForallV Ts' vs1' vs2'
          | _, _, _ => False
          end
        in forall us1 us2 ρ1'' ρ2'',
            ForallV Ts us1 us2 ->
            set_lists xs1 us1 ρ1' = Some ρ1'' ->
            set_lists xs2 us2 ρ2' = Some ρ2'' ->
            E' (V U) ρ1'' e1 ρ2'' e2
  end.

Definition ForallV Ts vs1 vs2 : Prop :=
  (fix ForallV (Ts : list ty) (vs1 : list val) (vs2 : list val) : Prop :=
     match Ts, vs1, vs2 with
     | [], [], [] => True
     | T :: Ts', v1 :: vs1', v2 :: vs2' => V T v1 v2 /\ ForallV Ts' vs1' vs2'
     | _, _, _ => False
     end) Ts vs1 vs2.

Notation E T := (E' (V T)).

(* Environment Relation *)
Definition G Γ ρ1 ρ2 :=
  forall x T,
    M.get x Γ = Some T ->
    exists v1 v2,
      M.get x ρ1 = Some v1 /\
      M.get x ρ2 = Some v2 /\
      V T v1 v2.

Definition contextual_equivalent Γ e1 e2 T := forall ρ1 ρ2, G Γ ρ1 ρ2 -> E T ρ1 e1 ρ2 e2.

(* Environment Lemmas *)
Lemma G_set {Γ ρ1 ρ2}:
  G Γ ρ1 ρ2 ->
  forall {x T v1 v2},
    V T v1 v2 ->
    G (M.set x T Γ) (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  unfold G.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss in *.
    inv H1; eauto.
  - rewrite M.gso in *; auto.
    rewrite M.gso; auto.
Qed.

Lemma G_set_lists {Γ ρ1 ρ2}:
  G Γ ρ1 ρ2 ->
  forall {xs Ts vs1 vs2 Γ' ρ1' ρ2'},
    ForallV Ts vs1 vs2 ->
    set_lists xs Ts Γ = Some Γ' ->
    set_lists xs vs1 ρ1 = Some ρ1' ->
    set_lists xs vs2 ρ2 = Some ρ2' ->
    G Γ' ρ1' ρ2'.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - destruct Ts; destruct vs1; destruct vs2; try discriminate.
    inv H0; inv H1; inv H2; auto.
  - destruct Ts; destruct vs1; destruct vs2; try discriminate.
    destruct (set_lists xs Ts Γ) eqn:Heq1;
      destruct (set_lists xs vs1 ρ1) eqn:Heq2;
      destruct (set_lists xs vs2 ρ2) eqn:Heq3;
      try discriminate.
    inv H0; inv H1; inv H2.
    destruct H.
    destruct (M.elt_eq x a); subst.
    + repeat rewrite M.gss in *.
      inv H3; eauto.
    + rewrite M.gso in *; auto.
      rewrite M.gso; eauto.
Qed.

Lemma G_get_list {Γ ρ1 ρ2} :
  G Γ ρ1 ρ2 ->
  forall {xs Ts},
    get_list xs Γ = Some Ts ->
    exists vs1 vs2,
      get_list xs ρ1 = Some vs1 /\
      get_list xs ρ2 = Some vs2 /\
      ForallV Ts vs1 vs2.
Proof.
  unfold G.
  intros H xs.
  induction xs; simpl; intros.
  - inv H0.
    eexists; eexists; repeat split; eauto; simpl; eauto.
  - destruct (Γ ! a) eqn:Heq1; try discriminate.
    destruct (H a t) as [v1 [v2 [Hv1 [Hv2 Vv]]]]; auto.
    destruct (get_list xs Γ); inv H0.
    destruct (IHxs l) as [vs1 [vs2 [Heqvs1 [Heqvs2 Hvs]]]]; auto.
    exists (v1 :: vs1); exists (v2 :: vs2).
    rewrite Hv1; rewrite Hv2.
    rewrite Heqvs1; rewrite Heqvs2.
    repeat split; auto.
Qed.

(* Compatibility Lemmas *)
Lemma ret_compat {Γ x T}:
  M.get x Γ = Some T ->
  contextual_equivalent Γ (Eret x) (Eret x) T.
Proof.
  unfold contextual_equivalent, G, E.
  intros.
  destruct (H0 _ _ H) as [v1 [v2 [Heqv1 [Heqv2 Vv]]]].
  exists v1; exists v2; repeat split; auto.
Qed.

Lemma fun_compat {Γ Γ' f w xs e T Ts U k} :
  set_lists xs Ts Γ = Some Γ' ->
  contextual_equivalent Γ' e e T ->
  contextual_equivalent (M.set f (Tfun w Ts T) Γ) k k U ->
  contextual_equivalent Γ (Efun f w xs e k) (Efun f w xs e k) U.
Proof.
  unfold contextual_equivalent.
  intros.
  destruct (H1 (M.set f (Vfun ρ1 w xs e) ρ1) (M.set f (Vfun ρ2 w xs e) ρ2)) as [v1 [v2 [kv1 [kv2 Vv]]]].
  - apply G_set; auto.
    simpl.
    exists ρ1; exists xs; exists e;
      exists ρ2; exists xs; exists e;
      repeat split; auto.
    + symmetry; eapply set_lists_length_eq; eauto.
    + symmetry; eapply set_lists_length_eq; eauto.
    + intros.
      apply H0.
      eapply G_set_lists; eauto.
  - unfold E.
    exists v1; exists v2; repeat split; auto.
Qed.

Lemma app_compat {Γ f w xs Ts T} :
  M.get f Γ = Some (Tfun w Ts T) ->
  get_list xs Γ = Some Ts ->
  contextual_equivalent Γ (Eapp f w xs) (Eapp f w xs) T.
Proof.
  unfold contextual_equivalent.
  intros.
  unfold G in H1.
  destruct (H1 _ _ H) as [fv1 [fv2 [Heqfv1 [Heqfv2 Vfv]]]].
  simpl in Vfv.
  destruct Vfv as [ρ1' [xs1' [e1' [ρ2' [xs2' [e2' [Heqfv1' [Heqfv2' [Hlen1 [Hlen2 HF]]]]]]]]]]; subst.
  destruct (G_get_list H1 H0) as [vs1 [vs2 [Heqvs1 [Heqvs2 Hvs]]]].
  destruct (set_lists_length3 ρ1' xs1' vs1) as [ρ1'' Heqρ1''].
  {
    rewrite <- (get_list_length_eq _ _ _ H0) in Hlen1.
    rewrite <- (get_list_length_eq _ _ _ Heqvs1).
    auto.
  }
  destruct (set_lists_length3 ρ2' xs2' vs2) as [ρ2'' Heqρ2''].
  {
    rewrite <- (get_list_length_eq _ _ _ H0) in Hlen2.
    rewrite <- (get_list_length_eq _ _ _ Heqvs2).
    auto.
  }

  destruct (HF vs1 vs2 ρ1'' ρ2'') as [u1 [u2 [e'u1 [e'u2 Vu]]]]; auto.
  exists u1; exists u2; repeat split; eauto.
Qed.

Lemma letapp_compat {Γ x f w xs k U Ts T}:
  M.get f Γ = Some (Tfun w Ts T) ->
  get_list xs Γ = Some Ts ->
  contextual_equivalent (M.set x T Γ) k k U ->
  contextual_equivalent Γ (Eletapp x f w xs k) (Eletapp x f w xs k) U.
Proof.
  intros.
  specialize (app_compat H H0); intros.
  unfold contextual_equivalent in *.
  intros.
  destruct (H2 _ _ H3) as [v1 [v2 [Rv1 [Rv2 Vv]]]].
  destruct (H1 (M.set x v1 ρ1) (M.set x v2 ρ2)) as [u1 [u2 [ku1 [ku2 Vu]]]].
  - apply G_set; auto.
  - inv Rv1.
    inv Rv2.
    exists u1; exists u2; repeat split; auto;
      econstructor; eauto.
Qed.

Lemma prim_val_compat {Γ T x p k} :
  contextual_equivalent (M.set x Tbool Γ) k k T ->
  contextual_equivalent Γ (Eprim_val x p k) (Eprim_val x p k) T.
Proof.
  unfold contextual_equivalent, E.
  intros.
  destruct (H (M.set x (Vprim p) ρ1) (M.set x (Vprim p) ρ2)) as [v1 [v2 [kv1 [kv2 Vv]]]]; eauto.
  apply G_set; simpl; eauto.
  exists v1; exists v2; repeat split; auto.
Qed.

Lemma if_compat {Γ T x e t} :
  M.get x Γ = Some Tbool ->
  contextual_equivalent Γ t t T ->
  contextual_equivalent Γ e e T ->
  contextual_equivalent Γ (Eif x t e) (Eif x t e ) T.
Proof.
  unfold contextual_equivalent, E, G.
  intros.
  destruct (H2 x Tbool) as [v1 [v2 [Heqv1 [Heqv2 Vv]]]]; auto.
  destruct Vv as [p [Heqp1 Heqp2]]; subst.
  destruct p.
  - destruct (H0 _ _ H2) as [u1 [u2 [Hequ1 [Hequ2 Vu]]]].
    exists u1; exists u2; repeat split; eauto.
  - destruct (H1 _ _ H2) as [u1 [u2 [Hequ1 [Hequ2 Vu]]]].
    exists u1; exists u2; repeat split; eauto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {Γ e T} :
  has_type Γ e T -> contextual_equivalent Γ e e T.
Proof.
  intros.
  induction H.
  - apply ret_compat; auto.
  - eapply fun_compat; eauto.
  - eapply app_compat; eauto.
  - eapply letapp_compat; eauto.
  - apply prim_val_compat; auto.
  - apply if_compat; auto.
Qed.

End Refl.

Module DPE.

Import ANF.

(* Map from web identifier to the live parameter list *)
Definition live_map : Type := M.t (list bool).

Inductive wf_ty (L : live_map) : ty -> Prop :=
| LM_Tbool :
  wf_ty L Tbool

| LM_Tfun :
  forall Ts T w bs,
    M.get w L = Some bs ->
    length bs = length Ts ->
    wf_ty L T ->
    wf_tys L Ts ->
    wf_ty L (Tfun w Ts T)

with wf_tys (L : live_map) : list ty -> Prop :=
| LM_nil :
  wf_tys L []

| LM_cons :
  forall T Ts,
    wf_ty L T ->
    wf_tys L Ts ->
    wf_tys L (T :: Ts).

Hint Constructors wf_ty : core.
Hint Constructors wf_tys : core.

Scheme wf_ty_mut := Induction for wf_ty Sort Prop
with wf_tys_mut := Induction for wf_tys Sort Prop.

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
Inductive elim_ty (L : live_map) : ty -> ty -> Prop :=
| Elim_Tbool :
  elim_ty L Tbool Tbool

| Elim_Tfun :
  forall {w Ts T Us U bs},
    M.get w L = Some bs ->
    length Ts = length bs ->
    elim_ty L T U ->
    elim_tys L Ts Us ->
    elim_ty L (Tfun w Ts T) (Tfun w (live_args Us bs) U)

with elim_tys (L : live_map) : list ty -> list ty -> Prop :=
| elim_tys_nil :
  elim_tys L [] []

| elim_tys_cons :
  forall {T Ts U Us},
    elim_ty L T U ->
    elim_tys L Ts Us ->
    elim_tys L (T :: Ts) (U :: Us).

Hint Constructors elim_ty : core.
Hint Constructors elim_tys : core.

Scheme elim_ty_mut := Induction for elim_ty Sort Prop
with elim_tys_mut := Induction for elim_tys Sort Prop.

Inductive elim_exp (L : live_map) (Γ : tenv) : exp -> ty -> exp -> Prop :=
| Elim_ret :
  forall {x T},
    M.get x Γ = Some T ->
    wf_ty L T ->
    elim_exp L Γ (Eret x) T (Eret x)

| Elim_fun :
  forall Ts {f w xs e k U T bs e' k' Γ'},
    set_lists xs Ts Γ = Some Γ' ->
    elim_exp L Γ' e T e' ->
    wf_tys L Ts ->
    elim_exp L (M.set f (Tfun w Ts T) Γ) k U k' ->

    M.get w L = Some bs ->
    length xs = length bs ->

    NoDup xs ->
    Disjoint _ (FromList xs) (Dom_map Γ) ->
    elim_exp L Γ (Efun f w xs e k) U (Efun f w (live_args xs bs) e' k')

| Elim_app :
  forall {f w xs bs Ts T},
    M.get f Γ = Some (Tfun w Ts T) ->
    get_list xs Γ = Some Ts ->

    M.get w L = Some bs ->
    length xs = length bs ->
    wf_ty L (Tfun w Ts T) ->
    elim_exp L Γ (Eapp f w xs) T (Eapp f w (live_args xs bs))

| Elim_letapp :
  forall {x f w xs k bs k' Ts T U},
    M.get f Γ = Some (Tfun w Ts T) ->
    get_list xs Γ = Some Ts ->
    elim_exp L (M.set x T Γ) k U k' ->

    M.get w L = Some bs ->
    length xs = length bs ->
    wf_ty L (Tfun w Ts T) ->
    elim_exp L Γ (Eletapp x f w xs k) U (Eletapp x f w (live_args xs bs) k')

| Elim_prim_val :
  forall {x p k k' T},
    elim_exp L (M.set x Tbool Γ) k T k' ->
    elim_exp L Γ (Eprim_val x p k) T (Eprim_val x p k')

| Elim_if :
  forall {x t e t' e' T},
    M.get x Γ = Some Tbool ->
    elim_exp L Γ t T t' ->
    elim_exp L Γ e T e' ->
    elim_exp L Γ (Eif x t e) T (Eif x t' e').

Hint Constructors elim_exp : core.

(* Logical Relations *)
Definition E' (P : val -> val -> Prop) (ρ1 : env) (e1 : exp) (ρ2 : env) (e2 : exp) : Prop :=
  exists v1 v2,
    bstep ρ1 e1 v1 /\
    bstep ρ2 e2 v2 /\
    P v1 v2.

Fixpoint V (L : live_map) (T : ty) (v1 : val) (v2 : val) : Prop :=
  match T with
  | Tbool =>
      exists p,
        v1 = Vprim p /\
        v2 = Vprim p

  | Tfun w Ts T =>
      exists ρ1' xs1 e1
        ρ2' xs2 e2 bs,

        M.get w L = Some bs /\

        (* webs stay the same *)
        v1 = Vfun ρ1' w xs1 e1 /\
        v2 = Vfun ρ2' w xs2 e2 /\

        xs2 = live_args xs1 bs /\
        length Ts = length xs1 /\
        length xs1 = length bs /\

        (* need local fix *)
        let fix ForallV (Ts : list ty) (vs1 : list val) (bs : list bool) (vs2 : list val) : Prop :=
          match bs, Ts, vs1 with
          | [], [], [] => vs2 = []
          | b :: bs', T :: Ts', v1 :: vs1' =>
              if b
              then match vs2 with
                   | [] => False
                   | v2 :: vs2' => V L T v1 v2 /\ ForallV Ts' vs1' bs' vs2'
                   end
              else ForallV Ts' vs1' bs' vs2
          | _, _, _ => False
          end
        in forall us1 us2 ρ1'' ρ2'',
            ForallV Ts us1 bs us2 -> (* only live args matter *)
            set_lists xs1 us1 ρ1' = Some ρ1'' ->
            set_lists xs2 us2 ρ2' = Some ρ2'' ->
            E' (V L T) ρ1'' e1 ρ2'' e2
  end.

Definition ForallV L Ts vs1 bs vs2 : Prop :=
  (fix ForallV (Ts : list ty) (vs1 : list val) (bs : list bool) (vs2 : list val) : Prop :=
     match bs, Ts, vs1 with
     | [], [], [] => vs2 = []
     | b :: bs', T :: Ts', v1 :: vs1' =>
         if b
         then match vs2 with
              | [] => False
              | v2 :: vs2' => V L T v1 v2 /\ ForallV Ts' vs1' bs' vs2'
              end
         else ForallV Ts' vs1' bs' vs2
     | _, _, _ => False
     end) Ts vs1 bs vs2.

Notation E L T := (E' (V L T)).

(* Environment Relations *)
Definition Elim_env L Γ1 Γ2 :=
  forall x T1,
    M.get x Γ1 = Some T1 ->
    forall T2,
      M.get x Γ2 = Some T2 ->
      elim_ty L T1 T2.

Definition G L (Γ1 : tenv) (Γ2 : tenv) ρ1 ρ2 :=
  forall x T1,
    M.get x Γ1 = Some T1 ->
    exists v1,
      M.get x ρ1 = Some v1 /\
        forall T2,
          M.get x Γ2 = Some T2 ->
          exists v2,
            M.get x ρ2 = Some v2 /\
            V L T1 v1 v2.

Definition elim_correct L Γ1 e1 e2 T1 :=
  has_type Γ1 e1 T1 /\
  wf_ty L T1 /\
  (forall Γ2 T2,
      Elim_env L Γ1 Γ2 ->
      elim_ty L T1 T2 ->
      (occurs_free e2) \subset (Dom_map Γ2) ->
      (Dom_map Γ2) \subset (Dom_map Γ1) ->
      (has_type Γ2 e2 T2 /\
       forall ρ1 ρ2,
         G L Γ1 Γ2 ρ1 ρ2 ->
         E L T1 ρ1 e1 ρ2 e2)).

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

(* Lemmas about [elim_ty], [elim_tys], and [Elim_env] *)
Lemma elim_ty_exists : forall {L T},
    wf_ty L T ->
    exists T', elim_ty L T T'.
Proof.
  intro L.
  eapply wf_ty_mut with (L := L)
                        (P := fun T S => exists T', elim_ty L T T')
                        (P0 := fun Ts S => exists Ts', elim_tys L Ts Ts'); intros; eauto.
  - destruct H as [T' ET'].
    destruct H0 as [Ts' ETs'].
    exists (Tfun w (live_args Ts' bs) T'); auto.
  - destruct H as [T' ET'].
    destruct H0 as [Ts' ETs']; eauto.
Qed.

Lemma elim_tys_exists {L Ts}:
  wf_tys L Ts ->
  exists Ts', elim_tys L Ts Ts'.
Proof.
  intros.
  induction H; eauto.
  destruct IHwf_tys as [Ts' ETs'].
  destruct (elim_ty_exists H) as [T' ET'].
  eauto.
Qed.

Lemma elim_tys_length {L Ts Ts'}:
  elim_tys L Ts Ts' ->
  length Ts = length Ts'.
Proof.
  intros.
  induction H; simpl; auto.
Qed.

Lemma elim_ty_deterministic {T L T1 T2} :
  elim_ty L T T1 ->
  elim_ty L T T2 ->
  T1 = T2.
Proof.
  intros H.
  revert T2.
  eapply elim_ty_mut with (L := L)
                          (P := fun T T1 e => forall T2, elim_ty L T T2 -> T1 = T2)
                          (P0 := fun Ts Ts1 e => forall Ts2, elim_tys L Ts Ts2 -> Ts1 = Ts2);
    intros.
  - inv H0; reflexivity.
  - inv H2.
    rewrite e in H6.
    inv H6.
    rewrite (H0 _ H9).
    rewrite (H1 _ H10).
    reflexivity.
  - inv H0; reflexivity.
  - inv H2.
    rewrite (H0 _ H5).
    rewrite (H1 _ H7).
    reflexivity.
  - assumption.
Qed.

Lemma elim_tys_deterministic {Ts L Ts1 Ts2} :
  elim_tys L Ts Ts1 ->
  elim_tys L Ts Ts2 ->
  Ts1 = Ts2.
Proof.
  intro H.
  revert Ts2.
  induction H; intros.
  - inv H; auto.
  - inv H1.
    erewrite IHelim_tys; eauto.
    erewrite elim_ty_deterministic; eauto.
Qed.

Lemma elim_tys_live_args {L} : forall {bs Ts1 Ts2},
    elim_tys L Ts1 Ts2 ->
    length Ts1 = length bs ->
    elim_tys L (live_args Ts1 bs) (live_args Ts2 bs).
Proof.
  intros.
  generalize dependent bs.
  induction H; simpl; intros.
  - destruct bs; simpl; auto.
  - destruct bs; simpl in *; inv H1.
    destruct b; eauto.
Qed.

(* Environment Lemmas *)
Lemma Elim_env_set {L T T'} :
  elim_ty L T T' ->
  forall {Γ Γ'} x,
    Elim_env L Γ Γ' ->
    Elim_env L (M.set x T Γ) (M.set x T' Γ').
Proof.
  unfold Elim_env.
  intros.
  destruct (M.elt_eq x x0); subst.
  - repeat rewrite M.gss in *; auto.
    inv H1; inv H2; eauto.
  - rewrite M.gso in *; auto.
    eapply H0; eauto.
Qed.

Lemma G_set {L Γ1 Γ2 ρ1 ρ2}:
  G L Γ1 Γ2 ρ1 ρ2 ->
  forall x T1 T2 v1 v2,
    V L T1 v1 v2 ->
    G L (M.set x T1 Γ1) (M.set x T2 Γ2) (M.set x v1 ρ1) (M.set x v2 ρ2).
Proof.
  unfold G, Dom_map, Ensembles.Included, Ensembles.In.
  intros.
  destruct (M.elt_eq x0 x); subst.
  - repeat rewrite M.gss in *; auto.
    inv H1.
    eexists; split; auto.
    intros.
    inv H1.
    eexists; split; auto.
  - rewrite M.gso in *; auto.
    rewrite M.gso; auto.
    rewrite M.gso; eauto.
Qed.

Lemma Dom_map_set_subset {Γ1 Γ2 : tenv} {x T1 T2}:
  (Dom_map Γ1) \subset (Dom_map Γ2) ->
  (Dom_map (M.set x T1 Γ1)) \subset (Dom_map (M.set x T2 Γ2)).
Proof.
  intros.
  apply Included_trans with (x |: Dom_map Γ1).
  apply Dom_map_set.
  apply Included_trans with (x |: Dom_map Γ2).
  apply Included_Union_compat; auto.
  apply Included_refl.
  apply Dom_map_set.
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

Lemma Elim_env_set_lists {L Γ1 Γ2}:
  Elim_env L Γ1 Γ2 ->
  (Dom_map Γ2) \subset (Dom_map Γ1) ->
  forall {xs Ts1 Ts2 bs Γ3 Γ4},
    elim_tys L Ts1 Ts2 ->
    set_lists xs Ts1 Γ1 = Some Γ3 ->
    set_lists (live_args xs bs) (live_args Ts2 bs) Γ2 = Some Γ4 ->
    Disjoint _ (FromList xs) (Dom_map Γ1) ->
    NoDup xs ->
    length xs = length bs ->
    Elim_env L Γ3 Γ4.
Proof.
  intros HE HS xs.
  induction xs; simpl; intros.
  - destruct Ts1; try discriminate.
    inv H; inv H0.
    destruct bs; simpl in *;
      inv H1; auto.
  - destruct Ts1; try discriminate.
    destruct (set_lists xs Ts1 Γ1) eqn:Heq1; try discriminate.
    inv H; inv H0; inv H3.
    destruct bs; simpl in *; inv H4.
    destruct b; simpl in *.
    + destruct (set_lists (live_args xs bs) (live_args Us bs) Γ2) eqn:Heq2; try discriminate.
      inv H1.
      apply Elim_env_set; auto.
      eapply IHxs; eauto.
      apply Disjoint_FromList_cons in H2; auto.
    + unfold Elim_env.
      intros.
      destruct (M.elt_eq a x); subst.
      * exfalso.
        unfold Ensembles.In, FromList, Dom_map in H3.
        inv H2.
        apply (H4 x).
        constructor; unfold Ensembles.In, FromList.
        apply in_eq.
        apply HS.
        specialize (live_args_not_In bs H5); intros.
        rewrite <- (set_lists_not_In _ _ _ _ _ H1 H2) in H3.
        unfold Ensembles.In, FromList, Dom_map in *.
        eauto.
      * rewrite M.gso in *; auto.
        unfold Elim_env in *.
        eapply IHxs; eauto.
        apply Disjoint_FromList_cons in H2; auto.
Qed.

Lemma G_set_lists {L Γ1 Γ2 ρ1 ρ2}:
  G L Γ1 Γ2 ρ1 ρ2 ->
  (Dom_map Γ2) \subset (Dom_map Γ1) ->
  forall {xs Ts1 Ts2 bs vs1 vs2 Γ3 Γ4 ρ3 ρ4},
    ForallV L Ts1 vs1 bs vs2 ->
    set_lists xs Ts1 Γ1 = Some Γ3 ->
    elim_tys L Ts1 Ts2 ->
    set_lists (live_args xs bs) (live_args Ts2 bs) Γ2 = Some Γ4 ->
    set_lists xs vs1 ρ1 = Some ρ3 ->
    set_lists (live_args xs bs) vs2 ρ2 = Some ρ4 ->
    Disjoint _ (FromList xs) (Dom_map Γ1) ->
    NoDup xs ->
    length xs = length bs ->
    G L Γ3 Γ4 ρ3 ρ4.
Proof.
  intros HG HS xs.
  induction xs; simpl; intros.
  - destruct Ts1; try discriminate.
    destruct vs1; try discriminate.
    inv H0; inv H1; inv H3.
    destruct bs; try contradiction.
    simpl in *.
    inv H2; inv H4; auto.
  - destruct Ts1; try discriminate.
    destruct vs1; try discriminate.
    destruct (set_lists xs Ts1 Γ1) eqn:Heq1; try discriminate.
    destruct (set_lists xs vs1 ρ1) eqn:Heq2; try discriminate.
    inv H0; inv H1; inv H3; inv H5; inv H6.
    destruct bs; try contradiction.
    simpl in *.
    destruct b; simpl in *.
    + destruct vs2; try contradiction.
      destruct H.
      destruct (set_lists (live_args xs bs) (live_args Us bs)) eqn:Heq3; try discriminate.
      destruct (set_lists (live_args xs bs) vs2 ρ2) eqn:Heq4; try discriminate.
      inv H2; inv H4.
      apply G_set; eauto.
      eapply IHxs; eauto.
      eapply Disjoint_FromList_cons; eauto.
      constructor; eauto.
    + assert (G L t0 Γ4 t1 ρ4).
      {
        eapply IHxs; eauto.
        eapply Disjoint_FromList_cons; eauto.
        constructor; eauto.
      }
      unfold G in *.
      intros.
      destruct (M.elt_eq a x); subst.
      * rewrite M.gss; auto.
        eexists; split; auto.
        intros.
        exfalso.
        apply (live_args_not_In bs) in H5.
        rewrite <- (set_lists_not_In _ _ _ _ _ H2 H5) in H6.
        unfold Ensembles.Included, Ensembles.In, FromList, Dom_map in *.
        edestruct HS as [T1' HeqT1']; eauto.
        apply (H0 x).
        constructor; unfold Ensembles.In; eauto.
        apply in_eq.
      * rewrite M.gso in *; auto.
Qed.

Lemma Elim_env_get {L Γ1 Γ2 x T1 T2} :
  Elim_env L Γ1 Γ2 ->
  M.get x Γ1 = Some T1 ->
  M.get x Γ2 = Some T2 ->
  elim_ty L T1 T2.
Proof.
  unfold Elim_env.
  intros; eapply H; eauto.
Qed.

(* Compatibility Lemmas *)
Lemma ret_compat {L Γ x T}:
  M.get x Γ = Some T ->
  wf_ty L T ->
  elim_correct L Γ (Eret x) (Eret x) T.
Proof.
  unfold elim_correct, G, E, Dom_map, Ensembles.Included, Ensembles.In.
  intros.
  split; auto.
  split; auto.
  intros.
  destruct (H3 x) as [Tx HeqTx]; auto.
  split; intros.
  - constructor.
    specialize (Elim_env_get H1 H HeqTx); intros.
    rewrite (elim_ty_deterministic H2 H5); auto.
  - edestruct H5 as [v1 [v2 [Hv1 [Hv2 Vv]]]]; eauto.
    eexists; eexists; repeat split; eauto.
Qed.

Lemma prim_val_compat {Γ L T x p k k'} :
  elim_correct L (M.set x Tbool Γ) k k' T ->
  elim_correct L Γ (Eprim_val x p k) (Eprim_val x p k') T.
Proof.
  unfold elim_correct.
  intros.
  destruct H as [Hk [HWF HG]].
  split; auto.
  split; auto.
  intros.

  assert (HFk' : occurs_free k' \subset x |: Dom_map Γ2).
  {
    unfold Ensembles.Included, Ensembles.In, Dom_map in *.
    intros.
    destruct (M.elt_eq x x0); subst.
    - apply Union_introl; auto.
    - apply Union_intror; eauto.
  }

  edestruct (HG (M.set x Tbool Γ2) T2) as [HTk' Hk']; eauto.
  - eapply Elim_env_set; eauto.
  - apply Included_trans with (x |: Dom_map Γ2); auto.
    eapply Dom_map_set.
  - apply Dom_map_set_subset; auto.
  - split; auto; intros.
    edestruct (HG (M.set x Tbool Γ2) T2) as [_ [v1 [v2 [kv1 [kv2 Vv]]]]]; eauto.
    + apply Elim_env_set; auto.
    + apply Included_trans with (x |: Dom_map Γ2); auto.
      eapply Dom_map_set.
    + apply Dom_map_set_subset; auto.
    + eapply G_set; eauto.
      simpl; eauto.
    + exists v1, v2; repeat split; eauto.
Qed.

Lemma fun_compat {L Γ Γ' e e' T f w xs Ts U k k' bs} :
  set_lists xs Ts Γ = Some Γ' ->
  elim_correct L Γ' e e' T ->
  wf_tys L Ts ->
  elim_correct L (M.set f (Tfun w Ts T) Γ) k k' U ->

  M.get w L = Some bs ->
  length xs = length bs ->

  NoDup xs ->
  Disjoint _ (FromList xs) (Dom_map Γ) ->

  elim_correct L Γ (Efun f w xs e k) (Efun f w (live_args xs bs) e' k') U.
Proof.
  unfold elim_correct.
  intros.
  destruct H0 as [He [HWT HGe]].
  destruct H2 as [Hk [HWU HGk]].
  split; eauto.
  split; eauto.
  intros.
  destruct (elim_ty_exists HWT) as [T' HT'].
  destruct (elim_tys_exists H1) as [Ts' HTs'].
  destruct (set_lists_length3 Γ2 (live_args xs bs) (live_args Ts' bs)) as [Γ4 HeqΓ4].
  apply live_args_length.
  rewrite (set_lists_length_eq _ _ _ _ H).
  eapply elim_tys_length; eauto.
  destruct (HGk (M.set f (Tfun w (live_args Ts' bs) T') Γ2) T2) as [HTk' Hk']; auto.
  - apply Elim_env_set; auto.
    apply Elim_Tfun; auto.
    rewrite <- (set_lists_length_eq _ _ _ _ H); auto.
  - unfold Dom_map, Ensembles.Included, Ensembles.In in *.
    intros.
    destruct (M.elt_eq f x); subst.
    + rewrite M.gss in *; eauto.
    + rewrite M.gso in *; eauto.
  - eapply Dom_map_set_subset; eauto.
  - destruct (HGe Γ4 T') as [HTe' He']; auto.
    + eapply Elim_env_set_lists; eauto.
    + unfold Ensembles.Included, Ensembles.In, Dom_map in *.
      intros.
      destruct (in_dec M.elt_eq x (live_args xs bs)).
      * eapply get_set_lists_In_xs; eauto.
      * rewrite <- (set_lists_not_In _ _ _ _ _ HeqΓ4 n).
        eapply H7.
        apply Free_fun2; auto.
    + apply Included_trans with (s2 := (FromList (live_args xs bs) :|: Dom_map Γ2)).
      eapply Dom_map_set_lists; eauto.
      apply Union_Included.
      * apply Included_trans with (FromList xs :|: Dom_map Γ).
        apply Included_Union_preserv_l.
        apply live_args_incl.
        eapply Dom_map_set_lists; eauto.
      * apply Included_trans with (Dom_map Γ); auto.
        apply Included_trans with (FromList xs :|: Dom_map Γ).
        apply Included_Union_preserv_r.
        apply Included_refl.
        eapply Dom_map_set_lists; eauto.
    + split; eauto.
      intros.
      assert (HV : V L (Tfun w Ts T) (Vfun ρ1 w xs e) (Vfun ρ2 w (live_args xs bs) e')).
      {
        simpl.
        exists ρ1, xs, e, ρ2, (live_args xs bs), e', bs;
          repeat split; auto.
        symmetry; eapply set_lists_length_eq; eauto.
        intros.
        eapply He'; eauto.
        eapply G_set_lists; eauto.
      }
      edestruct (Hk' (M.set f (Vfun ρ1 w xs e) ρ1) (M.set f (Vfun ρ2 w (live_args xs bs) e') ρ2)) as [v1 [v2 [kv1 [kv2 Vv]]]]; eauto.
      eapply G_set; eauto.
      exists v1, v2; repeat split; auto.
Qed.

Lemma Elim_env_get_list {L Γ1 Γ2} : forall {xs bs Ts1 Ts2},
  Elim_env L Γ1 Γ2 ->
  get_list xs Γ1 = Some Ts1 ->
  length xs = length bs ->
  get_list (live_args xs bs) Γ2 = Some Ts2 ->
  elim_tys L (live_args Ts1 bs) Ts2.
Proof.
  unfold Elim_env.
  intros xs; induction xs; simpl; intros.
  - inv H0.
    destruct bs.
    + inv H2; auto.
    + inv H1.
  - destruct (Γ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs Γ1) eqn:Heq2; try discriminate.
    inv H0.
    destruct bs; inv H1.
    destruct b; simpl in *.
    + destruct (Γ2 ! a) eqn:Heq3; try discriminate.
      destruct (get_list (live_args xs bs) Γ2) eqn:Heq4; try discriminate.
      inv H2.
      constructor.
      * eapply Elim_env_get; eauto.
      * eapply IHxs; eauto.
    + eapply IHxs; eauto.
Qed.

Lemma Dom_map_get_list {A} : forall xs (Γ : M.t A),
    (FromList xs) \subset Dom_map Γ ->
    exists Ts, get_list xs Γ = Some Ts.
Proof.
  unfold Ensembles.Included, Ensembles.In, Dom_map, FromList.
  intros xs.
  induction xs; simpl; intros; eauto.
  destruct (H a) as [Ta HeqTa]; auto.
  rewrite HeqTa.
  destruct (IHxs Γ) as [Ts HeqTs]; auto.
  rewrite HeqTs.
  eauto.
Qed.

Lemma G_get_list {L Γ1 Γ2 ρ1 ρ2} :
  G L Γ1 Γ2 ρ1 ρ2 ->
  forall {xs bs Ts},
    get_list xs Γ1 = Some Ts ->
    length xs = length bs ->
    (FromList (live_args xs bs)) \subset (Dom_map Γ2) ->
    exists vs1 vs2,
      get_list xs ρ1 = Some vs1 /\
      get_list (live_args xs bs) ρ2 = Some vs2 /\
      ForallV L Ts vs1 bs vs2.
Proof.
  unfold G.
  intros HG xs.
  induction xs; simpl; intros.
  - inv H.
    destruct bs; simpl; eauto.
    inv H0.
  - destruct (Γ1 ! a) eqn:Heq1; try discriminate.
    destruct (get_list xs Γ1) eqn:Heq2; try discriminate.
    inv H.
    destruct bs; inv H0.
    edestruct HG as [v1 [Heqv1 Hv2]]; eauto.
    destruct b; simpl in *.
    + unfold Ensembles.Included, Ensembles.In, Dom_map, FromList in H1.
      destruct (H1 a) as [Ta HeqTa]; auto.
      apply in_eq.
      edestruct Hv2 as [v2 [Heqv2 Vv]]; eauto.
      edestruct IHxs as [vs1 [vs2 [Heqvs1 [Heqvs2 HF]]]]; eauto.
      apply Included_trans with (FromList (a :: (live_args xs bs))); auto.
      apply incl_tl.
      apply incl_refl.

      exists (v1 :: vs1), (v2 :: vs2).
      rewrite Heqv1.
      rewrite Heqvs1.
      rewrite Heqv2.
      rewrite Heqvs2.
      auto.
    + edestruct IHxs as [vs1 [vs2 [Heqvs1 [Heqvs2 HF]]]]; eauto.
      exists (v1 :: vs1), vs2.
      rewrite Heqv1.
      rewrite Heqvs1.
      auto.
Qed.

Lemma app_compat {Γ L f w xs Ts T bs} :
  M.get f Γ = Some (Tfun w Ts T) ->
  get_list xs Γ = Some Ts ->
  M.get w L = Some bs ->
  length xs = length bs ->
  wf_ty L (Tfun w Ts T) ->
  elim_correct L Γ (Eapp f w xs) (Eapp f w (live_args xs bs)) T.
Proof.
  unfold elim_correct, Ensembles.Included, Ensembles.In, Dom_map.
  intros.
  inv H3.
  split; eauto.
  split; eauto.
  intros.
  destruct (H5 f) as [Tf HeqTf]; auto.
  rewrite H7 in H1; inv H1.
  split; intros.
  - destruct (elim_tys_exists H10) as [Ts' HTs'].
    apply HT_app with (live_args Ts' bs).
    + unfold Ensembles.Included, Ensembles.In, Dom_map in *.
      assert (elim_ty L (Tfun w Ts T) Tf).
      eapply Elim_env_get; eauto.
      inv H1.
      rewrite (elim_ty_deterministic H4 H17).
      rewrite (elim_tys_deterministic HTs' H18).
      rewrite H14 in H7; inv H7; auto.
    + destruct (Dom_map_get_list (live_args xs bs) Γ2) as [Txs HeqTxs].
      * apply Included_trans with (occurs_free (Eapp f w (live_args xs bs))); auto.
        unfold Ensembles.Included, Ensembles.In, FromList.
        intros; eauto.
      * assert (elim_tys L (live_args Ts bs) Txs).
        eapply Elim_env_get_list; eauto.
        eapply elim_tys_live_args in HTs'; eauto.
        rewrite <- (elim_tys_deterministic H1 HTs'); auto.

  - unfold G in H1.
    edestruct H1 as [fv1 [Heqfv1 [fv2 [Heqfv2 Vfv]]]]; eauto.
    unfold Ensembles.In, Dom_map; eauto.
    simpl in Vfv.
    destruct Vfv as [ρ1' [xs1' [e1' [ρ2' [xs2' [e2' [bs' [Heqbs' [Heqfv1' [Heqfv2' [Hxs2 [HlenTs [Hlenbs HF]]]]]]]]]]]]]; subst.
    rewrite H7 in Heqbs'; inv Heqbs'.

    edestruct (G_get_list H1 H0 H2) as [vs1 [vs2 [Heqvs1 [Heqvs2 HFv]]]]; eauto.
    {
      apply Included_trans with (occurs_free (Eapp f w (live_args xs bs'))); auto.
      unfold Ensembles.Included, Ensembles.In, FromList, Dom_map in *.
      intros.
      apply Free_app2; auto.
    }

    destruct (set_lists_length3 ρ1' xs1' vs1) as [ρ1'' Heqρ1''].
    {
      rewrite <- (get_list_length_eq _ _ _ H0) in HlenTs.
      rewrite <- (get_list_length_eq _ _ _ Heqvs1).
      auto.
    }

    destruct (set_lists_length3 ρ2' (live_args xs1' bs') vs2) as [ρ2'' Heqρ2''].
    {
      rewrite <- (get_list_length_eq _ _ _ H0) in HlenTs.
      rewrite <- (get_list_length_eq _ _ _ Heqvs2).
      apply live_args_length.
      auto.
    }

    edestruct (HF vs1 vs2 ρ1'' ρ2'') as [u1 [u2 [e'u1 [e'u2 Vu]]]]; eauto.
    exists u1, u2; repeat split; eauto.
Qed.

Lemma letapp_compat {L Γ x f w xs k bs k' Ts T U} :
  M.get f Γ = Some (Tfun w Ts T) ->
  get_list xs Γ = Some Ts ->
  elim_correct L (M.set x T Γ) k k' U ->

  M.get w L = Some bs ->
  length xs = length bs ->
  wf_ty L (Tfun w Ts T) ->
  elim_correct L Γ (Eletapp x f w xs k) (Eletapp x f w (live_args xs bs) k') U.
Proof.
  intros.
  specialize (app_compat H H0 H2 H3 H4); intros Happ.
  unfold elim_correct in *.
  destruct H1 as [HTk [HWU Hk']].
  destruct Happ as [HTapp [HWT Happ']].
  split; eauto.
  split; eauto.
  intros.
  destruct (elim_ty_exists HWT) as [T' HT'].
  destruct (Happ' Γ2 T') as [HTapp' HGapp']; auto.
  {
    apply Included_trans with (occurs_free (Eletapp x f w (live_args xs bs) k')); auto.
    unfold Ensembles.Included, Ensembles.In.
    intros.
    inv H8; eauto.
  }

  inv HTapp'.
  destruct (Hk' (M.set x T' Γ2) T2) as [HTk' HGk']; eauto.
  - apply Elim_env_set; auto.
  - apply Included_trans with (x |: (Dom_map Γ2)).
    + unfold Ensembles.Included, Ensembles.In, Dom_map in *.
      intros.
      destruct (M.elt_eq x x0); subst.
      * apply Union_introl; eauto.
      * apply Union_intror; eauto.
    + apply Dom_map_set.
  - apply Dom_map_set_subset; auto.
  - split; eauto.
    intros.
    destruct (HGapp' ρ1 ρ2) as [v1 [v2 [Rv1 [Rv2 Vv]]]]; auto.
    destruct (HGk' (M.set x v1 ρ1) (M.set x v2 ρ2)) as [u1 [u2 [ku1 [ku2 Vu]]]].
    apply G_set; auto.

    inv Rv1.
    inv Rv2.
    exists u1, u2; repeat split; eauto.
Qed.

Lemma if_compat {L Γ x t e t' e' T} :
  M.get x Γ = Some Tbool ->
  elim_correct L Γ t t' T ->
  elim_correct L Γ e e' T ->
  elim_correct L Γ (Eif x t e) (Eif x t' e') T.
Proof.
  unfold elim_correct.
  intros.
  destruct H0 as [HTt [HWT HFt']].
  destruct H1 as [HTe [_ HFe']].
  split; auto.
  split; auto.
  intros.
  edestruct HFt' as [HTt' HGt']; eauto.
  {
    apply Included_trans with (occurs_free (Eif x t' e')); auto.
    unfold Ensembles.Included, Ensembles.In.
    eauto.
  }

  edestruct HFe' as [HTe' HGe']; eauto.
  {
    apply Included_trans with (occurs_free (Eif x t' e')); auto.
    unfold Ensembles.Included, Ensembles.In.
    eauto.
  }

  assert (Γ2 ! x = Some Tbool).
  {
    unfold Elim_env, Ensembles.Included, Ensembles.In in *.
    destruct (H2 x) as [Tx HeqTx]; auto.
    specialize (H0 _ _ H _ HeqTx).
    inv H0; auto.
  }

  split; auto; intros.
  unfold G in H5.
  edestruct (H5 x Tbool) as [v1 [Heqv1 [v2 [Heqv2 Vv]]]]; eauto.
  inv Vv.
  destruct H6; subst.
  destruct x0.
  - destruct (HGt' ρ1 ρ2) as [u1 [u2 [Hequ1 [Hequ2 Vu]]]]; auto.
    exists u1, u2; repeat split; auto.
  - destruct (HGe' ρ1 ρ2) as [u1 [u2 [Hequ1 [Hequ2 Vu]]]]; auto.
    exists u1, u2; repeat split; auto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {L Γ e T e'} :
  elim_exp L Γ e T e' -> elim_correct L Γ e e' T.
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

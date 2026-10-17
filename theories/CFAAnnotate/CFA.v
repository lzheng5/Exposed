From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From CFAAnnotate Require Import LabeledANF Base Annotate.
From LambdaWeb Require Import ANF.

(* Web Annotation Based on a Value Set (0CFA) Analysis *)

Module A0 := CFAAnnotate.LabeledANF.
Module A1 := LambdaWeb.ANF.

(* The top-level semantic objects come from the Annotate functor framework *)
Module T := AnnotateTop.

(* --------------------------------------------------------------- *)
(* Abstract Values                                                 *)
(* --------------------------------------------------------------- *)

(* An abstract value is either
   - [AVlab l]: a value introduced at the (function or constructor) site labeled `l`
     of the analyzed unit, or
   - [AVext]: a value unknown to the analyzed unit, i.e. coming from the context. *)
Inductive aval : Type :=
| AVext : aval
| AVlab : label -> aval.

Definition avals := Ensemble aval.

(* The syntactic information recorded for an introduction site *)
Inductive site : Type :=
| Sfun : var -> list var -> site    (* the function name and its parameters *)
| Scon : list var -> site.          (* the variables holding the fields *)

(* --------------------------------------------------------------- *)
(* Analysis Result                                                 *)
(* --------------------------------------------------------------- *)

Record analysis :=
  mk_analysis {
      a_env : var -> avals;          (* value sets, one per variable (monovariant) *)
      a_ret : label -> avals;        (* return sets, one per function site *)
      a_site : label -> option site; (* the introduction sites *)
      a_esc : label -> bool          (* whether a label interacts with the context *)
    }.

(* Whether an abstract value interacts with the context *)
Definition aesc (A : analysis) (a : aval) : bool :=
  match a with
  | AVext => true
  | AVlab l => a_esc A l
  end.

(* The web assignment *)
Definition web_of (A : analysis) (l : label) : web :=
  if a_esc A l then w_ext else w_int.

(* All values in `S` interact with the context. *)
Definition ext_set (A : analysis) (S : avals) : Prop :=
  forall a, a \in S -> aesc A a = true.

(* All values in `S` live in the same web as the label `l`. *)
Definition same_web (A : analysis) (S : avals) (l : label) : Prop :=
  forall a, a \in S -> aesc A a = a_esc A l.

(* --------------------------------------------------------------- *)
(* Abstract Semantics                                              *)
(* --------------------------------------------------------------- *)

(* The constraints for calling `f` at the call site labeled `l` with arguments `ys`
   and the result flowing into `R`. *)
Definition app_ok (A : analysis) (f : var) (l : label) (ys : list var) (R : avals) : Prop :=
  if a_esc A l then
    (* foreign or escaping callee: the arguments escape and the result is unknown *)
    Forall (fun y => ext_set A (a_env A y)) ys /\ (AVext \in R)
  else
    (* internal callee: arguments flow into parameters and results flow out *)
    forall l' f' xs',
      (AVlab l' \in a_env A f) ->
      a_site A l' = Some (Sfun f' xs') ->
      Forall2 (fun y x => a_env A y \subset a_env A x) ys xs' /\
      (a_ret A l' \subset R).

(* `check A e R`: the analysis result `A` is acceptable for `e` and
   `R` over-approximates the values `e` may return.

   This is a declarative constraint system rather than a fixpoint computation,
   so any solver that produces an [analysis] may be plugged in and checked. *)
Inductive check (A : analysis) : A0.exp -> avals -> Prop :=
| Check_ret :
  forall {x R},
    (a_env A x \subset R) ->
    check A (A0.Eret x) R

| Check_fun :
  forall {f l xs e k R},
    (AVlab l \in a_env A f) ->
    (if a_esc A l then
       (* escaping function: the context may call it with unknown arguments,
          and it returns to the context *)
       Forall (fun x => AVext \in a_env A x) xs /\ ext_set A (a_ret A l)
     else
       a_site A l = Some (Sfun f xs)) ->
    check A e (a_ret A l) ->
    check A k R ->
    check A (A0.Efun f l xs e k) R

| Check_app :
  forall {f l ys R},
    same_web A (a_env A f) l ->
    app_ok A f l ys R ->
    check A (A0.Eapp f l ys) R

| Check_letapp :
  forall {x f l ys k R},
    same_web A (a_env A f) l ->
    app_ok A f l ys (a_env A x) ->
    check A k R ->
    check A (A0.Eletapp x f l ys k) R

| Check_constr :
  forall {x l t ys k R},
    (AVlab l \in a_env A x) ->
    (if a_esc A l then
       (* escaping constructor: the context may project its fields *)
       Forall (fun y => ext_set A (a_env A y)) ys
     else
       a_site A l = Some (Scon ys)) ->
    check A k R ->
    check A (A0.Econstr x l t ys k) R

| Check_proj :
  forall {x l n y k R},
    same_web A (a_env A y) l ->
    (if a_esc A l then
       AVext \in a_env A x
     else
       forall l' ys y',
         (AVlab l' \in a_env A y) ->
         a_site A l' = Some (Scon ys) ->
         nth_error ys n = Some y' ->
         a_env A y' \subset a_env A x) ->
    check A k R ->
    check A (A0.Eproj x l n y k) R

| Check_case_nil :
  forall {x l R},
    same_web A (a_env A x) l ->
    check A (A0.Ecase x l []) R

| Check_case_cons :
  forall {x l c e cl R},
    same_web A (a_env A x) l ->
    check A e R ->
    check A (A0.Ecase x l cl) R ->
    check A (A0.Ecase x l ((c, e) :: cl)) R.

Hint Constructors check : core.

(* The analysis result is acceptable for a whole compilation unit `e`:
   everything free in `e` comes from the context, and everything `e` returns goes to the context. *)
Definition check_top (A : analysis) (R : avals) (e : A0.exp) : Prop :=
  check A e R /\
  ext_set A R /\
  (forall x, x \in A0.occurs_free e -> AVext \in a_env A x).

(* --------------------------------------------------------------- *)
(* Web Annotation                                                  *)
(* --------------------------------------------------------------- *)

Fixpoint annotate (A : analysis) (e : A0.exp) : A1.exp :=
  match e with
  | A0.Eret x => A1.Eret x
  | A0.Eapp f l xs => A1.Eapp f (web_of A l) xs
  | A0.Eletapp x f l xs k => A1.Eletapp x f (web_of A l) xs (annotate A k)
  | A0.Efun f l xs e k => A1.Efun f (web_of A l) xs (annotate A e) (annotate A k)
  | A0.Econstr x l t xs k => A1.Econstr x (web_of A l) t xs (annotate A k)
  | A0.Ecase x l cl =>
      A1.Ecase x (web_of A l)
        ((fix annotate_case (cl : list (ctor_tag * A0.exp)) :=
            match cl with
            | [] => []
            | (c, e) :: cl => (c, annotate A e) :: annotate_case cl
            end) cl)
  | A0.Eproj x l n y k => A1.Eproj x (web_of A l) n y (annotate A k)
  end.

Lemma annotate_occurs_free A e :
  A1.occurs_free (annotate A e) \subset A0.occurs_free e.
Proof.
  unfold Ensembles.Included, Ensembles.In.
  induction e using A0.exp_ind'; simpl; intros y Hy; inv Hy; eauto.
Qed.

Lemma annotate_find_tag A cl t e :
  find_tag cl t e ->
  find_tag
    ((fix annotate_case (cl : list (ctor_tag * A0.exp)) :=
        match cl with
        | [] => []
        | (c, e) :: cl => (c, annotate A e) :: annotate_case cl
        end) cl)
    t (annotate A e).
Proof.
  intros Hfind.
  induction Hfind; simpl; eauto.
Qed.

(* --------------------------------------------------------------- *)
(* Cross-language Logical Relations                                *)
(* --------------------------------------------------------------- *)

Inductive Forall3 {T1 T2 T3 : Type} (P : T1 -> T2 -> T3 -> Prop) : list T1 -> list T2 -> list T3 -> Prop :=
| Forall3_nil :
  Forall3 P [] [] []

| Forall3_cons :
  forall x y z xs ys zs,
    P x y z ->
    Forall3 P xs ys zs ->
    Forall3 P (x :: xs) (y :: ys) (z :: zs).

Hint Constructors Forall3 : core.

Lemma Forall3_impl {T1 T2 T3} (P Q : T1 -> T2 -> T3 -> Prop) xs ys zs :
  (forall x y z, P x y z -> Q x y z) ->
  Forall3 P xs ys zs ->
  Forall3 Q xs ys zs.
Proof.
  intros HPQ HF.
  induction HF; auto.
Qed.

Lemma Forall3_length {T1 T2 T3} (P : T1 -> T2 -> T3 -> Prop) xs ys zs :
  Forall3 P xs ys zs ->
  length xs = length ys /\ length ys = length zs.
Proof.
  intros HF.
  induction HF as [| x y z xs' ys' zs' HP HF' [IH1 IH2]]; simpl; auto.
Qed.

Lemma Forall3_nth_error {T1 T2 T3} (P : T1 -> T2 -> T3 -> Prop) xs ys zs n y :
  Forall3 P xs ys zs ->
  nth_error ys n = Some y ->
  exists x z, nth_error xs n = Some x /\ nth_error zs n = Some z /\ P x y z.
Proof.
  intros HF.
  revert n.
  induction HF as [| x' y' z' xs' ys' zs' HP HF' IH]; intros n Hnth.
  - destruct n; inv Hnth.
  - destruct n; simpl in *.
    + inv Hnth; eauto.
    + eapply IH; eauto.
Qed.

Lemma Forall3_Forall2_r {T1 T2 T3} (P : T1 -> T2 -> T3 -> Prop) (Q : T2 -> T3 -> Prop) xs ys zs :
  (forall x y z, P x y z -> Q y z) ->
  Forall3 P xs ys zs ->
  Forall2 Q ys zs.
Proof.
  intros HPQ HF.
  induction HF; eauto.
Qed.

(* Change the first list along a pointwise relation *)
Lemma Forall3_Forall2_l {T1 T2 T3} (P Q : T1 -> T2 -> T3 -> Prop) (S : T1 -> T1 -> Prop) xs xs' ys zs :
  (forall x x' y z, S x x' -> P x y z -> Q x' y z) ->
  Forall2 S xs xs' ->
  Forall3 P xs ys zs ->
  Forall3 Q xs' ys zs.
Proof.
  intros HPQ HS.
  revert ys zs.
  induction HS as [| x x' xs1 xs1' HS1 HS' IH]; intros ys zs HF; inv HF; eauto.
Qed.

Section Relations.

  Variable A : analysis.

  Definition R' (P : nat -> aval -> A0.wval -> A1.wval -> Prop) (S : avals) (i : nat) (r1 : A0.res) (r2 : A1.res) :=
    match r1, r2 with
    | A0.OOT, A1.OOT => True
    | A0.Res v1, A1.Res v2 => exists a, (a \in S) /\ P i a v1 v2
    | _, _ => False
    end.

  Definition E' (P : nat -> aval -> A0.wval -> A1.wval -> Prop) (ex : bool) (S : avals) (i : nat) (ρ1 : A0.env) (e1 : A0.exp) (ρ2 : A1.env) (e2 : A1.exp) : Prop :=
    forall j1 r1,
      j1 <= i ->
      A0.bstep_fuel ρ1 e1 j1 r1 ->
      exists j2 r2,
        A1.bstep_fuel ex ρ2 e2 j2 r2 /\
        R' P S (i - j1) r1 r2.

  (* `V i a v1 v2`: the source value `v1` and the target value `v2` are related
     at the abstract value `a`.

     Abstract values interacting with the context are interpreted as the
     top-level relation, which is independent of the analysis.

     Note that the runtime labels of source values are never consulted:
     a value from the context may carry any label. *)
  Fixpoint V (i : nat) (a : aval) (v1 : A0.wval) (wv2 : A1.wval) {struct i} : Prop :=
    match a with
    | AVext => T.V i v1 wv2
    | AVlab l =>
        if a_esc A l then T.V i v1 wv2 else
          wf_val wv2 /\
          match v1, wv2 with
          | A0.TAG _ _ v1', A1.TAG _ w2 v2' =>
              w2 = w_int /\
              match a_site A l, v1', v2' with
              | Some (Sfun f xs), A0.Vfun f1 ρ1 xs1 e1, A1.Vfun f2 ρ2 xs2 e2 =>
                  f1 = f /\ xs1 = xs /\ length xs1 = length xs2 /\
                  match i with
                  | 0 => True
                  | S i0 =>
                      forall j vs1 vs2 ρ3 ρ4,
                        j <= i0 ->
                        Forall3 (fun x v1 v2 => exists a, (a \in a_env A x) /\ V (i0 - (i0 - j)) a v1 v2) xs1 vs1 vs2 ->
                        set_lists xs1 vs1 (M.set f1 v1 ρ1) = Some ρ3 ->
                        set_lists xs2 vs2 (M.set f2 wv2 ρ2) = Some ρ4 ->
                        E' V false (a_ret A l) (i0 - (i0 - j)) ρ3 e1 ρ4 e2
                  end

              | Some (Scon ys), A0.Vconstr c1 vs1, A1.Vconstr c2 vs2 =>
                  c1 = c2 /\
                  match i with
                  | 0 => length ys = length vs1 /\ length vs1 = length vs2
                  | S i0 => Forall3 (fun y v1 v2 => exists a, (a \in a_env A y) /\ V i0 a v1 v2) ys vs1 vs2
                  end

              | _, _, _ => False
              end
          end
    end.

  (* Related at some abstract value in `S` *)
  Definition Vs i S v1 v2 := exists a, (a \in S) /\ V i a v1 v2.

  Definition R := (R' V).

  Definition E := (E' V).

  (* Environment Relation *)
  Definition G i Γ ρ1 ρ2 :=
    wf_env ρ2 /\
    forall x,
      (x \in Γ) ->
      exists v1 v2,
        M.get x ρ1 = Some v1 /\
        M.get x ρ2 = Some v2 /\
        Vs i (a_env A x) v1 v2.

  (* Escaping abstract values are interpreted as the top-level relation *)
  Lemma V_esc i a v1 v2 :
    aesc A a = true ->
    V i a v1 v2 <-> T.V i v1 v2.
  Proof.
    intros Hesc.
    destruct a as [| l]; simpl in *;
      destruct i; simpl; try rewrite Hesc; reflexivity.
  Qed.

  Lemma V_ext i v1 v2 :
    T.V i v1 v2 ->
    V i AVext v1 v2.
  Proof. intros HV; destruct i; exact HV. Qed.

  Lemma V_int_inv i a v1 v2 :
    aesc A a = false ->
    V i a v1 v2 ->
    exists l, a = AVlab l /\ a_esc A l = false.
  Proof.
    intros Hesc HV.
    destruct a as [| l]; simpl in *; try discriminate.
    eauto.
  Qed.

  (* Lemmas about [wf_val], [exposed], and webs *)
  Lemma V_wf_val_r {i a v1 v2} :
    V i a v1 v2 ->
    wf_val v2.
  Proof.
    intros HV.
    destruct (aesc A a) eqn:Hesc.
    - eapply T.VM.V_wf_val_r.
      eapply V_esc; eauto.
    - destruct (V_int_inv _ _ _ _ Hesc HV) as [l [Heq Hl]]; subst.
      destruct i; simpl in HV; rewrite Hl in HV; destruct HV as [Hwf _]; auto.
  Qed.

  Lemma V_esc_exposed {i a v1 v2} :
    aesc A a = true ->
    V i a v1 v2 ->
    exposed v2.
  Proof.
    intros Hesc HV.
    eapply T.V_exposed_r.
    eapply V_esc; eauto.
  Qed.

  Lemma V_web {i a v1 w2 v2} :
    V i a v1 (Tag w2 v2) ->
    w2 = if aesc A a then w_ext else w_int.
  Proof.
    intros HV.
    destruct (aesc A a) eqn:Hesc.
    - pose proof (V_esc_exposed Hesc HV) as Hex.
      inv Hex; apply w_ext_unique; auto.
    - destruct (V_int_inv _ _ _ _ Hesc HV) as [l [Heq Hl]]; subst.
      destruct v1 as [l1 v1].
      destruct i; simpl in HV; rewrite Hl in HV;
        destruct HV as [_ [Hw _]]; auto.
  Qed.

  Lemma Vs_wf_val_Forall_r {i ys vs1 vs2} :
    Forall3 (fun y v1 v2 => Vs i (a_env A y) v1 v2) ys vs1 vs2 ->
    Forall wf_val vs2.
  Proof.
    intros HF.
    induction HF as [| y v1 v2 ys' vs1' vs2' [a [Ha HV]] HF' IH]; auto.
    constructor; auto.
    eapply V_wf_val_r; eauto.
  Qed.

  (* Results related at escaping abstract values are exposed *)
  Lemma R_exposed {S i r1 r2} :
    ext_set A S ->
    R S i r1 r2 ->
    exposed_res r2.
  Proof.
    unfold R, R'.
    intros HS HR.
    destruct r1 as [| v1]; destruct r2 as [| v2]; try contradiction; auto.
    destruct HR as [a [Ha HV]].
    constructor.
    eapply V_esc_exposed; eauto.
  Qed.

  Lemma R_subset {S1 S2 i r1 r2} :
    S1 \subset S2 ->
    R S1 i r1 r2 ->
    R S2 i r1 r2.
  Proof.
    unfold R, R'.
    intros Hsub HR.
    destruct r1 as [| v1]; destruct r2 as [| v2]; try contradiction; auto.
    destruct HR as [a [Ha HV]].
    eexists; split; eauto.
  Qed.

  (* Monotonicity Lemmas *)
  Lemma V_mono i :
    forall {j a v1 v2},
      V i a v1 v2 ->
      j <= i ->
      V j a v1 v2.
  Proof.
    induction i as [i IHi] using lt_wf_rec.
    intros j a v1 v2 HV Hj.
    destruct (aesc A a) eqn:Hesc.
    - eapply V_esc; eauto.
      eapply T.VM.V_mono; eauto.
      eapply V_esc; eauto.
    - destruct (V_int_inv _ _ _ _ Hesc HV) as [l [Heq Hl]]; subst.
      destruct v1 as [l1 v1]; destruct v2 as [w2 v2].
      destruct i as [| i0]; destruct j as [| j0]; simpl in *; rewrite Hl in *; try lia;
        destruct HV as [Hwf [Hw HV]]; subst; repeat (split; auto);
        destruct (a_site A l) as [[f xs | ys] |]; try contradiction;
        destruct v1; destruct v2; try contradiction.
      + destruct HV as [Hf [Hxs [Hlen _]]]; auto.
      + destruct HV as [Hc HF]; subst.
        pose proof (Forall3_length _ _ _ _ HF) as [Hlen1 Hlen2]; auto.
      + destruct HV as [Hf [Hxs [Hlen HV]]]; subst.
        repeat (split; auto).
        intros j' vs1 vs2 ρ3 ρ4 Hj' HF Hset1 Hset2.
        assert (Hj0 : j' <= i0) by lia.
        specialize (HV j' vs1 vs2 ρ3 ρ4 Hj0).
        rewrite normalize_step in *; try lia.
        eapply HV; eauto.
      + destruct HV as [Hc HF]; subst.
        split; auto.
        eapply Forall3_impl; eauto.
        intros y v1 v2 [a [Ha HVa]].
        eexists; split; eauto.
        eapply (IHi i0); eauto; lia.
  Qed.

  Lemma Vs_mono {i j S v1 v2} :
    Vs i S v1 v2 ->
    j <= i ->
    Vs j S v1 v2.
  Proof.
    intros [a [Ha HV]] Hj.
    eexists; split; eauto.
    eapply V_mono; eauto.
  Qed.

  Lemma R_mono {S i j r1 r2} :
    R S i r1 r2 ->
    j <= i ->
    R S j r1 r2.
  Proof.
    unfold R, R'.
    intros HR Hj.
    destruct r1 as [| v1]; destruct r2 as [| v2]; try contradiction; auto.
    destruct HR as [a [Ha HV]].
    eexists; split; eauto.
    eapply V_mono; eauto.
  Qed.

  Lemma E_mono {ex S i j ρ1 e1 ρ2 e2} :
    E ex S i ρ1 e1 ρ2 e2 ->
    j <= i ->
    E ex S j ρ1 e1 ρ2 e2.
  Proof.
    unfold E, E'.
    intros HE Hj j1 r1 Hj1 Hstep.
    destruct (HE j1 r1) as [j2 [r2 [Hstep2 HR]]]; auto; try lia.
    exists j2, r2; split; auto.
    eapply R_mono; eauto; lia.
  Qed.

  (* Environment Lemmas *)
  Lemma G_wf_env_r {i Γ ρ1 ρ2} :
    G i Γ ρ1 ρ2 ->
    wf_env ρ2.
  Proof. unfold G; intros [Hwf _]; auto. Qed.

  Lemma G_subset {i Γ1 Γ2 ρ1 ρ2} :
    G i Γ1 ρ1 ρ2 ->
    Γ2 \subset Γ1 ->
    G i Γ2 ρ1 ρ2.
  Proof.
    unfold G.
    intros [Hwf HG] Hsub.
    split; auto.
  Qed.

  Lemma G_mono {i j Γ ρ1 ρ2} :
    G i Γ ρ1 ρ2 ->
    j <= i ->
    G j Γ ρ1 ρ2.
  Proof.
    unfold G.
    intros [Hwf HG] Hj.
    split; auto.
    intros x Hx.
    destruct (HG x Hx) as [v1 [v2 [Hget1 [Hget2 HV]]]].
    exists v1, v2; repeat (split; auto).
    eapply Vs_mono; eauto.
  Qed.

  Lemma G_get {i Γ ρ1 ρ2} :
    G i Γ ρ1 ρ2 ->
    forall x v1,
      (x \in Γ) ->
      M.get x ρ1 = Some v1 ->
      exists v2,
        M.get x ρ2 = Some v2 /\
        Vs i (a_env A x) v1 v2.
  Proof.
    unfold G.
    intros [Hwf HG] x v1 Hx Hget.
    destruct (HG x Hx) as [v1' [v2 [Hget1 [Hget2 HV]]]].
    rewrite Hget in Hget1; inv Hget1.
    eauto.
  Qed.

  Lemma G_get_list {i Γ ρ1 ρ2} :
    G i Γ ρ1 ρ2 ->
    forall xs vs1,
      (FromList xs \subset Γ) ->
      get_list xs ρ1 = Some vs1 ->
      exists vs2,
        get_list xs ρ2 = Some vs2 /\
        Forall3 (fun x v1 v2 => Vs i (a_env A x) v1 v2) xs vs1 vs2.
  Proof.
    intros HG xs.
    induction xs as [| x xs IHxs]; simpl; intros vs1 Hsub Hget.
    - inv Hget; eauto.
    - destruct (ρ1 ! x) as [v1 |] eqn:Hget1; try discriminate.
      destruct (get_list xs ρ1) as [vs1' |] eqn:Hgets1; try discriminate.
      inv Hget.
      rewrite FromList_cons in Hsub.
      edestruct (G_get HG x v1) as [v2 [Hget2 HV]]; eauto.
      edestruct IHxs as [vs2 [Hgets2 HF]]; eauto.
      { eapply Included_trans; eauto; apply Included_Union_r. }
      rewrite Hget2, Hgets2.
      eauto.
  Qed.

  Lemma G_set {i Γ ρ1 ρ2} :
    G i Γ ρ1 ρ2 ->
    forall {x v1 v2},
      Vs i (a_env A x) v1 v2 ->
      G i (x |: Γ) (M.set x v1 ρ1) (M.set x v2 ρ2).
  Proof.
    unfold G.
    intros [Hwf HG] x v1 v2 HV.
    split.
    - eapply wf_env_set; eauto.
      destruct HV as [a [Ha HVa]].
      eapply V_wf_val_r; eauto.
    - intros y Hy.
      destruct (M.elt_eq y x) as [Heq | Hneq]; subst.
      + repeat rewrite M.gss; eauto.
      + repeat (rewrite M.gso; auto).
        inv Hy.
        * inv H; contradiction.
        * eauto.
  Qed.

  Lemma G_set_lists {i Γ ρ1 ρ2} :
    G i Γ ρ1 ρ2 ->
    forall {xs vs1 vs2 ρ3 ρ4},
      Forall3 (fun x v1 v2 => Vs i (a_env A x) v1 v2) xs vs1 vs2 ->
      set_lists xs vs1 ρ1 = Some ρ3 ->
      set_lists xs vs2 ρ2 = Some ρ4 ->
      G i (FromList xs :|: Γ) ρ3 ρ4.
  Proof.
    intros HG xs vs1 vs2 ρ3 ρ4 HF.
    revert ρ3 ρ4.
    induction HF as [| x v1 v2 xs' vs1' vs2' HV HF' IH]; simpl; intros ρ3 ρ4 Hset1 Hset2.
    - inv Hset1; inv Hset2.
      eapply G_subset; eauto.
      rewrite FromList_nil, Union_Empty_set_neut_l.
      apply Included_refl.
    - destruct (set_lists xs' vs1' ρ1) as [ρ3' |] eqn:Hset1'; try discriminate.
      destruct (set_lists xs' vs2' ρ2) as [ρ4' |] eqn:Hset2'; try discriminate.
      inv Hset1; inv Hset2.
      eapply (@G_subset _ (x |: (FromList xs' :|: Γ))).
      + eapply G_set; eauto.
      + rewrite FromList_cons, Union_assoc.
        apply Included_refl.
  Qed.

  (* Bridges to the Top-level Relations *)
  Lemma G_top_G {i Γ ρ1 ρ2} :
    (forall x, x \in Γ -> AVext \in a_env A x) ->
    T.G i Γ ρ1 ρ2 ->
    G i Γ ρ1 ρ2.
  Proof.
    unfold T.G, G.
    intros Hext [Hwf HG].
    split; auto.
    intros x Hx.
    destruct (HG x Hx) as [v1 [v2 [Hget1 [Hget2 HV]]]].
    exists v1, v2; repeat (split; auto).
    exists AVext; split; auto.
    eapply V_ext; eauto.
  Qed.

  Lemma R_top {S i r1 r2} :
    ext_set A S ->
    R S i r1 r2 ->
    T.R i r1 r2.
  Proof.
    unfold R, R', T.R, T.VM.R, AnnotateUtil.R'.
    intros HS HR.
    destruct r1 as [| v1]; destruct r2 as [| v2]; try contradiction; auto.
    destruct HR as [a [Ha HV]].
    eapply V_esc; eauto.
  Qed.

  Lemma E_top {S i ρ1 e1 ρ2 e2} :
    ext_set A S ->
    E true S i ρ1 e1 ρ2 e2 ->
    T.E true i ρ1 e1 ρ2 e2.
  Proof.
    unfold E, E', T.E, T.VM.E, AnnotateUtil.E'.
    intros HS HE j1 r1 Hj1 Hstep.
    destruct (HE j1 r1 Hj1 Hstep) as [j2 [r2 [Hstep2 HR]]].
    exists j2, r2; split; auto.
    eapply (R_top HS HR).
  Qed.

  Lemma Forall3_ext {i xs vs1 vs2} :
    Forall (fun x => AVext \in a_env A x) xs ->
    length xs = length vs1 ->
    Forall2 (T.V i) vs1 vs2 ->
    Forall3 (fun x v1 v2 => Vs i (a_env A x) v1 v2) xs vs1 vs2.
  Proof.
    intros Hxs.
    revert vs1 vs2.
    induction Hxs as [| x xs' Hx Hxs' IH]; intros vs1 vs2 Hlen HF;
      destruct vs1 as [| v1 vs1']; inv Hlen; inv HF; auto.
    constructor; auto.
    exists AVext; split; auto.
    eapply V_ext; eauto.
  Qed.

  Lemma Forall3_top {i ys vs1 vs2} :
    Forall (fun y => ext_set A (a_env A y)) ys ->
    Forall3 (fun y v1 v2 => Vs i (a_env A y) v1 v2) ys vs1 vs2 ->
    Forall2 (T.V i) vs1 vs2.
  Proof.
    intros Hys HF.
    revert Hys.
    induction HF as [| y v1 v2 ys' vs1' vs2' [a [Ha HV]] HF' IH]; intros Hys; inv Hys; auto.
    constructor; auto.
    eapply V_esc; eauto.
  Qed.

  (* Compatibility Lemmas *)
  Definition ex_ok (ex : bool) (S : avals) :=
    ex = true -> ext_set A S.

  Definition cfa_correct ex S e :=
    forall i ρ1 ρ2,
      G i (A0.occurs_free e) ρ1 ρ2 ->
      E ex S i ρ1 e ρ2 (annotate A e).

  Lemma bstep_fuel_ex_inv {ex ρ e j r} :
    A1.bstep_fuel ex ρ e j r ->
    if ex then exposed_res r else True.
  Proof.
    intros Hstep.
    inv Hstep; destruct ex; auto.
  Qed.

  Lemma R_ex_ok {ex S i r1 r2} :
    ex_ok ex S ->
    R S i r1 r2 ->
    if ex then exposed_res r2 else True.
  Proof.
    intros Hex HR.
    destruct ex; auto.
    eapply R_exposed; eauto.
  Qed.

  Lemma same_web_web {S l a} :
    same_web A S l ->
    a \in S ->
    (if aesc A a then w_ext else w_int) = web_of A l.
  Proof.
    unfold same_web, web_of.
    intros Hweb Ha.
    rewrite (Hweb a Ha); auto.
  Qed.

  Lemma ret_compat {ex S x} :
    (a_env A x \subset S) ->
    ex_ok ex S ->
    cfa_correct ex S (A0.Eret x).
  Proof.
    unfold cfa_correct, E, E'.
    intros Hsub Hex i ρ1 ρ2 HG j1 r1 Hj1 Hstep.
    inv Hstep.
    - exists 0, A1.OOT; split; simpl; auto.
    - match goal with
      | [ H : A0.bstep _ _ _ _ |- _ ] => inv H
      end.
      edestruct (G_get HG x) as [v2 [Hget2 [a [Ha HV]]]]; eauto.
      exists 1, (A1.Res v2); split.
      + constructor.
        * constructor; auto.
        * destruct ex; auto.
          constructor.
          eapply V_esc_exposed; eauto.
          eapply Hex; auto.
      + simpl.
        exists a; split; auto.
        eapply V_mono; eauto; lia.
  Qed.

  Lemma Vfun_V {f l xs e} :
    (AVlab l \in a_env A f) ->
    (if a_esc A l then
       Forall (fun x => AVext \in a_env A x) xs /\ ext_set A (a_ret A l)
     else
       a_site A l = Some (Sfun f xs)) ->
    cfa_correct (a_esc A l) (a_ret A l) e ->
    forall i Γ ρ1 ρ2 l1,
      G i Γ ρ1 ρ2 ->
      A0.occurs_free e \subset FromList xs :|: (f |: Γ) ->
      V i (AVlab l) (A0.Tag l1 (A0.Vfun f ρ1 xs e)) (Tag (web_of A l) (A1.Vfun f ρ2 xs (annotate A e))).
  Proof.
    unfold cfa_correct, web_of.
    intros Hf Hsite He.
    destruct (a_esc A l) eqn:Hesc.
    - destruct Hsite as [Hxs Hret].
      intros i.
      induction i as [| i IHi]; intros Γ ρ1 ρ2 l1 HG HFV;
        apply V_esc; simpl; auto;
        unfold T.V; simpl;
        rewrite w_ext_exposedb;
        pose proof (G_wf_env_r HG) as Hwf;
        assert (Hex : exposed (Tag w_ext (A1.Vfun f ρ2 xs (annotate A e)))) by (constructor; apply w_ext_exposed);
        repeat (split; auto).
      intros j vs1 vs2 ρ3 ρ4 Hj Hexs HF Hset1 Hset2.
      rewrite normalize_step in *; auto.
      eapply E_top; eauto.
      eapply He.
      eapply G_subset; eauto.
      eapply G_set_lists; eauto.
      + eapply G_set.
        * eapply G_mono; eauto; lia.
        * exists (AVlab l); split; auto.
          eapply V_mono with (i := i); try lia.
          eapply IHi; eauto.
          eapply G_mono; eauto; lia.
      + eapply Forall3_ext; eauto.
        eapply set_lists_length_eq; eauto.
    - intros i.
      induction i as [| i IHi]; intros Γ ρ1 ρ2 l1 HG HFV;
        simpl; rewrite Hesc, Hsite;
        pose proof (G_wf_env_r HG) as Hwf;
        assert (Hwfv : wf_val (Tag w_int (A1.Vfun f ρ2 xs (annotate A e))))
          by (constructor; auto; intros Hc; contradiction (w_int_not_exposed Hc));
        repeat (split; auto).
      intros j vs1 vs2 ρ3 ρ4 Hj HF Hset1 Hset2.
      rewrite normalize_step in *; auto.
      eapply He.
      eapply G_subset; eauto.
      eapply G_set_lists; eauto.
      eapply G_set.
      + eapply G_mono; eauto; lia.
      + exists (AVlab l); split; auto.
        eapply V_mono with (i := i); try lia.
        eapply IHi; eauto.
        eapply G_mono; eauto; lia.
  Qed.

  Lemma fun_compat {ex S f l xs e k} :
    (AVlab l \in a_env A f) ->
    (if a_esc A l then
       Forall (fun x => AVext \in a_env A x) xs /\ ext_set A (a_ret A l)
     else
       a_site A l = Some (Sfun f xs)) ->
    cfa_correct (a_esc A l) (a_ret A l) e ->
    cfa_correct ex S k ->
    cfa_correct ex S (A0.Efun f l xs e k).
  Proof.
    intros Hf Hsite He Hk.
    unfold cfa_correct, E, E' in *.
    intros i ρ1 ρ2 HG j1 r1 Hj1 Hstep.
    simpl.
    inv Hstep.
    - exists 0, A1.OOT; split; simpl; auto.
    - match goal with
      | [ H : A0.bstep _ _ _ _ |- _ ] => inv H
      end.
      match goal with
      | [ H : A0.bstep_fuel _ k _ _ |- _ ] => rename H into Hstepk
      end.
      edestruct (Hk (i - 1)
                   (M.set f (A0.Tag l (A0.Vfun f ρ1 xs e)) ρ1)
                   (M.set f (Tag (web_of A l) (A1.Vfun f ρ2 xs (annotate A e))) ρ2))
        with (j1 := c) (r1 := r1) as [j2 [r2 [Hstep2 HR]]]; eauto; try lia.
      + eapply G_subset.
        * eapply G_set.
          -- eapply G_mono; eauto; lia.
          -- exists (AVlab l); split; auto.
             eapply Vfun_V; eauto.
             ++ eapply G_mono; eauto; lia.
             ++ eapply A0.free_fun_e_subset.
        * eapply A0.free_fun_k_subset.
      + exists (Datatypes.S j2), r2; split.
        * constructor; auto.
          eapply bstep_fuel_ex_inv; eauto.
        * eapply R_mono; eauto; lia.
  Qed.

  Ltac name_app_hyps :=
    match goal with
    | [ H : A0.bstep _ _ _ _ |- _ ] => inv H
    end;
    match goal with
    | [ H : M.get ?f ?ρ = Some (A0.Tag _ (A0.Vfun _ _ _ _)) |- _ ] => rename H into Hgetf
    end;
    match goal with
    | [ H : get_list _ _ = Some _ |- _ ] => rename H into Hgets
    end;
    match goal with
    | [ H : set_lists _ _ _ = Some _ |- _ ] => rename H into Hset
    end.

  (* The callee part shared by [app_compat] and [letapp_compat] *)
  Lemma call_compat {i Γ ρ1 ρ2 f l ys Rs f' w' ρ' xs' e vs ρ'' c r1} :
    G (Datatypes.S i) Γ ρ1 ρ2 ->
    (f \in Γ) ->
    (FromList ys \subset Γ) ->
    same_web A (a_env A f) l ->
    app_ok A f l ys Rs ->
    ρ1 ! f = Some (A0.Tag w' (A0.Vfun f' ρ' xs' e)) ->
    get_list ys ρ1 = Some vs ->
    set_lists xs' vs (M.set f' (A0.Tag w' (A0.Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
    A0.bstep_fuel ρ'' e c r1 ->
    c <= i ->
    exists f2 ρ2' xs2 e2 vs2 ρ4 j2 r2,
      ρ2 ! f = Some (Tag (web_of A l) (A1.Vfun f2 ρ2' xs2 e2)) /\
      get_list ys ρ2 = Some vs2 /\
      set_lists xs2 vs2 (M.set f2 (Tag (web_of A l) (A1.Vfun f2 ρ2' xs2 e2)) ρ2') = Some ρ4 /\
      A1.bstep_fuel (exposedb (web_of A l)) ρ4 e2 j2 r2 /\
      (web_of A l \in Exposed -> Forall exposed vs2 /\ exposed_res r2) /\
      R Rs (i - c) r1 r2.
  Proof.
    intros HG Hf Hys Hweb Happ Hgetf Hgets Hset Hbody Hc.
    edestruct (G_get HG f) as [fv2 [Hgetf2 [a [Ha HVf]]]]; eauto.
    edestruct (G_get_list HG ys) as [vs2 [Hgets2 HFvs]]; eauto.
    destruct fv2 as [w2 fv2].
    pose proof (V_web HVf) as Hw2.
    rewrite (same_web_web Hweb Ha) in Hw2; subst w2.
    unfold app_ok, web_of in *.
    destruct (a_esc A l) eqn:Hesc.
    - (* external callee *)
      destruct Happ as [Hysext Hext].
      assert (Hesca : aesc A a = true) by (rewrite (Hweb a Ha); auto).
      apply (V_esc _ _ _ _ Hesca) in HVf.
      unfold T.V in HVf; simpl in HVf.
      destruct HVf as [Hwf2 HVf].
      rewrite w_ext_exposedb in HVf.
      destruct HVf as [Hexf HVf].
      destruct fv2 as [f2 ρ2' xs2 e2 | c2 vs2']; simpl in HVf; try contradiction.
      destruct HVf as [Hlen HVf].
      pose proof (Forall3_top Hysext HFvs) as HFtop.
      assert (Hlen2 : length xs2 = length vs2).
      { pose proof (set_lists_length_eq _ _ _ _ Hset) as Hl1.
        pose proof (Forall2_length _ _ _ HFtop) as Hl2.
        unfold var in *; lia. }
      destruct (set_lists_length3 (M.set f2 (Tag w_ext (A1.Vfun f2 ρ2' xs2 e2)) ρ2') xs2 vs2 Hlen2) as [ρ4 Hset2].
      edestruct (HVf i vs vs2 ρ'' ρ4) with (j1 := c) as [j2 [r2 [Hbody2 HR2]]]; eauto; try lia.
      + eapply T.V_exposed_Forall_r; eauto.
      + rewrite normalize_step; auto.
        eapply T.VM.V_mono_Forall; eauto.
      + exists f2, ρ2', xs2, e2, vs2, ρ4, j2, r2.
        rewrite w_ext_exposedb.
        repeat (split; auto).
        * eapply T.V_exposed_Forall_r; eauto.
        * eapply bstep_fuel_exposed_inv; eauto.
        * rewrite normalize_step in HR2; auto.
          unfold R, R', AnnotateUtil.R' in *.
          destruct r1; destruct r2; try contradiction; auto.
          exists AVext; split; auto.
          eapply V_ext; eauto.
    - (* internal callee *)
      assert (Hesca : aesc A a = false) by (rewrite (Hweb a Ha); auto).
      destruct (V_int_inv _ _ _ _ Hesca HVf) as [l' [Heq Hl']]; subst a.
      simpl in HVf; rewrite Hl' in HVf.
      destruct HVf as [Hwf2 [_ HVf]].
      destruct (a_site A l') as [[g zs | zs] |] eqn:Hsite;
        destruct fv2 as [f2 ρ2' xs2 e2 | c2 vs2']; try contradiction.
      destruct HVf as [Hg [Hzs [Hlen HVf]]]; subst g zs.
      destruct (Happ l' f' xs' Ha Hsite) as [Hsubs Hret].
      assert (HFargs : Forall3 (fun x v1 v2 => exists a, (a \in a_env A x) /\ V (i - (i - i)) a v1 v2) xs' vs vs2).
      { eapply Forall3_Forall2_l; eauto.
        intros y x v1 v2 Hsub [a [Ha' HVa]].
        exists a; split; auto.
        rewrite normalize_step; auto.
        eapply V_mono; eauto. }
      assert (Hlen2 : length xs2 = length vs2).
      { rewrite <- Hlen.
        pose proof (Forall3_length _ _ _ _ HFargs) as [Hl1 Hl2]; lia. }
      destruct (set_lists_length3 (M.set f2 (Tag w_int (A1.Vfun f2 ρ2' xs2 e2)) ρ2') xs2 vs2 Hlen2) as [ρ4 Hset2].
      edestruct (HVf i vs vs2 ρ'' ρ4) with (j1 := c) as [j2 [r2 [Hbody2 HR2]]]; eauto; try lia.
      exists f2, ρ2', xs2, e2, vs2, ρ4, j2, r2.
      rewrite w_int_exposedb.
      do 4 (split; auto).
      split.
      + intros Hc'; contradiction (w_int_not_exposed Hc').
      + rewrite normalize_step in HR2; auto.
        eapply R_subset; eauto.
  Qed.

  Lemma app_compat {ex S f l ys} :
    same_web A (a_env A f) l ->
    app_ok A f l ys S ->
    ex_ok ex S ->
    cfa_correct ex S (A0.Eapp f l ys).
  Proof.
    unfold cfa_correct, E, E'.
    intros Hweb Happ Hex i ρ1 ρ2 HG j1 r1 Hj1 Hstep.
    simpl.
    inv Hstep.
    - exists 0, A1.OOT; split; simpl; auto.
    - name_app_hyps.
      match goal with
      | [ H : A0.bstep_fuel _ _ _ _ |- _ ] => rename H into Hbody
      end.
      destruct i as [| i0]; try lia.
      edestruct (call_compat HG (A0.Free_app1 _ _ _) (A0.free_app_xs_subset _ _ _) Hweb Happ Hgetf Hgets Hset Hbody) as [f2 [ρ2' [xs2 [e2 [vs2 [ρ4 [j2 [r2 [Hgetf2 [Hgets2 [Hset2 [Hbody2 [Hexp HR]]]]]]]]]]]]]; eauto; try lia.
      exists (Datatypes.S j2), r2; split.
      + constructor.
        * econstructor; eauto.
        * eapply R_ex_ok; eauto.
      + eapply R_mono; eauto; lia.
  Qed.

  Lemma letapp_compat {ex S x f l ys k} :
    same_web A (a_env A f) l ->
    app_ok A f l ys (a_env A x) ->
    cfa_correct ex S k ->
    cfa_correct ex S (A0.Eletapp x f l ys k).
  Proof.
    intros Hweb Happ Hk.
    unfold cfa_correct, E, E' in *.
    intros i ρ1 ρ2 HG j1 r1 Hj1 Hstep.
    simpl.
    inv Hstep.
    - exists 0, A1.OOT; split; simpl; auto.
    - name_app_hyps.
      + (* the call returns *)
        match goal with
        | [ H : A0.bstep_fuel _ k _ _ |- _ ] => rename H into Hstepk
        end.
        match goal with
        | [ H : A0.bstep_fuel _ _ _ (A0.Res _) |- _ ] => rename H into Hbody
        end.
        destruct i as [| i0]; try lia.
        edestruct (call_compat HG (A0.Free_letapp2 _ _ _ _ _) (A0.free_letapp_xs_subset _ _ _ _ _) Hweb Happ Hgetf Hgets Hset Hbody) as [f2 [ρ2' [xs2 [e2 [vs2 [ρ4 [j2 [r2 [Hgetf2 [Hgets2 [Hset2 [Hbody2 [Hexp HR]]]]]]]]]]]]]; eauto; try lia.
        destruct r2 as [| v2]; try contradiction.
        edestruct (Hk (i0 - c0) (M.set x v ρ1) (M.set x v2 ρ2)) with (j1 := c') (r1 := r1) as [j3 [r3 [Hstepk2 HR3]]]; eauto; try lia.
        * eapply G_subset.
          -- eapply G_set; eauto.
             eapply G_mono; eauto; lia.
          -- eapply A0.free_letapp_k_subset.
        * exists (Datatypes.S (j2 + j3)), r3; split.
          -- constructor.
             ++ eapply BStep_letapp_Res; eauto.
                intros Hw.
                destruct (Hexp Hw) as [Hexvs Hexr].
                inv Hexr; auto.
             ++ eapply bstep_fuel_ex_inv; eauto.
          -- eapply R_mono; eauto; lia.
      + (* the call runs out of fuel *)
        match goal with
        | [ H : A0.bstep_fuel _ _ _ A0.OOT |- _ ] => rename H into Hbody
        end.
        destruct i as [| i0]; try lia.
        edestruct (call_compat HG (A0.Free_letapp2 _ _ _ _ _) (A0.free_letapp_xs_subset _ _ _ _ _) Hweb Happ Hgetf Hgets Hset Hbody) as [f2 [ρ2' [xs2 [e2 [vs2 [ρ4 [j2 [r2 [Hgetf2 [Hgets2 [Hset2 [Hbody2 [Hexp HR]]]]]]]]]]]]]; eauto; try lia.
        destruct r2 as [| v2]; try contradiction.
        exists (Datatypes.S j2), A1.OOT; split.
        * constructor.
          -- eapply BStep_letapp_OOT; eauto.
             intros Hw.
             destruct (Hexp Hw); auto.
          -- destruct ex; auto.
        * simpl; auto.
  Qed.

  Lemma constr_compat {ex S x l t ys k} :
    (AVlab l \in a_env A x) ->
    (if a_esc A l then
       Forall (fun y => ext_set A (a_env A y)) ys
     else
       a_site A l = Some (Scon ys)) ->
    cfa_correct ex S k ->
    cfa_correct ex S (A0.Econstr x l t ys k).
  Proof.
    intros Hx Hsite Hk.
    unfold cfa_correct, E, E' in *.
    intros i ρ1 ρ2 HG j1 r1 Hj1 Hstep.
    simpl.
    inv Hstep.
    - exists 0, A1.OOT; split; simpl; auto.
    - match goal with
      | [ H : A0.bstep _ _ _ _ |- _ ] => inv H
      end.
      match goal with
      | [ H : get_list _ _ = Some _ |- _ ] => rename H into Hgets
      end.
      match goal with
      | [ H : A0.bstep_fuel _ k _ _ |- _ ] => rename H into Hstepk
      end.
      destruct i as [| i0]; try lia.
      edestruct (G_get_list HG ys) as [vs2 [Hgets2 HFvs]]; eauto.
      { eapply A0.free_constr_xs_subset. }
      pose proof (Vs_wf_val_Forall_r HFvs) as Hwfvs.
      assert (Hexvs : web_of A l \in Exposed -> Forall exposed vs2).
      { unfold web_of.
        destruct (a_esc A l) eqn:Hesc; intros Hw.
        - eapply T.V_exposed_Forall_r.
          eapply Forall3_top; eauto.
        - contradiction (w_int_not_exposed Hw). }
      assert (HV : V i0 (AVlab l) (A0.Tag l (A0.Vconstr t vs)) (Tag (web_of A l) (A1.Vconstr t vs2))).
      { unfold web_of in *.
        destruct (a_esc A l) eqn:Hesc.
        - apply V_esc; simpl; auto.
          eapply T.Vconstr_V; eauto.
          + apply w_ext_exposed.
          + eapply (T.VM.V_mono_Forall (Datatypes.S i0)); try lia.
            eapply Forall3_top; eauto.
        - assert (Hwfv : wf_val (Tag w_int (A1.Vconstr t vs2))).
          { eapply wf_val_Vconstr; eauto. }
          destruct i0 as [| i0']; simpl; rewrite Hesc, Hsite;
            repeat (split; auto).
          + pose proof (Forall3_length _ _ _ _ HFvs) as [Hl1 Hl2]; auto.
          + pose proof (Forall3_length _ _ _ _ HFvs) as [Hl1 Hl2]; auto.
          + eapply Forall3_impl; eauto.
            intros y v1 v2 [a [Ha HVa]].
            exists a; split; auto.
            eapply V_mono; eauto; lia. }
      edestruct (Hk i0 (M.set x (A0.Tag l (A0.Vconstr t vs)) ρ1) (M.set x (Tag (web_of A l) (A1.Vconstr t vs2)) ρ2))
        with (j1 := c) (r1 := r1) as [j2 [r2 [Hstep2 HR]]]; eauto; try lia.
      + eapply G_subset.
        * eapply G_set.
          -- eapply G_mono; eauto; lia.
          -- exists (AVlab l); split; eauto.
        * eapply A0.free_constr_k_subset.
      + exists (Datatypes.S j2), r2; split.
        * constructor.
          -- econstructor; eauto.
          -- eapply bstep_fuel_ex_inv; eauto.
        * eapply R_mono; eauto; lia.
  Qed.

  Lemma proj_compat {ex S x l n y k} :
    same_web A (a_env A y) l ->
    (if a_esc A l then
       AVext \in a_env A x
     else
       forall l' ys y',
         (AVlab l' \in a_env A y) ->
         a_site A l' = Some (Scon ys) ->
         nth_error ys n = Some y' ->
         a_env A y' \subset a_env A x) ->
    cfa_correct ex S k ->
    cfa_correct ex S (A0.Eproj x l n y k).
  Proof.
    intros Hweb Hsite Hk.
    unfold cfa_correct, E, E' in *.
    intros i ρ1 ρ2 HG j1 r1 Hj1 Hstep.
    simpl.
    inv Hstep.
    - exists 0, A1.OOT; split; simpl; auto.
    - match goal with
      | [ H : A0.bstep _ _ _ _ |- _ ] => inv H
      end.
      match goal with
      | [ H : M.get y _ = Some _ |- _ ] => rename H into Hgety
      end.
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] => rename H into Hnth
      end.
      match goal with
      | [ H : A0.bstep_fuel _ k _ _ |- _ ] => rename H into Hstepk
      end.
      destruct i as [| i0]; try lia.
      assert (Hfield : exists vs2 v2,
                 M.get y ρ2 = Some (Tag (web_of A l) (A1.Vconstr t vs2)) /\
                 nth_error vs2 n = Some v2 /\
                 Vs i0 (a_env A x) v v2).
      { edestruct (G_get HG y) as [yv2 [Hgety2 [a [Ha HVy]]]]; eauto.
        destruct yv2 as [w2 yv2].
        pose proof (V_web HVy) as Hw2.
        rewrite (same_web_web Hweb Ha) in Hw2; subst w2.
        unfold web_of in *.
        destruct (a_esc A l) eqn:Hesc.
        - assert (Hesca : aesc A a = true) by (rewrite (Hweb a Ha); auto).
          apply (V_esc _ _ _ _ Hesca) in HVy.
          unfold T.V in HVy; simpl in HVy.
          destruct HVy as [Hwf2 HVy].
          rewrite w_ext_exposedb in HVy.
          destruct HVy as [Hexy HVy].
          destruct yv2 as [f2 ρ2' xs2 e2 | c2 vs2]; simpl in HVy; try contradiction.
          destruct HVy as [Hc HF]; subst c2.
          rewrite normalize_step in HF; auto.
          destruct (Forall2_nth_error Hnth HF) as [v2 [Hnth2 HV2]].
          exists vs2, v2; repeat (split; auto).
          exists AVext; split; auto.
          eapply V_ext; eauto.
        - assert (Hesca : aesc A a = false) by (rewrite (Hweb a Ha); auto).
          destruct (V_int_inv _ _ _ _ Hesca HVy) as [l' [Heq Hl']]; subst a.
          simpl in HVy; rewrite Hl' in HVy.
          destruct HVy as [Hwf2 [_ HVy]].
          destruct (a_site A l') as [[g zs | ys] |] eqn:Hs;
            destruct yv2 as [f2 ρ2' xs2 e2 | c2 vs2]; try contradiction.
          destruct HVy as [Hc HF]; subst c2.
          destruct (Forall3_nth_error _ _ _ _ _ _ HF Hnth) as [y' [v2 [Hnth1 [Hnth2 [a [Ha' HV2]]]]]].
          exists vs2, v2; repeat (split; auto).
          exists a; split; auto.
          eapply Hsite; eauto. }
      destruct Hfield as [vs2 [v2 [Hgety2 [Hnth2 HV2]]]].
      edestruct (Hk i0 (M.set x v ρ1) (M.set x v2 ρ2)) with (j1 := c) (r1 := r1) as [j2 [r2 [Hstep2 HR]]]; eauto; try lia.
      + eapply G_subset.
        * eapply G_set; eauto.
          eapply G_mono; eauto; lia.
        * eapply A0.free_proj_k_subset.
      + exists (Datatypes.S j2), r2; split.
        * constructor.
          -- econstructor; eauto.
          -- eapply bstep_fuel_ex_inv; eauto.
        * eapply R_mono; eauto; lia.
  Qed.

  Lemma V_constr_inv {i a w1 t vs1 w2 v2} :
    V i a (A0.Tag w1 (A0.Vconstr t vs1)) (Tag w2 v2) ->
    exists vs2, v2 = A1.Vconstr t vs2.
  Proof.
    intros HV.
    destruct (aesc A a) eqn:Hesc.
    - apply (V_esc _ _ _ _ Hesc) in HV.
      unfold T.V in HV.
      destruct i; simpl in HV; destruct HV as [Hwf HV];
        destruct (exposedb w2); try contradiction;
        destruct HV as [Hex HV];
        destruct v2 as [f2 ρ2 xs2 e2 | c2 vs2]; simpl in HV; try contradiction;
        destruct HV as [Hc _]; subst; eauto.
    - destruct (V_int_inv _ _ _ _ Hesc HV) as [l [Heq Hl]]; subst a.
      destruct i; simpl in HV; rewrite Hl in HV;
        destruct HV as [Hwf [_ HV]];
        destruct (a_site A l) as [[g zs | ys] |];
        destruct v2 as [f2 ρ2 xs2 e2 | c2 vs2]; try contradiction;
        destruct HV as [Hc _]; subst; eauto.
  Qed.

  Lemma case_nil_compat {ex S x l} :
    cfa_correct ex S (A0.Ecase x l []).
  Proof.
    unfold cfa_correct, E, E'.
    intros i ρ1 ρ2 HG j1 r1 Hj1 Hstep.
    inv Hstep.
    - exists 0, A1.OOT; split; simpl; auto.
    - match goal with
      | [ H : A0.bstep _ _ _ _ |- _ ] => inv H
      end.
      match goal with
      | [ H : find_tag [] _ _ |- _ ] => inv H
      end.
  Qed.

  Lemma case_cons_compat {ex S x l c e cl} :
    same_web A (a_env A x) l ->
    cfa_correct ex S e ->
    cfa_correct ex S (A0.Ecase x l cl) ->
    cfa_correct ex S (A0.Ecase x l ((c, e) :: cl)).
  Proof.
    intros Hweb He Hcl.
    unfold cfa_correct, E, E' in *.
    intros i ρ1 ρ2 HG j1 r1 Hj1 Hstep.
    simpl in *.
    inv Hstep.
    - exists 0, A1.OOT; split; simpl; auto.
    - match goal with
      | [ H : A0.bstep _ _ _ _ |- _ ] => inv H
      end.
      match goal with
      | [ H : M.get x _ = Some _ |- _ ] => rename H into Hgetx
      end.
      match goal with
      | [ H : find_tag _ _ _ |- _ ] => rename H into Hfind
      end.
      match goal with
      | [ H : A0.bstep_fuel _ _ _ _ |- _ ] => rename H into Hbody
      end.
      edestruct (G_get HG x) as [xv2 [Hgetx2 [a [Ha HVx]]]]; eauto.
      destruct xv2 as [w2 xv2].
      pose proof (V_web HVx) as Hw2.
      rewrite (same_web_web Hweb Ha) in Hw2; subst w2.
      destruct (V_constr_inv HVx) as [vs2 Heq]; subst xv2.
      inv Hfind.
      + (* the first branch *)
        edestruct (He i ρ1 ρ2) with (j1 := c0) (r1 := r1) as [j2 [r2 [Hstep2 HR]]]; eauto; try lia.
        * eapply G_subset; eauto.
          eapply A0.free_case_hd_subset.
        * exists (Datatypes.S j2), r2; split.
          -- constructor.
             ++ econstructor; eauto.
             ++ eapply bstep_fuel_ex_inv; eauto.
          -- eapply R_mono; eauto; lia.
      + (* the remaining branches *)
        match goal with
        | [ H : find_tag cl _ _ |- _ ] => rename H into Hfind'
        end.
        edestruct (Hcl i ρ1 ρ2) with (j1 := Datatypes.S c0) (r1 := r1) as [j2 [r2 [Hstep2 HR]]]; eauto.
        * eapply G_subset; eauto.
          eapply A0.free_case_tl_subset.
        * inv Hstep2.
          -- exists 0, A1.OOT; split; auto.
          -- match goal with
             | [ H : A1.bstep _ _ _ _ _ |- _ ] => inv H
             end.
             match goal with
             | [ H : M.get x ρ2 = Some _ |- _ ] => rewrite Hgetx2 in H; inv H
             end.
             exists (Datatypes.S c1), r2; split; auto.
             constructor; auto.
             econstructor; eauto.
  Qed.

End Relations.

(* Fundamental Property *)
Theorem fundamental_property {A e R} :
  check A e R ->
  forall ex,
    ex_ok A ex R ->
    cfa_correct A ex R e.
Proof.
  intros Hcheck.
  induction Hcheck as [ x R Hsub
                      | f l xs e k R Hf Hsite He IHe Hk IHk
                      | f l ys R Hweb Happ
                      | x f l ys k R Hweb Happ Hk IHk
                      | x l t ys k R Hx Hsite Hk IHk
                      | x l n y k R Hweb Hsite Hk IHk
                      | x l R Hweb
                      | x l c e cl R Hweb He IHe Hcl IHcl ];
    intros ex Hex.
  - eapply ret_compat; eauto.
  - eapply fun_compat; eauto.
    eapply IHe.
    intros Hesc; rewrite Hesc in Hsite.
    destruct Hsite as [_ Hret]; auto.
  - eapply app_compat; eauto.
  - eapply letapp_compat; eauto.
  - eapply constr_compat; eauto.
  - eapply proj_compat; eauto.
  - eapply case_nil_compat; eauto.
  - eapply case_cons_compat; eauto.
Qed.

(* Top Level *)
Theorem top A R e :
  check_top A R e ->
  T.trans_correct e (annotate A e).
Proof.
  unfold check_top, T.trans_correct.
  intros [Hcheck [Hext Hfree]].
  split.
  - eapply annotate_occurs_free.
  - intros i ρ1 ρ2 HG.
    eapply E_top; eauto.
    eapply (fundamental_property Hcheck true (fun _ => Hext)).
    eapply G_top_G; eauto.
Qed.

(* Adequacy *)
Theorem adequacy e1 e2 :
  T.trans_correct e1 e2 ->
  forall ρ1 ρ2,
    (forall k, T.G k (A0.occurs_free e1) ρ1 ρ2) ->
    forall j1 r1,
      A0.bstep_fuel ρ1 e1 j1 r1 ->
      exists j2 r2,
        A1.bstep_fuel true ρ2 e2 j2 r2 /\
        (forall k, T.R k r1 r2).
Proof.
  unfold T.trans_correct, T.E, T.VM.E, AnnotateUtil.E'.
  intros [HS HT] ρ1 ρ2 HG j1 r1 Hstep.
  edestruct (HT j1 ρ1 ρ2 (HG j1) j1 r1) as [j2 [r2 [Hstep2 HR]]]; eauto.
  exists j2, r2; split; auto.
  intros k.
  edestruct (HT (j1 + k) ρ1 ρ2 (HG (j1 + k)) j1 r1) as [j2' [r2' [Hstep2' HR']]]; eauto; try lia.
  rewrite_math (j1 + k - j1 = k).
  unfold T.R, T.VM.R, AnnotateUtil.R' in *.
  destruct r1 as [| v1]; destruct r2 as [| v2]; destruct r2' as [| v2']; auto; try contradiction.
  destruct (A1.bstep_fuel_deterministic v2 v2' Hstep2 Hstep2') as [Heq _]; subst; eauto.
Qed.

(* Every program admits an acceptable analysis result:
   the trivial one, where everything interacts with the context.
   Its annotation places everything in the exposed web `w_ext`. *)
Definition trivial_analysis : analysis :=
  mk_analysis
    (fun _ => Full_set _)
    (fun _ => Full_set _)
    (fun _ => None)
    (fun _ => true).

Lemma trivial_ext_set S :
  ext_set trivial_analysis S.
Proof.
  intros a Ha.
  destruct a; auto.
Qed.

Lemma trivial_check e :
  check trivial_analysis e (Full_set _).
Proof.
  induction e using A0.exp_ind'; constructor; simpl; auto;
    repeat split;
    try solve [ constructor
              | intros a Ha; destruct a; auto
              | apply trivial_ext_set
              | apply Forall_forall; intros y Hy; solve [ constructor | apply trivial_ext_set ] ].
Qed.

Lemma trivial_check_top e :
  check_top trivial_analysis (Full_set _) e.
Proof.
  unfold check_top.
  repeat split.
  - apply trivial_check.
  - apply trivial_ext_set.
Qed.

(* Linking Preservation *)
Theorem preserves_linking f x e1 e2 e1' e2' :
  T.trans_correct e1 e1' ->
  T.trans_correct e2 e2' ->
  T.trans_correct (A0.link f x e1 e2) (A1.link f w_ext x e1' e2').
Proof.
  unfold A0.link, A1.link.
  intros HT1 HT2.
  eapply T.fun_compat; eauto.
  - apply w_ext_exposed.
  - eapply T.letapp_compat; eauto.
    + apply w_ext_exposed.
    + apply w_ext_unique.
Qed.

(* Separately analyzed and annotated compilation units can be linked. *)
Corollary annotate_preserves_linking f x An1 An2 R1 R2 e1 e2 :
  check_top An1 R1 e1 ->
  check_top An2 R2 e2 ->
  T.trans_correct (A0.link f x e1 e2) (A1.link f w_ext x (annotate An1 e1) (annotate An2 e2)).
Proof.
  intros HC1 HC2.
  eapply preserves_linking; eapply top; eauto.
Qed.

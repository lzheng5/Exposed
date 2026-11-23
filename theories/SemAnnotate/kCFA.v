From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From SemAnnotate Require Import LabeledANF.

(* kCFA *)
(* Please note that everything related to the analysis is *static*. *)

(* --------------------------------------------------------------- *)
(* The Unknown/Foreign Side                                          *)
(* --------------------------------------------------------------- *)

(* Everything the analysis does not see is summarised by two dedicated labels:
     - [l_top_intro]: *every* value that originates outside the analysed unit
     - [l_top_elim]: *every* elimination performed outside the analysed unit *)
Parameter l_top_intro l_top_elim : label.

(* Interaction Set *)
(* Each pair has the format (l_intro, l_elim). *)
Definition ainteraction : Type := (label * label).
Definition ainteractions := Ensemble ainteraction.

(* --------------------------------------------------------------- *)
(* Contexts                                                          *)
(* --------------------------------------------------------------- *)

(* Call String, most recent call site first. *)
Definition calls := list label.

(* Precision of the CFA *)
Parameter k : nat.

(* Keep only the [k] most recent call sites. *)
Definition truncate (δ : calls) : calls := firstn k δ.

(* The context entered by a call made at site [l] from context [δ]. *)
Definition push (l : label) (δ : calls) : calls := truncate (l :: δ).

(* Abstract binding environment: the context in which each variable in scope
     was bound.  It is the abstraction of a concrete environment [ρ], and is
     kept as a [M.t] so that it can be read off [ρ] by [M.map]. *)
Definition abenv := M.t calls.

Definition abenv_get (β : abenv) (x : var) : calls :=
  match M.get x β with
  | Some δ => δ
  | None => []
  end.

(* Bind every variable of [xs] in context [δ]. *)
Definition abenv_set (xs : list var) (δ : calls) (β : abenv) : abenv :=
  fold_right (fun x β => M.set x δ β) β xs.

(* --------------------------------------------------------------- *)
(* Abstract values                                                   *)
(* --------------------------------------------------------------- *)

(* An abstract value is an allocation site, summarised:
     - a closure is its introduction label together with its (syntactic) code
       and the binding environment it closes over -- the latter says in which
       context each free variable of the body has to be looked up;
     - a constructor is its introduction label together with its tag -- its
       fields are read back through the field set [ai_fld] of that label,
       which is what makes the domain finite;
     - [AVtop] is the single abstract value standing for everything unknown:
       any foreign value, and any of our values that has escaped to the
       context.  Its introduction clabel is [l_top_intro]. *)
Inductive aval : Type :=
| AVtop : aval
| AVfun : label -> abenv -> var -> list var -> exp -> aval
| AVconstr : label -> ctor_tag -> aval.

Definition avals := Ensemble aval.

Definition label_of (av : aval) : label :=
  match av with
  | AVtop => l_top_intro
  | AVfun l _ _ _ _ => l
  | AVconstr l _ => l
  end.

(* Abstract environment (store): one value set per variable and the context it
     was bound in (polyvariant). *)
Definition aenv := (var * calls) -> avals.

(* Abstract return sets, keyed by the closure's introduction label and the
     context its body is entered in. *)
Definition aret := (label * calls) -> avals.

(* Abstract field sets, keyed by the constructor's introduction label: every
     field of every constructor allocated at a site is collected in [afld] at
     that site (field- and context-insensitive; the field values themselves
     still carry their binding environments). *)
Definition afld := label -> avals.

(* Abstract entry contexts, keyed by the closure's introduction label: every
     context in which the body may be entered. *)
Definition actx := label -> Ensemble calls.

(* --------------------------------------------------------------- *)
(* The analysis result                                             *)
(* --------------------------------------------------------------- *)
Record analysis_result : Type :=
  mk_analysis_result {
      ai_env : aenv;           (* value sets                                 *)
      ai_ret : aret;           (* return sets                                *)
      ai_fld : afld;           (* field sets                                 *)
      ai_ctx : actx;           (* entry contexts                             *)
      ai_esc : avals;          (* values that may escape to the context      *)
      ai_int : ainteractions   (* statically predicted interactions          *)
    }.

(* The value set of [x] in scope [β]: look [x] up at the context it was bound in. *)
Definition aeval (A : analysis_result) (β : abenv) (x : var) : avals :=
  ai_env A (x, abenv_get β x).

(* What the context may do with a value we handed it.  [ai_esc] has to be closed
     under this: the context can eliminate an escaped value, call an escaped
     closure with arbitrary (hence unknown) arguments and keep whatever it
     returns, and project out of an escaped constructor.  The context may call
     an escaped closure from any call site and any call string, so its body has
     to be entered in every context [δ]. *)
Definition escapes_ok (A : analysis_result) : Prop :=
  (forall av,
      (av \in ai_esc A) ->
      ((label_of av, l_top_elim) \in ai_int A)) /\
    (forall l β f xs e,
        (AVfun l β f xs e \in ai_esc A) ->
        forall δ,
          (δ \in ai_ctx A l) /\
          (AVfun l β f xs e \in ai_env A (f, δ)) /\
          (forall x, List.In x xs -> (AVtop \in aeval A (abenv_set xs δ (M.set f δ β)) x)) /\ (* [AVtop] only flows into the variable under [δ] *)
          (ai_ret A (l, δ) \subset ai_esc A)) /\
    (forall l t,
        (AVconstr l t \in ai_esc A) ->
        (ai_fld A l \subset ai_esc A)).

(* --------------------------------------------------------------- *)
(* The Abstract Semantics                                            *)
(* --------------------------------------------------------------- *)

(* Interactions at Elimination Sites *)
(* The call site `l` eliminates everything that reaches `f`; since `AVtop`
   also stands for our own escaped closures, it eliminates each of them as
   well. *)
Definition aelim_fun_int (A : analysis_result) (β : abenv) (f : var) (l : label) : Prop :=
  (forall av, (av \in aeval A β f) -> ((label_of av, l) \in ai_int A)) /\
    ((AVtop \in aeval A β f) ->
     forall l' β' f' xs' e', (AVfun l' β' f' xs' e' \in ai_esc A) -> ((l', l) \in ai_int A)).

(* The elimination site `l` of a constructor held in `y` (by a projection or
   a case) eliminates everything that reaches `y`; since `AVtop` also stands
   for our own escaped constructors, it eliminates each of them as well. *)
Definition aelim_constr_int (A : analysis_result) (β : abenv) (y : var) (l : label) : Prop :=
  (forall av, (av \in aeval A β y) -> ((label_of av, l) \in ai_int A)) /\
    ((AVtop \in aeval A β y) ->
     forall l' t, (AVconstr l' t \in ai_esc A) -> ((l', l) \in ai_int A)).

(* [acheck A δ β e R] reads: the analysis result [A] is acceptable
     for [e], analysed in context [δ] with the variables in scope bound as
     described by [β], and [R] over-approximates the values [e] may return.
     This is the "abstract semantics": a declarative
     constraint system rather than a fixpoint computation, so any solver that
     produces an [analysis_result] may be plugged in and checked against it. *)
Inductive acheck (A : analysis_result) : calls -> abenv -> exp -> avals -> Prop :=
| Acheck_ret :
  forall {δ β x R},
    (aeval A β x \subset R) ->
    acheck A δ β (Eret x) R

| Acheck_fun :
  forall {δ β f l xs e k R},
    (* the closure introduced here, closing over [β], flows into [f] *)
    (AVfun l β f xs e \in ai_env A (f, δ)) ->
    (* its body is analysed here, once per context it may be entered in, and
       returns into [ai_ret A (l, δ')] *)
    (forall δ',
        (δ' \in ai_ctx A l) ->
        acheck A δ' (abenv_set xs δ (M.set f δ' β)) e (ai_ret A (l, δ'))) ->
    acheck A δ (M.set f δ β) k R ->
    acheck A δ β (Efun f l xs e k) R

| Acheck_app :
  forall {δ β f l xs R},
    (* the call site l eliminates everything that reaches [f] *)
    aelim_fun_int A β f l ->

    (* internal call: the callee is entered in context [push l δ]; arguments
       flow to parameters, results flow out.  Only callees of the call's arity
       are constrained: a call of any other arity gets stuck (`set_lists`
       fails), so it never needs a flow *)
    (forall l' β' f' xs' e',
        (AVfun l' β' f' xs' e' \in aeval A β f) ->
        length xs = length xs' ->
          (push l δ \in ai_ctx A l') /\
          (AVfun l' β' f' xs' e' \in ai_env A (f', push l δ)) /\
          Forall2 (fun x x' => aeval A β x \subset ai_env A (x', push l δ)) xs xs' /\
          (ai_ret A (l', push l δ) \subset R)) ->

    (* unknown callee: the arguments escape and the result is unknown; since
       `AVtop` also stands for our own escaped closures, the callee may be any
       of them, which is then called as a known callee *)
    ((AVtop \in aeval A β f) ->
       Forall (fun x => aeval A β x \subset ai_esc A) xs /\ (* each argument can escape *)
       (AVtop \in R) /\ (* result is unknown *)
       (forall l' β' f' xs' e',
           (AVfun l' β' f' xs' e' \in ai_esc A) ->
             length xs = length xs' ->
             (push l δ \in ai_ctx A l') /\
             (AVfun l' β' f' xs' e' \in ai_env A (f', push l δ)) /\
             Forall2 (fun x x' => aeval A β x \subset ai_env A (x', push l δ)) xs xs' /\ (* call the escaping function with the current arguments *)
             (ai_ret A (l', push l δ) \subset R))) -> (* what each escaping function may return can also be returned from this callsite *)

    acheck A δ β (Eapp f l xs) R.

Hint Constructors acheck : core.


(* Checking Semantics With Respect to Colored Label Pair Set *)

(* Color *)
Definition color := nat.
Definition colors := Ensemble nat.

(* Colored Label *)
Definition clabel : Type := (color * label).
Definition clabels : Type := Ensemble clabel.

(* Interaction Set *)
(* Each pair has the format (l_intro, l_elim). *)
Definition interaction : Type := (clabel * clabel).
Definition interactions := Ensemble interaction.

(* Tagged Value *)
Inductive ctag A : Type :=
| CTAG : analysis_result -> clabel -> A -> ctag A.

Hint Constructors ctag : core.

(* Value *)
(* A closure records, next to its captured environment `ρ`, the abstract
   binding environment `β` it was created under: the context in which each
   variable of `ρ` was bound.  This pins down the abstract value of the
   closure, `AVfun l β f xs e`. *)
Inductive cval : Type :=
| CVfun : var -> M.t (ctag cval) -> abenv -> list var -> exp -> cval
| CVconstr : ctor_tag -> list (ctag cval) -> cval.

Hint Constructors cval : core.

Definition clval := ctag cval.

Definition CTag A c l cv := CTAG cval A (c, l) cv.

(* Environment *)
Definition cenv := M.t clval.

(* Result *)
Inductive cres : Type :=
| COOT
| CRes : clval -> cres.

Hint Constructors cres : core.

(* Free variables of a closure: those of its body, minus its parameters and
   its own name. *)
Definition fun_fv (f : var) (xs : list var) (e : exp) : vars :=
  fun y => (y \in occurs_free e) /\ ~ List.In y xs /\ y <> f.

(* The body of a closure only reads its parameters, its own name, and its free
   variables. *)
Lemma occurs_free_fun_fv f xs e :
  occurs_free e \subset FromList xs :|: (f |: fun_fv f xs e).
Proof.
  intros y Hy.
  destruct (in_dec M.elt_eq y xs) as [Hin | Hnin].
  - apply Union_introl; exact Hin.
  - apply Union_intror.
    destruct (M.elt_eq y f) as [-> | Hneq].
    + apply Union_introl; apply In_singleton.
    + apply Union_intror; unfold fun_fv, Ensembles.In; auto.
Qed.

Lemma fun_fv_subset f xs e Γ :
  occurs_free e \subset FromList xs :|: (f |: Γ) ->
  fun_fv f xs e \subset Γ.
Proof.
  intros HS y [Hy [Hxs Hf]].
  destruct (HS y Hy) as [y' Hy' | y' Hy'].
  - contradiction.
  - inv Hy'; [inv H; contradiction | assumption].
Qed.

(* Approximation *)
(* `approx_val av v`: the abstract value `av` over-approximates the concrete
   value `v`, with respect to the analysis result carried by the tag of `v`.
   - [AVtop] stands for everything unknown, so it approximates any value;
   - otherwise `av` must share the introduction label of `v` and approximate
     the untagged value under the tag's analysis result. *)
Inductive approx_val : aval -> clval -> Prop :=
| Approx_top :
  forall v,
    approx_val AVtop v

| Approx_TAG :
  forall A c l av v,
    label_of av = l ->
    approx_val' A av v ->
    approx_val av (CTag A c l v)

(* A closure is approximated by its own allocation site, under the abstract
   binding environment `β` it records, provided that its captured environment
   is approximated by `A` under `β` at the free variables of the closure. *)
with approx_val' : analysis_result -> aval -> cval -> Prop :=
| Approx_CVfun :
  forall A l β f ρ xs e,
    approx_env (ai_env A) β (fun_fv f xs e) ρ ->
    approx_val' A (AVfun l β f xs e) (CVfun f ρ β xs e)

(* A constructor is approximated by its own allocation site.  Its fields are
   approximated by the field set of that site, which the logical relation
   records for every constructor it relates. *)
| Approx_CVconstr :
  forall A l t vs,
    approx_val' A (AVconstr l t) (CVconstr t vs)

(* Every value bound in `ρ` at a variable of `Γ` is approximated by some
   abstract value in the value set of its variable, looked up under `β` as
   `aeval` does. *)
with approx_env : aenv -> abenv -> vars -> cenv -> Prop :=
| Approx_env :
  forall AE β Γ ρ,
    (forall x v,
        (x \in Γ) ->
        ρ ! x = Some v ->
        exists av, (av \in AE (x, abenv_get β x)) /\ approx_val av v) ->
    approx_env AE β Γ ρ.

Hint Constructors approx_val : core.
Hint Constructors approx_val' : core.
Hint Constructors approx_env : core.

Scheme approx_val_mut := Induction for approx_val Sort Prop
with approx_val'_mut := Induction for approx_val' Sort Prop
with approx_env_mut := Induction for approx_env Sort Prop.

(* `v` is approximated by some abstract value in `avs`. *)
Definition approx_vals (avs : avals) (v : clval) : Prop :=
  exists av, (av \in avs) /\ approx_val av v.

Lemma approx_vals_subset {AE x' v} {x : var}:
  approx_vals (AE x) v ->
  (AE x) \subset (AE x') ->
  approx_vals (AE x') v.
Proof. unfold approx_vals. fcrush. Qed.

Lemma approx_vals_subset_list {AE xs vs2} :
  Forall2 (fun (x : var) (v : clval) => approx_vals (AE x) v) xs vs2 ->
  forall xs',
    Forall2 (fun x x' : var => AE x \subset AE x') xs xs' ->
    Forall2 (fun (x : var) (v1 : clval) => approx_vals (AE x) v1) xs' vs2.
Proof.
  intro H.
  induction H; intros; simpl.
  - inv H; auto.
  - inv H1.
    constructor; auto.
    eapply approx_vals_subset; eauto.
Qed.

Lemma set_lists_approx_top {AE xs vs ρ ρ'} :
  (forall x, List.In x xs -> AVtop \in AE x) ->
  set_lists xs vs ρ = Some ρ' ->
  Forall2 (fun x v => approx_vals (AE x) v) xs vs.
Proof.
  intros Htop.
  revert vs ρ ρ' Htop.
  induction xs as [| x xs IHxs]; intros vs ρ ρ' Htop Hset.
  - destruct vs as [| v vs]; [constructor | discriminate Hset].
  - destruct vs as [| v vs]; [discriminate Hset |].
    simpl in Hset.
    destruct (set_lists xs vs ρ) as [ρ'' |] eqn:Heq; [| discriminate Hset].
    constructor.
    + (* `AVtop` approximates every value *)
      exists AVtop; split; [apply Htop; left; reflexivity | constructor].
    + eapply IHxs; [| exact Heq].
      intros y Hy; apply Htop; right; exact Hy.
Qed.

Lemma approx_env_get {AE β Γ ρ x v} :
  approx_env AE β Γ ρ ->
  (x \in Γ) ->
  ρ ! x = Some v ->
  approx_vals (AE (x, (abenv_get β x))) v.
Proof. intros Henv Hx Hget; inv Henv; unfold approx_vals; eauto. Qed.

Lemma approx_env_subset {AE β Γ Γ' ρ} :
  approx_env AE β Γ ρ ->
  Γ' \subset Γ ->
  approx_env AE β Γ' ρ.
Proof. intros Henv Hsub; inv Henv; constructor; eauto. Qed.

(*
Lemma approx_env_set {AE β Γ ρ} x v :
  approx_env AE β Γ ρ ->
  approx_vals (AE x) v ->
  approx_env AE (x |: Γ) (M.set x v ρ).
Proof.
  intros Henv Hv.
  inv Henv.
  constructor; intros y w Hy Hget.
  destruct (M.elt_eq x y); subst.
  - rewrite M.gss in Hget; inv Hget; exact Hv.
  - rewrite M.gso in Hget by auto.
    inv Hy; [inv H0; contradiction | eauto].
Qed.

Lemma approx_env_get_list {AE Γ ρ} :
  approx_env AE Γ ρ ->
  forall xs vs,
    FromList xs \subset Γ ->
    get_list xs ρ = Some vs ->
    Forall2 (fun x v => approx_vals (AE x) v) xs vs.
Proof.
  intros Henv xs.
  induction xs as [| x xs IHxs]; simpl; intros vs Hxs Hget.
  - inv Hget; constructor.
  - destruct (M.get x ρ) as [v |] eqn:Hx; [| discriminate Hget].
    destruct (get_list xs ρ) as [vs' |] eqn:Hxs'; [| discriminate Hget].
    inv Hget.
    constructor.
    + eapply approx_env_get; eauto.
      apply Hxs; left; reflexivity.
    + eapply IHxs; eauto.
      intros y Hy; apply Hxs; right; exact Hy.
Qed.

Lemma approx_env_set_lists {AE Γ ρ} :
  approx_env AE Γ ρ ->
  forall xs vs ρ',
    Forall2 (fun x v => approx_vals (AE x) v) xs vs ->
    set_lists xs vs ρ = Some ρ' ->
    approx_env AE (FromList xs :|: Γ) ρ'.
Proof.
  intros Henv xs.
  induction xs as [| x xs IHxs]; intros vs ρ' Hall Hset; simpl in Hset.
  - destruct vs as [| v vs]; [| discriminate Hset].
    inv Hset.
    eapply approx_env_subset; [exact Henv |].
    intros y Hy; inv Hy; [inv H | exact H].
  - destruct vs as [| v vs]; [discriminate Hset |].
    destruct (set_lists xs vs ρ) as [ρ'' |] eqn:Heq; [| discriminate Hset].
    inv Hset.
    inv Hall.
    apply (approx_env_subset (Γ := x |: (FromList xs :|: Γ))).
    + apply approx_env_set; [eapply IHxs; eauto | eassumption].
    + intros y Hy.
      inv Hy.
      * destruct H as [-> | Hin].
        -- apply Union_introl; apply In_singleton.
        -- apply Union_intror; apply Union_introl; exact Hin.
      * apply Union_intror; apply Union_intror; exact H.
Qed.

(* A result is approximated by `R` if it is out of time, or returns a value
   approximated by some abstract value in `R`. *)
Inductive approx_res : avals -> cres -> Prop :=
| Approx_OOT :
  forall R,
    approx_res R COOT

| Approx_res :
  forall R av v,
    (av \in R) ->
    approx_val av v ->
    approx_res R (CRes v).

Hint Constructors approx_res : core.

Lemma approx_res_subset Rs Rs' r :
  approx_res Rs r ->
  Rs \subset Rs' ->
  approx_res Rs' r.
Proof. intros. inv H; fcrush. Qed.
*)

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

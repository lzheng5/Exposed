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

(* Precision of the CFA *)
Parameter k : nat.

(* Keep only the [k] most recent call sites. *)
Definition truncate {A : Type} (xs : list A) := firstn k xs.

(* The context entered by a call made at site [l] from context [δ]. *)
Definition push {A : Type} (x : A) (xs : list A) : list A := truncate (x :: xs).

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

(* Abstract call String, most recent call site first. *)
Definition acalls := list label.

(* Abstract binding environment: the context in which each variable in scope
     was bound.  It is the abstraction of a concrete environment [ρ], and is
     kept as a [M.t] so that it can be read off [ρ] by [M.map]. *)
Definition abenv := M.t acalls.

Definition abenv_get (β : abenv) (x : var) : acalls :=
  match M.get x β with
  | Some δ => δ
  | None => []
  end.

Definition abenv_set (x : var) (δ : acalls) (β : abenv) : abenv :=
  M.set x δ β.

(* Bind every variable of [xs] in context [δ]. *)
Definition abenv_set_list (xs : list var) (δ : acalls) (β : abenv) : abenv :=
  fold_right (fun x β => abenv_set x δ β) β xs.

Lemma abenv_get_set_eq x δ β :
  abenv_get (abenv_set x δ β) x = δ.
Proof. unfold abenv_get, abenv_set; rewrite M.gss; reflexivity. Qed.

Lemma abenv_get_set_neq x y δ β :
  x <> y ->
  abenv_get (abenv_set x δ β) y = abenv_get β y.
Proof. intros Hxy; unfold abenv_get, abenv_set; rewrite M.gso by congruence; reflexivity. Qed.

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
| AVfun : label -> var -> abenv -> list var -> exp -> aval
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
Definition aenv := (var * acalls) -> avals.

(* Abstract return sets, keyed by the closure's introduction label and the
     context its body is entered in. *)
Definition aret := (label * acalls) -> avals.

(* Abstract field sets, keyed by the constructor's introduction label: every
     field of every constructor allocated at a site is collected in [afld] at
     that site (field- and context-insensitive; the field values themselves
     still carry their binding environments). *)
Definition afld := label -> avals.

(* Abstract entry contexts, keyed by the closure's introduction label: every
     context in which the body may be entered. *)
Definition actx := label -> Ensemble acalls.

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
        (AVfun l f β xs e \in ai_esc A) ->
        forall δ,
          (δ \in ai_ctx A l) /\
          (AVfun l f β xs e \in ai_env A (f, δ)) /\
          (forall x, List.In x xs -> (AVtop \in aeval A (abenv_set_list xs δ (M.set f δ β)) x)) /\ (* [AVtop] only flows into the variable under [δ] *)
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
     forall l' f' β' xs' e', (AVfun l' f' β' xs' e' \in ai_esc A) -> ((l', l) \in ai_int A)).

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
Inductive acheck (A : analysis_result) : acalls -> abenv -> exp -> avals -> Prop :=
| Acheck_ret :
  forall {δ β x R},
    (aeval A β x \subset R) ->
    acheck A δ β (Eret x) R

| Acheck_fun :
  forall {δ β f l xs e k R},
    (* the closure introduced here, closing over [β], flows into [f] *)
    (AVfun l f β xs e \in ai_env A (f, δ)) ->
    (* its body is analysed here, once per context it may be entered in, and
       returns into [ai_ret A (l, δ')] *)
    (forall δ',
        (δ' \in ai_ctx A l) ->
        acheck A δ' (abenv_set_list xs δ (M.set f δ' β)) e (ai_ret A (l, δ'))) ->
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
    (forall l' f' β' xs' e',
        (AVfun l' f' β' xs' e' \in aeval A β f) ->
        length xs = length xs' ->
          (push l δ \in ai_ctx A l') /\
          (AVfun l' f' β' xs' e' \in ai_env A (f', push l δ)) /\
          Forall2 (fun x x' => aeval A β x \subset ai_env A (x', push l δ)) xs xs' /\
          (ai_ret A (l', push l δ) \subset R)) ->

    (* unknown callee: the arguments escape and the result is unknown; since
       `AVtop` also stands for our own escaped closures, the callee may be any
       of them, which is then called as a known callee *)
    ((AVtop \in aeval A β f) ->
       Forall (fun x => aeval A β x \subset ai_esc A) xs /\ (* each argument can escape *)
       (AVtop \in R) /\ (* result is unknown *)
       (forall l' f' β' xs' e',
           (AVfun l' f' β' xs' e' \in ai_esc A) ->
             length xs = length xs' ->
             (push l δ \in ai_ctx A l') /\
             (AVfun l' f' β' xs' e' \in ai_env A (f', push l δ)) /\
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
   closure, `AVfun l f β xs e`. *)
(* Why `β` belongs to `cval` instead of `ctag`?
   Note a tag belongs to a value, but a binding context belongs to a binding.
   The same value can be bound in several places at once:
   - at (x, δ) in the caller and
   - at (x', push l δ) in the callee.
   No single per-value β can describe both. *)
Inductive cval : Type :=
| CVfun : var -> M.t (ctag cval) -> abenv -> list var -> exp -> cval
| CVconstr : ctor_tag -> list (ctag cval) -> cval.

Hint Constructors cval : core.

Definition clval := ctag cval.

Definition CTag A c l cv := CTAG cval A (c, l) cv.

(* The abstract value of a value allocated at `l`. *)
Definition aval_of (l : label) (v : cval) : aval :=
  match v with
  | CVfun f _ β xs e => AVfun l f β xs e
  | CVconstr t _ => AVconstr l t
  end.

(* Environment *)
Definition cenv := M.t clval.

(* Result *)
Inductive cres : Type :=
| COOT
| CRes : clval -> cres.

Hint Constructors cres : core.

(* Concrete call strings *)
Definition calls := list clabel.

(* The abstract call site of a colored call site, as seen from the unit
   wearing color `c`: one of our call sites is itself, a foreign call site is
   `l_top_elim`. *)
Definition aclabel_of (c : color) (cl : clabel) : label :=
  let (c', l) := cl in if Nat.eq_dec c' c then l else l_top_elim.

(* The abstract call string of a concrete one, as seen from the unit wearing
   color `c`: its [k] most recent call sites, abstracted. *)
Definition acalls_of (c : color) (cs : calls) : acalls :=
  truncate (map (aclabel_of c) cs).

(* Abstracting commutes with pushing a call site. *)
Lemma acalls_of_cons c cl cs :
  acalls_of c (cl :: cs) = push (aclabel_of c cl) (acalls_of c cs).
Proof.
  unfold acalls_of, push, truncate; cbn [map].
  destruct k as [| n]; [reflexivity |].
  cbn [firstn]; f_equal.
  (* [cbn] unfolds the inner [firstn (S n) _] into a [match]; it is still
     convertible to [firstn (S n) _], so close the goal up to conversion *)
  assert (H : firstn n (firstn (S n) (map (aclabel_of c) cs)) = firstn n (map (aclabel_of c) cs))
    by (rewrite firstn_firstn, Nat.min_l by lia; reflexivity).
  exact (eq_sym H).
Qed.

(* Internal call: made at one of our own call sites. *)
Lemma acalls_of_internal c l cs :
  acalls_of c ((c, l) :: cs) = push l (acalls_of c cs).
Proof.
  rewrite acalls_of_cons.
  change (aclabel_of c (c, l)) with (if Nat.eq_dec c c then l else l_top_elim).
  destruct (Nat.eq_dec c c) as [_ | Hneq]; [reflexivity | exfalso; apply Hneq; reflexivity].
Qed.

(* Foreign call: made at a call site of another unit. *)
Lemma acalls_of_external c c' l cs :
  c' <> c ->
  acalls_of c ((c', l) :: cs) = push l_top_elim (acalls_of c cs).
Proof.
  intros Hneq.
  rewrite acalls_of_cons.
  change (aclabel_of c (c', l)) with (if Nat.eq_dec c' c then l else l_top_elim).
  destruct (Nat.eq_dec c' c); [contradiction | reflexivity].
Qed.

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
    approx_env (fun_fv f xs e) (ai_env A) β ρ ->
    approx_val' A (AVfun l f β xs e) (CVfun f ρ β xs e)

(* A constructor is approximated by its own allocation site.  Its fields are
   approximated by the field set of that site, which the logical relation
   records for every constructor it relates. *)
| Approx_CVconstr :
  forall A l t vs,
    approx_val' A (AVconstr l t) (CVconstr t vs)

(* Every value bound in `ρ` at a variable of `Γ` is approximated by some
   abstract value in the value set of its variable, looked up under `β` as
   `aeval` does. *)
with approx_env : vars -> aenv -> abenv -> cenv -> Prop :=
| Approx_env :
  forall AE Γ β ρ,
    (forall x v,
        (x \in Γ) ->
        ρ ! x = Some v ->
        exists av, (av \in AE (x, abenv_get β x)) /\ approx_val av v) ->
    approx_env Γ AE β ρ.

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

Lemma approx_env_subset {AE β Γ Γ' ρ} :
  approx_env Γ AE β ρ ->
  Γ' \subset Γ ->
  approx_env Γ' AE β ρ.
Proof. intros Henv Hsub; inv Henv; constructor; eauto. Qed.

Lemma approx_env_get {AE β Γ ρ x v} :
  approx_env Γ AE β ρ ->
  (x \in Γ) ->
  ρ ! x = Some v ->
  approx_vals (AE (x, (abenv_get β x))) v.
Proof. intros Henv Hx Hget; inv Henv; unfold approx_vals; eauto. Qed.

Lemma approx_env_get_list {AE Γ β ρ} :
  approx_env Γ AE β ρ ->
  forall xs vs,
    FromList xs \subset Γ ->
    get_list xs ρ = Some vs ->
    Forall2 (fun x v => approx_vals (AE (x, abenv_get β x)) v) xs vs.
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

Lemma approx_env_set {AE β Γ ρ} x δ v :
  approx_env Γ AE β ρ ->
  approx_vals (AE (x, δ)) v ->
  approx_env (x |: Γ) AE (abenv_set x δ β) (M.set x v ρ).
Proof.
  intros Henv Hv.
  inv Henv.
  constructor; intros y w Hy Hget.
  destruct (M.elt_eq x y); subst.
  - rewrite M.gss in Hget; inv Hget.
    rewrite abenv_get_set_eq.
    exact Hv.
  - rewrite M.gso in Hget by auto.
    rewrite abenv_get_set_neq by auto.
    inv Hy; [inv H0; contradiction | eauto].
Qed.

(* The parameters [xs] are all bound in the same context [δ]. *)
Lemma approx_env_set_lists {AE Γ β ρ} δ :
  approx_env Γ AE β ρ ->
  forall xs vs ρ',
    Forall2 (fun x v => approx_vals (AE (x, δ)) v) xs vs ->
    set_lists xs vs ρ = Some ρ' ->
    approx_env (FromList xs :|: Γ) AE (abenv_set_list xs δ β) ρ'.
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
    change (abenv_set_list (x :: xs) δ β) with (abenv_set x δ (abenv_set_list xs δ β)).
    apply (approx_env_subset (Γ := x |: (FromList xs :|: Γ))).
    + apply approx_env_set; [eapply IHxs; eauto | eassumption].
    + intros y Hy.
      inv Hy.
      * destruct H as [-> | Hin].
        -- apply Union_introl; apply In_singleton.
        -- apply Union_intror; apply Union_introl; exact Hin.
      * apply Union_intror; apply Union_intror; exact H.
Qed.

(* The fields of a constructor, read from the variables `xs`, flow into a
   value set `avs` that includes the value sets of all the variables. *)
Lemma approx_vals_fields {AE : afld} {xs vs avs} :
  Forall2 (fun x v => approx_vals (AE x) v) xs vs ->
  Forall (fun x => AE x \subset avs) xs ->
  Forall (approx_vals avs) vs.
Proof.
  intros H; induction H as [| x v xs vs Hv Hvs IH]; intros Hsub; constructor.
  - destruct Hv as [av [Hin Hav]].
    exists av; split; [exact (Forall_inv Hsub av Hin) | exact Hav].
  - exact (IH (Forall_inv_tail Hsub)).
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

(* `approx_int c AI I`: the static interactions `AI` of the unit wearing color
   `c` over-approximate the collected interactions `I`, as seen from that unit.
   `l_top_intro` and `l_top_elim` approximate all foreign interactions:
   - an internal interaction is predicted as it is;
   - one of our values eliminated by the context is predicted as eliminated
     at `l_top_elim`;
   - a foreign value eliminated by us is predicted as introduced at
     `l_top_intro`;
   - interactions between other units are not constrained. *)
Definition approx_int (c : color) (AI : ainteractions) (I : interactions) : Prop :=
  forall c1 l1 c2 l2,
    (((c1, l1), (c2, l2)) \in I) ->
    (c1 = c -> c2 = c -> (l1, l2) \in AI) /\
    (c1 = c -> c2 <> c -> (l1, l_top_elim) \in AI) /\
    (c1 <> c -> c2 = c -> (l_top_intro, l2) \in AI).

Lemma approx_int_empty c AI :
  approx_int c AI (Empty_set _).
Proof. unfold approx_int, Ensembles.In. fcrush. Qed.

(* Adding an internal interaction of the unit `c` that its analysis predicts. *)
Lemma approx_int_add_internal {c AI l1 l2 I} :
  (l1, l2) \in AI ->
  approx_int c AI I ->
  approx_int c AI (((c, l1), (c, l2)) |: I).
Proof.
  unfold approx_int.
  intros Hl HI c1 l1' c2 l2' Hin.
  inv Hin.
  - match goal with [Hs : _ \in [set _] |- _] => inv Hs end.
    repeat split.
    + intros _ _; exact Hl.
    + intros _ Hneq; exfalso; apply Hneq; reflexivity.
    + intros Hneq _; exfalso; apply Hneq; reflexivity.
  - match goal with [HI' : _ \in I |- _] => exact (HI _ _ _ _ HI') end.
Qed.

Lemma approx_int_add {c AI cl I} :
  approx_int c AI [set cl] ->
  approx_int c AI I ->
  approx_int c AI (cl |: I).
Proof.
  unfold approx_int.
  intros H1 H2 c1 l1 c2 l2 Hin.
  inv Hin; eauto.
Qed.

Lemma approx_int_singleton {c AI c1 l1 c2 l2} :
  (c1 = c -> c2 = c -> (l1, l2) \in AI) ->
  (c1 = c -> c2 <> c -> (l1, l_top_elim) \in AI) ->
  (c1 <> c -> c2 = c -> (l_top_intro, l2) \in AI) ->
  approx_int c AI [set ((c1, l1), (c2, l2))].
Proof.
  unfold approx_int.
  intros H1 H2 H3 c1' l1' c2' l2' Hin.
  inv Hin.
  auto.
Qed.

Lemma approx_int_union {c AI I1 I2} :
  approx_int c AI I1 ->
  approx_int c AI I2 ->
  approx_int c AI (I1 :|: I2).
Proof.
  unfold approx_int.
  intros H1 H2 c1 l1 c2 l2 Hin.
  inv Hin; eauto.
Qed.

(* `approx_clabel c l cl`: the abstract call site `l` approximates the
   colored call site `cl`, as seen from the unit wearing color `c`:
   - one of our call sites is approximated by itself;
   - a foreign call site is approximated by `l_top_elim`, as for interactions. *)
Definition approx_clabel (c : color) (l : label) (cl : clabel) : Prop :=
  match cl with
  | (c', l') => (c' = c -> l = l') /\ (c' <> c -> l = l_top_elim)
  end.

(* `approx_calls c δ cs`: the abstract call string `δ` approximates the
   concrete call string `cs`, as seen from the unit wearing color `c`: `δ`
   approximates, site by site, the [k] most recent call sites of `cs`. *)
Definition approx_calls (c : color) (δ : acalls) (cs : calls) : Prop :=
  Forall2 (approx_clabel c) δ (truncate cs).

Lemma Forall2_firstn {A B} (R : A -> B -> Prop) n xs ys :
  Forall2 R xs ys ->
  Forall2 R (firstn n xs) (firstn n ys).
Proof.
  intros H; revert n.
  induction H; intros [| n]; simpl; constructor; auto.
Qed.

Lemma approx_calls_nil c :
  approx_calls c [] [].
Proof. unfold approx_calls, truncate. destruct k; auto. Qed.

(* A call made at a site approximated by `l` extends the call string. *)
Lemma approx_calls_push {c δ cs} l cl :
  approx_clabel c l cl ->
  approx_calls c δ cs ->
  approx_calls c (push l δ) (cl :: cs).
Proof.
  unfold approx_calls, push, truncate.
  intros Hl H.
  (* [simpl] only the goal: in [H], [firstn (S n) cs] has to stay folded for
     [firstn_firstn] to apply *)
  revert H; destruct k as [| n]; intros H; simpl.
  - constructor.
  - constructor; [exact Hl |].
    pose proof (Forall2_firstn _ n _ _ H) as H'.
    rewrite firstn_firstn in H'.
    rewrite Nat.min_l in H' by lia.
    exact H'.
Qed.

(* Internal call: made at one of our own call sites. *)
Lemma approx_calls_push_internal {c δ cs} l :
  approx_calls c δ cs ->
  approx_calls c (push l δ) ((c, l) :: cs).
Proof.
  apply approx_calls_push.
  split; intros Hc; [reflexivity | exfalso; apply Hc; reflexivity].
Qed.

(* Foreign call: made at a call site of another unit. *)
Lemma approx_calls_push_external {c δ cs} c' l :
  c' <> c ->
  approx_calls c δ cs ->
  approx_calls c (push l_top_elim δ) ((c', l) :: cs).
Proof.
  intros Hneq.
  apply approx_calls_push.
  split; intros Hc; [contradiction | reflexivity].
Qed.

Lemma aclabel_of_approx c cl :
  approx_clabel c (aclabel_of c cl) cl.
Proof.
  destruct cl as [c' l]; unfold aclabel_of, approx_clabel; cbn.
  destruct (Nat.eq_dec c' c); split; intros; congruence.
Qed.

(* `acalls_of` computes the abstract call string that `approx_calls` relates. *)
Lemma approx_calls_acalls_of c cs :
  approx_calls c (acalls_of c cs) cs.
Proof.
  unfold approx_calls, acalls_of, truncate.
  apply Forall2_firstn.
  induction cs as [| cl cs IH]; simpl; constructor; auto.
  apply aclabel_of_approx.
Qed.

(* Invariants for Escaped Values *)
(* A value held by the unit wearing `c` that belongs to another unit must have
   escaped from that unit with its own allocation site: an `AVtop` in
   `ai_esc` would not constrain anything. *)
Definition cescaped (c : color) (v : clval) : Prop :=
  match v with
  | CTAG _ A' (c', l) w => c' <> c -> aval_of l w \in ai_esc A'
  end.

Lemma cescaped_defining A c l v :
  cescaped c (CTag A c l v).
Proof.
  unfold cescaped; destruct v; simpl;
    intros Hneq; exfalso; apply Hneq; reflexivity.
Qed.

Definition cescaped_env (c : color) (Γ : vars) (ρ : cenv) : Prop :=
  forall x v, (x \in Γ) -> ρ ! x = Some v -> cescaped c v.

Lemma cescaped_env_subset {c Γ Γ' ρ} :
  cescaped_env c Γ ρ ->
  Γ' \subset Γ ->
  cescaped_env c Γ' ρ.
Proof. unfold cescaped_env; eauto. Qed.

Lemma cescaped_env_set {c Γ ρ} x v :
  cescaped_env c Γ ρ ->
  cescaped c v ->
  cescaped_env c (x |: Γ) (M.set x v ρ).
Proof.
  unfold cescaped_env.
  intros Hesc Hv y w Hy Hget.
  destruct (M.elt_eq x y); subst.
  - rewrite M.gss in Hget; inv Hget; exact Hv.
  - rewrite M.gso in Hget by auto.
    inv Hy; [inv H; contradiction | eauto].
Qed.

Lemma cescaped_env_get {c Γ ρ} x v :
  cescaped_env c Γ ρ ->
  (x \in Γ) ->
  ρ ! x = Some v ->
  cescaped c v.
Proof. unfold cescaped_env; eauto. Qed.

Lemma cescaped_env_get_list {c Γ ρ} :
  cescaped_env c Γ ρ ->
  forall xs vs,
    FromList xs \subset Γ ->
    get_list xs ρ = Some vs ->
    Forall (cescaped c) vs.
Proof.
  intros Hesc xs.
  induction xs as [| x xs IHxs]; simpl; intros vs Hxs Hget.
  - inv Hget; constructor.
  - destruct (M.get x ρ) as [v |] eqn:Hx; [| discriminate Hget].
    destruct (get_list xs ρ) as [vs' |] eqn:Hxs'; [| discriminate Hget].
    inv Hget.
    constructor.
    + eapply cescaped_env_get; eauto.
      apply Hxs; left; reflexivity.
    + eapply IHxs; eauto.
      intros y Hy; apply Hxs; right; exact Hy.
Qed.

Lemma cescaped_env_set_lists {c Γ ρ} :
  cescaped_env c Γ ρ ->
  forall xs vs ρ',
    Forall (cescaped c) vs ->
    set_lists xs vs ρ = Some ρ' ->
    cescaped_env c (FromList xs :|: Γ) ρ'.
Proof.
  intros Hesc xs.
  induction xs as [| x xs IHxs]; intros vs ρ' Hall Hset; simpl in Hset.
  - destruct vs as [| v vs]; [| discriminate Hset].
    inv Hset.
    eapply cescaped_env_subset; [exact Hesc |].
    intros y Hy; inv Hy; [inv H | exact H].
  - destruct vs as [| v vs]; [discriminate Hset |].
    destruct (set_lists xs vs ρ) as [ρ'' |] eqn:Heq; [| discriminate Hset].
    inv Hset.
    inv Hall.
    apply (cescaped_env_subset (Γ := x |: (FromList xs :|: Γ))).
    + apply cescaped_env_set; [eapply IHxs; eauto | eassumption].
    + intros y Hy.
      inv Hy.
      * destruct H as [-> | Hin].
        -- apply Union_introl; apply In_singleton.
        -- apply Union_intror; apply Union_introl; exact Hin.
      * apply Union_intror; apply Union_intror; exact H.
Qed.

(* Invariants for Value Flow *)
(* How a value held by the unit wearing `c` (with analysis result `A`) is
   approximated in the value set `avs`:
   - a value of the unit itself is approximated by its own allocation site,
     not merely by `AVtop` -- unless it has already *escaped*, in which case
     `AVtop` stands for it.  This is what lets its exact site reach `ai_esc A`
     when it escapes, and what makes eliminating it a (statically) known
     elimination;
   - a foreign value is approximated by `AVtop`, so that eliminating it is
     treated as an unknown elimination. *)
Definition cflows (c : color) (A : analysis_result) (avs : avals) (v : clval) : Prop :=
  match v with
  | CTAG _ _ (c', l) w =>
      (c' = c -> (* c is the defining unit *)
       (aval_of l w \in avs) \/ (* internal value *)
         ((aval_of l w \in ai_esc A) /\ (AVtop \in avs))) /\ (* unknown value *)
        (c' <> c -> AVtop \in avs) (* c is not the defining unit *)
  end.

Lemma cflows_subset {c A avs avs' v} :
  cflows c A avs v ->
  avs \subset avs' ->
  cflows c A avs' v.
Proof.
  intros Hb Hsub.
  destruct v as [A' [c' l'] w]; unfold cflows in *.
  destruct Hb as [Hown Hforeign].
  split.
  - intros Heq.
    destruct (Hown Heq) as [Hin | [Hesc Htop]].
    + left; apply Hsub; exact Hin.
    + right; split; [exact Hesc | apply Hsub; exact Htop].
  - intros Hneq; apply Hsub; exact (Hforeign Hneq).
Qed.

(* Invariants for Variable Binding *)
(* `cflows` specialised to the value set of variable `x`. *)
Definition cbinding (c : color) (A : analysis_result) (x : var) (δ : acalls) (v : clval) : Prop :=
  cflows c A (ai_env A (x, δ)) v.

Definition cbinding_env (c : color) (A : analysis_result) (Γ : vars) (β : abenv) (ρ : cenv) : Prop :=
  forall x v, (x \in Γ) -> ρ ! x = Some v -> cbinding c A x (abenv_get β x) v.

Lemma cbinding_env_subset {c A Γ Γ' β ρ} :
  cbinding_env c A Γ β ρ ->
  Γ' \subset Γ ->
  cbinding_env c A Γ' β ρ.
Proof. unfold cbinding_env; eauto. Qed.

Lemma cbinding_env_set {c A Γ β ρ} x δ v :
  cbinding_env c A Γ β ρ ->
  cbinding c A x δ v ->
  cbinding_env c A (x |: Γ) (abenv_set x δ β) (M.set x v ρ).
Proof.
  unfold cbinding_env.
  intros Hex Hv y w Hy Hget.
  destruct (M.elt_eq x y); subst.
  - rewrite M.gss in Hget; inv Hget.
    rewrite abenv_get_set_eq; auto.
  - rewrite M.gso in Hget by auto.
    inv Hy; [inv H; contradiction | eauto].
    rewrite abenv_get_set_neq; auto.
Qed.

Lemma cbinding_env_get {c A Γ β ρ} x v :
  cbinding_env c A Γ β ρ ->
  (x \in Γ) ->
  ρ ! x = Some v ->
  cbinding c A x (abenv_get β x) v.
Proof. unfold cbinding_env; eauto. Qed.

Lemma cbinding_env_get_list {c A Γ β ρ} :
  cbinding_env c A Γ β ρ ->
  forall xs vs,
    FromList xs \subset Γ ->
    get_list xs ρ = Some vs ->
    Forall2 (fun x v => cbinding c A x (abenv_get β x) v) xs vs.
Proof.
  intros Hloc xs.
  induction xs as [| x xs IHxs]; simpl; intros vs Hxs Hget.
  - inv Hget; constructor.
  - destruct (M.get x ρ) as [v |] eqn:Hx; [| discriminate Hget].
    destruct (get_list xs ρ) as [vs' |] eqn:Hxs'; [| discriminate Hget].
    inv Hget.
    constructor.
    + eapply cbinding_env_get; eauto.
      apply Hxs; left; reflexivity.
    + eapply IHxs; eauto.
      intros y Hy; apply Hxs; right; exact Hy.
Qed.

Lemma cbinding_env_set_lists {c A Γ β ρ} :
  cbinding_env c A Γ β ρ ->
  forall xs vs δ ρ',
    Forall2 (fun x v => cbinding c A x δ v) xs vs ->
    set_lists xs vs ρ = Some ρ' ->
    cbinding_env c A (FromList xs :|: Γ) (abenv_set_list xs δ β) ρ'.
Proof.
  intros Hloc xs.
  induction xs as [| x xs IHxs]; intros vs δ ρ' Hall Hset; simpl in Hset.
  - destruct vs as [| v vs]; [| discriminate Hset].
    inv Hset.
    eapply cbinding_env_subset; [exact Hloc |].
    intros y Hy; inv Hy; [inv H | exact H].
  - destruct vs as [| v vs]; [discriminate Hset |].
    destruct (set_lists xs vs ρ) as [ρ'' |] eqn:Heq; [| discriminate Hset].
    inv Hset.
    inv Hall.
    apply (cbinding_env_subset (Γ := x |: (FromList xs :|: Γ))).
    + apply cbinding_env_set; [eapply IHxs; eauto | eassumption].
    + intros y Hy.
      inv Hy.
      * destruct H as [-> | Hin].
        -- apply Union_introl; apply In_singleton.
        -- apply Union_intror; apply Union_introl; exact Hin.
      * apply Union_intror; apply Union_intror; exact H.
Qed.

(* `cbinding` is preserved when the value flows into a variable whose value
   set includes that of the original one. *)
Lemma cbinding_subset {c A x δ x' v} :
  cbinding c A x δ v ->
  ai_env A (x, δ) \subset ai_env A (x', δ) ->
  cbinding c A x' δ v.
Proof. apply cflows_subset. Qed.

Lemma cbinding_subset_list {c A δ xs xs' vs} :
  Forall2 (fun x v => cbinding c A x δ v) xs vs ->
  Forall2 (fun x x' => ai_env A (x, δ) \subset ai_env A (x', δ)) xs xs' ->
  Forall2 (fun x' v => cbinding c A x' δ v) xs' vs.
Proof.
  intros Hb.
  revert xs'.
  induction Hb as [| x v xs vs Hx Hb IH]; intros xs' Hsub; inv Hsub.
  - constructor.
  - constructor; [eapply cbinding_subset; eauto | eapply IH; eauto].
Qed.

Lemma cbinding_cflows {c A x δ v} :
  cbinding c A x δ v ->
  cflows c A (ai_env A (x, δ)) v.
Proof. intros H; exact H. Qed.

Lemma cflows_cbinding {c A x δ v} :
  cflows c A (ai_env A (x, δ)) v ->
  cbinding c A x δ v.
Proof. intros H; exact H. Qed.

Lemma cflows_fields {c A δ xs vs avs} :
  Forall2 (fun x v => cbinding c A x δ v) xs vs ->
  Forall (fun x => ai_env A (x, δ) \subset avs) xs ->
  Forall (cflows c A avs) vs.
Proof.
  intros H; induction H as [| x v xs vs Hv Hvs IH]; intros Hsub; constructor.
  - eapply cflows_subset; [eapply cbinding_cflows; exact Hv | exact (Forall_inv Hsub)].
  - exact (IH (Forall_inv_tail Hsub)).
Qed.

(* Invariants for Results *)
(* A result returned by the unit wearing `c` into the return set `Rs` keeps
   the invariants of a binding: a foreign value has escaped, and a closure of
   the unit itself is approximated in `Rs` by its own allocation site, unless
   it has escaped already.  Unlike `approx_res`, this survives `AVtop ∈ Rs`. *)
Definition cresult (c : color) (A : analysis_result) (Rs : avals) (r : cres) : Prop :=
  match r with
  | COOT => True
  | CRes v => cescaped c v /\ cflows c A Rs v
  end.

Lemma cresult_subset {c A Rs Rs' r} :
  cresult c A Rs r ->
  Rs \subset Rs' ->
  cresult c A Rs' r.
Proof.
  intros Hok Hsub.
  destruct r as [| v]; [exact I |].
  destruct Hok as [Hesc Hfl].
  split; [exact Hesc | eapply cflows_subset; eauto].
Qed.

(* A value that crosses the program boundary: a value that has escaped
   from its unit with its own allocation site. *)
Definition cboundary (cv : clval) : Prop :=
  match cv with
  | CTAG _ A (c, l) w => aval_of l w \in ai_esc A
  end.

(* A result that crosses the program boundary. *)
Definition cboundary_res (r : cres) : Prop :=
  match r with
  | COOT => True
  | CRes v => cboundary v
  end.

(* Checking Semantics based on the Collecting Semantics *)
(* This semantics dynamically validates the analysis result, `A`.
   The collected interactions are validated against `ai_int A` once, in
   `CbstepF_Step`, which covers every interaction produced underneath it,
   including the call edge added by `Cbstep_app_*` and `Cbstep_letapp_*`. *)
Inductive cbstep (A : analysis_result) (c : color) (bdr : bool) (δ : calls) (β : abenv) (ρ : cenv)
  : exp -> fuel -> avals -> cres -> interactions -> Prop :=
| Cbstep_ret :
  forall {x v Rs},
    M.get x ρ = Some v ->
    cbstep A c bdr δ β ρ (Eret x) 0 Rs (CRes v) (Empty_set _)

(* The closure closes over `β`, and `f` is bound in the current context. *)
| Cbstep_fun :
  forall {f l xs e k i Rs r I},
    cbstep_fuel A c bdr δ (abenv_set f (acalls_of c δ) β) (M.set f (CTag A c l (CVfun f ρ β xs e)) ρ) k i Rs r I ->
    (* The abstract value is in `A` based on the current abstract call string `(acalls_of c δ)` *)
    (* Same as: (AVfun l f β xs e \in aeval A (abenv_set f (acalls_of c δ) β) f) -> *)
    (AVfun l f β xs e \in ai_env A (f, acalls_of c δ)) ->
    cbstep A c bdr δ β ρ (Efun f l xs e k) i Rs r I

(* Foreign call: dynamic counterpart of the unknown-callee branch of `Acheck_app`,
   validated from both sides.  The caller (`A`) sees an unknown value being
   eliminated and its arguments escaping; the callee (`A'`) sees one of its
   escaped closures being eliminated by the context.  The call string is
   extended with the caller's site `(c, l)`, which the callee abstracts as
   `l_top_elim`: its entry context is
   `push l_top_elim (acalls_of c' δ) = acalls_of c' ((c, l) :: δ)`
   (`acalls_of_external`). *)
| Cbstep_app_External :
  forall Rs {A' f f' c' l l' xs ρ' β' xs' e vs ρ'' i r I},
    M.get f ρ = Some (CTag A' c' l' (CVfun f' ρ' β' xs' e)) ->
    c <> c' ->

    (* callee side: the closure has escaped and is eliminated by the context
       (the caller side, `(l_top_intro, l)`, is checked by `CbstepF_Step`) *)
    (AVfun l' f' β' xs' e \in ai_esc A') ->
    ((l', l_top_elim) \in ai_int A') ->

    (* caller side: the arguments escape to the callee's unit *)
    get_list xs ρ = Some vs ->
    Forall (cescaped c') vs ->

    (* callee side: the (unknown) arguments flow to the parameters, bound
       together with the closure itself in the entry context *)
    set_lists xs' vs (M.set f' (CTag A' c' l' (CVfun f' ρ' β' xs' e)) ρ') = Some ρ'' ->
    approx_env (occurs_free e) (ai_env A')
      (abenv_set_list xs' (push l_top_elim (acalls_of c' δ))
         (abenv_set f' (push l_top_elim (acalls_of c' δ)) β'))
      ρ'' ->

    (* the body is validated against the callee's own analysis result, in the
       entry context, and returns into `ai_ret A' (l', entry context)` *)
    cbstep_fuel A' c' true ((c, l) :: δ)
      (abenv_set_list xs' (push l_top_elim (acalls_of c' δ))
         (abenv_set f' (push l_top_elim (acalls_of c' δ)) β'))
      ρ'' e i (ai_ret A' (l', push l_top_elim (acalls_of c' δ))) r I ->

    cbstep A c bdr δ β ρ (Eapp f l xs) i Rs r (((c', l'), (c, l)) |: I)

(* Internal call: dynamic counterpart of the known-callee branch of
   `Acheck_app`.  The callee wears the caller's color, so it belongs to the
   same unit and is validated against the same analysis result `A`.  The body
   is entered in the context `push l (acalls_of c δ) = acalls_of c ((c, l) :: δ)`
   (`acalls_of_internal`), as in `Acheck_app`. *)
| Cbstep_app_Internal :
  forall Rs { f f' l l' xs ρ' β' xs' e vs ρ'' i r I},
    M.get f ρ = Some (CTag A c l' (CVfun f' ρ' β' xs' e)) ->

    (* the arguments flow to the parameters, bound in the entry context *)
    get_list xs ρ = Some vs ->
    Forall2 (fun x' v => cbinding c A x' (push l (acalls_of c δ)) v) xs' vs ->
    set_lists xs' vs (M.set f' (CTag A c l' (CVfun f' ρ' β' xs' e)) ρ') = Some ρ'' ->

    (* the body returns into `ai_ret A (l', push l (acalls_of c δ))`, keyed by
       the context the body is *entered* in, not the caller's context `δ`:
       - the body is checked statically once per entry context `δ'`, against
         `ai_ret A (l', δ')` (`Acheck_fun`), and the caller reads its result
         from `ai_ret A (l', push l δ)` (`Acheck_app`), so the dynamic check
         has to use the same key;
       - keying by the caller's context `δ` would merge the returns of every
         call to `l'` made from `δ`, whatever site it is made at, which is
         exactly the precision call strings are meant to keep apart;
       - the context at the point of return carries nothing new: in a
         big-step semantics, control is back in the caller at `δ`. *)
    cbstep_fuel A c false ((c, l) :: δ)
      (abenv_set_list xs' (push l (acalls_of c δ))
         (abenv_set f' (push l (acalls_of c δ)) β'))
      ρ'' e i (ai_ret A (l', push l (acalls_of c δ))) r I ->

    cbstep A c bdr δ β ρ (Eapp f l xs) i Rs r (((c, l'), (c, l)) |: I)

with cbstep_fuel (A : analysis_result) (c : color) (bdr : bool) (δ : calls) (β : abenv) (ρ : cenv)
  : exp -> fuel -> avals -> cres -> interactions -> Prop :=
| CbstepF_OOT :
  forall {e Rs},
    cbstep_fuel A c bdr δ β ρ e 0 Rs COOT (Empty_set _)

| CbstepF_Step :
  forall {e i Rs r I},
    cbstep A c bdr δ β ρ e i Rs r I ->

    (* Approximations of outputs are valid if the input environments are properly approximated. *)
    approx_res Rs r ->
    approx_int c (ai_int A) I ->

    (* Coloring invariants are valid if the input environments are valid. *)
    cresult c A Rs r ->
    (if bdr then cboundary_res r else True) ->

    cbstep_fuel A c bdr δ β ρ e (S i) Rs r I.

Hint Constructors cbstep : core.
Hint Constructors cbstep_fuel : core.

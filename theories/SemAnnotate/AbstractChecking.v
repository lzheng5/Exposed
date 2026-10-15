From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From SemAnnotate Require Import LabeledANF.

(* Checking Semantics Based On A Simple Value Set Analysis *)

Section ValueSetAnalysis.

  (* --------------------------------------------------------------- *)
  (* The unknown/foreign side                                          *)
  (* --------------------------------------------------------------- *)

  (* Everything the analysis does not see is summarised by two dedicated labels:
     - [l_top_intro]: *every* value that originates outside the analysed unit
     - [l_top_elim]: *every* elimination performed outside the analysed unit *)
  Variable l_top_intro l_top_elim : label.

  (* Interaction Set *)
  (* Each pair has the format (l_intro, l_elim). *)
  Definition ainteraction : Type := (label * label).
  Definition ainteractions := Ensemble ainteraction.

  (* --------------------------------------------------------------- *)
  (* Abstract values                                                   *)
  (* --------------------------------------------------------------- *)

  (* An abstract value is an allocation site, summarised:
     - a closure is its introduction label together with its (syntactic) code;
     - a constructor is its introduction label, its tag, and the *variables*
       holding its fields -- the fields themselves are read back through the
       abstract environment, which is what makes the domain finite;
     - [AVtop] is the single abstract value standing for everything unknown:
       any foreign value, and any of our values that has escaped to the
       context.  Its introduction clabel is [l_top_intro]. *)
  Inductive aval : Type :=
  | AVtop : aval
  | AVfun : label -> var -> list var -> exp -> aval.

  Definition avals := Ensemble aval.

  Definition label_of (av : aval) : label :=
    match av with
    | AVtop => l_top_intro
    | AVfun l _ _ _ => l
    end.

  (* Abstract environment: one value set per variable (monovariant). *)
  Definition aenv := var -> avals.

  (* Abstract return sets, keyed by the closure's introduction label: a
     function body is analysed once, at its definition site, and everything it
     may return is collected in [Ret] at that site. *)
  Definition aret := label -> avals.

  (* --------------------------------------------------------------- *)
  (* The analysis result                                               *)
  (* --------------------------------------------------------------- *)

  Variable A : aenv.          (* value sets                                 *)
  Variable Ret : aret.        (* return sets                                *)
  Variable Esc : avals.       (* values that may escape to the context      *)
  Variable I : ainteractions.  (* statically predicted interactions          *)

  (* What the context may do with a value we handed it.  [Esc] has to be closed
     under this: the context can eliminate an escaped value, call an escaped
     closure with arbitrary (hence unknown) arguments and keep whatever it
     returns, and project out of an escaped constructor. *)
  Definition escapes_ok : Prop :=
    (forall av,
        (av \in Esc) ->
        ((label_of av, l_top_elim) \in I)) /\
    (forall l f xs e,
        (AVfun l f xs e \in Esc) ->
        (forall x, List.In x xs -> (AVtop \in A x)) /\
        (Ret l \subset Esc)).
    (* /\
    (forall l t ys,
        (AVconstr l t ys \in Esc) ->
        forall y, List.In y ys -> (A y \subset Esc)).*)

  (* --------------------------------------------------------------- *)
  (* The abstract semantics                                            *)
  (* --------------------------------------------------------------- *)

  (* [acheck e R] reads: the analysis result [(A, Ret, Esc, I)] is acceptable
     for [e] and [R] over-approximates the values [e] may return.
     This is the "abstract semantics": a declarative
     constraint system rather than a fixpoint computation, so any solver that
     produces [(A, Ret, Esc, I)] may be plugged in and checked against it. *)
  Inductive acheck : exp -> avals -> Prop :=
  | Acheck_ret :
    forall {x R},
      (A x \subset R) ->
      acheck (Eret x) R

  | Acheck_fun :
    forall {f l xs e k R},
      (* the closure introduced here flows into [f] *)
      (AVfun l f xs e \in A f) ->
      (* its body is analysed once, here, and returns into [Ret l] *)
      acheck e (Ret l) ->
      acheck k R ->
      acheck (Efun f l xs e k) R

  | Acheck_app :
    forall {f l xs R},
      (* the call site (c, l) eliminates everything that reaches [f] *)
      (forall av, (av \in A f) -> ((label_of av, l) \in I)) ->
      (* known callee: arguments flow to parameters, results flow out *)
      (forall l' f' xs' e',
          (AVfun l' f' xs' e' \in A f) ->
          length xs = length xs' /\
          (AVfun l' f' xs' e' \in A f') /\
          Forall2 (fun x x' => A x \subset A x') xs xs' /\
          (Ret l' \subset R)) ->
      (* unknown callee: the arguments escape and the result is unknown *)
      ((AVtop \in A f) ->
        Forall (fun x => A x \subset Esc) xs /\
        (AVtop \in R)) ->
      acheck (Eapp f l xs) R

             (*
  | Acheck_letapp :
    forall {x f l xs k R},
      (forall av, (av \in A f) -> ((label_of av, (c, l)) \in I)) ->
      (forall l' f' xs' e',
          (AVfun l' f' xs' e' \in A f) ->
          length xs = length xs' /\
          (AVfun l' f' xs' e' \in A f') /\
          Forall2 (fun z z' => A z \subset A z') xs xs' /\
          (Ret l' \subset A x)) ->
      ((AVtop \in A f) ->
       Forall (fun z => A z \subset Esc) xs /\ (AVtop \in A x)) ->
      acheck c k R ->
      acheck c (Eletapp x f l xs k) R

  | Acheck_constr :
    forall {x l t xs k R},
      (* the constructor introduced here flows into [x]; its fields are the
         variables [xs], read back through [A] *)
      (AVconstr (c, l) t xs \in A x) ->
      acheck c k R ->
      acheck c (Econstr x l t xs k) R

  | Acheck_proj :
    forall {x l n y k R},
      (forall av, (av \in A y) -> ((label_of av, (c, l)) \in I)) ->
      (forall l' t ys,
          (AVconstr l' t ys \in A y) ->
          forall z, nth_error ys n = Some z -> (A z \subset A x)) ->
      ((AVtop \in A y) -> (AVtop \in A x)) ->
      acheck c k R ->
      acheck c (Eproj x l n y k) R

  | Acheck_case_nil :
    forall {x l R},
      (forall av, (av \in A x) -> ((label_of av, (c, l)) \in I)) ->
      acheck c (Ecase x l []) R

  | Acheck_case_cons :
    forall {x l t e ls R},
      (forall av, (av \in A x) -> ((label_of av, (c, l)) \in I)) ->
      acheck c e R ->
      acheck c (Ecase x l ls) R ->
      acheck c (Ecase x l ((t, e) :: ls)) R.
              *)
             .
  Hint Constructors acheck : core.

  (* --------------------------------------------------------------- *)
  (* Concretisation                                                    *)
  (* --------------------------------------------------------------- *)

  (* [approx_val c v av]: the runtime value [v] is described by the abstract
     value [av], as seen from the unit of color [c].

     Our own values (color [c]) are described precisely.  Two kinds of value
     are described by [AVtop]: values that came in from the context (they carry
     the dedicated color [cext]), and values of ours that escaped to the
     context -- the latter is [Approx_escaped], and it is what lets [Esc] be a
     flat set instead of a reachability closure. *)
  Inductive approx_val (c : color) : lval -> aval -> Prop :=
  | Approx_escaped :
    forall {v av},
      approx_val c v av ->
      (av \in Esc) ->
      approx_val c v AVtop

  | Approx_foreign_fun :
    forall {U l f ρ xs e},
      approx_val c (CTag U cext l (CVfun f ρ xs e)) AVtop

  | Approx_foreign_constr_nil :
    forall {U l t},
      approx_val c (CTag U cext l (CVconstr t [])) AVtop

  | Approx_foreign_constr_cons :
    forall {U l t v vs},
      approx_val c v AVtop ->
      approx_val c (CTag U cext l (CVconstr t vs)) AVtop ->
      approx_val c (CTag U cext l (CVconstr t (v :: vs))) AVtop

  | Approx_fun :
    forall {U l f ρ xs e},
      approx_env c ρ ->
      (* the body was analysed at this definition site *)
      acheck c e (Ret (c, l)) ->
      approx_val c (CTag U c l (CVfun f ρ xs e)) (AVfun (c, l) f xs e)

  | Approx_constr_nil :
    forall {U l t},
      approx_val c (CTag U c l (CVconstr t [])) (AVconstr (c, l) t [])

  | Approx_constr_cons :
    forall {U l t v vs y ys av},
      (av \in A y) ->
      approx_val c v av ->
      approx_val c (CTag U c l (CVconstr t vs)) (AVconstr (c, l) t ys) ->
      approx_val c (CTag U c l (CVconstr t (v :: vs))) (AVconstr (c, l) t (y :: ys))

  with approx_env (c : color) : cenv -> Prop :=
  | Approx_env :
    forall {ρ},
      (forall x v,
          ρ ! x = Some v ->
          exists av, (av \in A x) /\ approx_val c v av) ->
      approx_env c ρ.

  (* [Approx_escaped] is deliberately left out of the hint database: its
     recursive premise has the same subject, so [eauto] would loop on it. *)
  Hint Resolve Approx_foreign_fun Approx_foreign_constr_nil
       Approx_foreign_constr_cons Approx_fun Approx_constr_nil
       Approx_constr_cons : core.
  Hint Constructors approx_env : core.

  Scheme approx_val_mut := Induction for approx_val Sort Prop
  with approx_env_mut := Induction for approx_env Sort Prop.

  (* [v] is in the concretisation of the value set [R]. *)
  Definition approx_in (c : color) (v : lval) (R : avals) : Prop :=
    exists av, (av \in R) /\ approx_val c v av.

  Inductive approx_res (c : color) : cres -> avals -> Prop :=
  | Approx_COOT :
    forall {R}, approx_res c COOT R

  | Approx_CRes :
    forall {v R},
      approx_in c v R ->
      approx_res c (CRes v) R.

  Hint Constructors approx_res : core.

  (* --------------------------------------------------------------- *)
  (* The checking semantics induced by the analysis                    *)
  (* --------------------------------------------------------------- *)

  (* Same shape as [cbstep], with two differences.

     1. No interaction set is produced.  Every elimination site instead carries
        the side condition [((c', l'), (c, l)) \in I]: the interaction it would
        have collected must already be predicted by the analysis.  Allocation
        sites carry the dual side condition, that the value they allocate was
        predicted by [A].

     2. Calls into the context are opaque.  A foreign closure (color [cext]) is
        not stepped into; [Acbstep_app_unknown] lets the context return any
        value that [AVtop] describes, or diverge.  What the context may do with
        the arguments it was handed is covered by [escapes_ok], statically. *)
  Inductive acbstep (U : internals) (c : color) (ρ : cenv) : exp -> fuel -> cres -> Prop :=
  | Acbstep_ret :
    forall {x v},
      M.get x ρ = Some v ->
      acbstep U c ρ (Eret x) 0 (CRes v)

  | Acbstep_fun :
    forall {f l xs e k i r},
      (* the allocated closure was predicted *)
      (AVfun (c, l) f xs e \in A f) ->
      acbstep_fuel U c (M.set f (CTag U c l (CVfun f ρ xs e)) ρ) k i r ->
      acbstep U c ρ (Efun f l xs e k) i r

  | Acbstep_app :
    forall {U' f f' l l' xs ρ' xs' e vs ρ'' i r},
      M.get f ρ = Some (CTag U' c l' (CVfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (CTag U' c l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      (* CHECK, where [cbstep] would have collected *)
      (((c, l'), (c, l)) \in I) ->
      acbstep_fuel U' c ρ'' e i r ->
      acbstep U c ρ (Eapp f l xs) i r

  | Acbstep_app_unknown :
    forall {U' f l cv xs vs i r},
      (* the callee came from the context, so it is not stepped into *)
      M.get f ρ = Some (CTag U' cext lval cv) ->
      get_list xs ρ = Some vs ->
      ((l_top_intro, (c, l)) \in I) ->
      (* the context returns something unknown, or diverges *)
      approx_res c r [set AVtop] ->
      acbstep U c ρ (Eapp f l xs) i r

  | Acbstep_letapp_Res :
    forall {U' x f f' l l' xs k ρ' xs' e vs ρ'' i i' v r},
      M.get f ρ = Some (CTag U' c l' (CVfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (CTag U' c l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      (((c, l'), (c, l)) \in I) ->
      acbstep_fuel U' c ρ'' e i (CRes v) ->
      acbstep_fuel U c (M.set x v ρ) k i' r ->
      acbstep U c ρ (Eletapp x f l xs k) (i + i') r

  | Acbstep_letapp_OOT :
    forall {U' x f f' l l' xs k ρ' xs' e vs ρ'' i},
      M.get f ρ = Some (CTag U' c l' (CVfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (CTag U' c l' (CVfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      (((c, l'), (c, l)) \in I) ->
      acbstep_fuel U' c ρ'' e i COOT ->
      acbstep U c ρ (Eletapp x f l xs k) i COOT

  | Acbstep_letapp_unknown_Res :
    forall {U' x f l cv xs k vs i i' v r},
      M.get f ρ = Some (CTag U' cext lval cv) ->
      get_list xs ρ = Some vs ->
      ((l_top_intro, (c, l)) \in I) ->
      approx_val c v AVtop ->
      acbstep_fuel U c (M.set x v ρ) k i' r ->
      acbstep U c ρ (Eletapp x f l xs k) (i + i') r

  | Acbstep_letapp_unknown_OOT :
    forall {U' f l cv x xs k vs i},
      M.get f ρ = Some (CTag U' cext lval cv) ->
      get_list xs ρ = Some vs ->
      ((l_top_intro, (c, l)) \in I) ->
      acbstep U c ρ (Eletapp x f l xs k) i COOT

  | Acbstep_constr :
    forall {x l t xs e r vs i},
      get_list xs ρ = Some vs ->
      (* the allocated constructor was predicted *)
      (AVconstr (c, l) t xs \in A x) ->
      acbstep_fuel U c (M.set x (CTag U c l (CVconstr t vs)) ρ) e i r ->
      acbstep U c ρ (Econstr x l t xs e) i r

  | Acbstep_proj :
    forall {U' x l c' l' t n y e i r v vs},
      M.get y ρ = Some (CTag U' c' l' (CVconstr t vs)) ->
      nth_error vs n = Some v ->
      (((c', l'), (c, l)) \in I) ->
      acbstep_fuel U c (M.set x v ρ) e i r ->
      acbstep U c ρ (Eproj x l n y e) i r

  | Acbstep_case :
    forall {U' x l c' l' ls t e r i vs},
      M.get x ρ = Some (CTag U' c' l' (CVconstr t vs)) ->
      find_tag ls t e ->
      (((c', l'), (c, l)) \in I) ->
      acbstep_fuel U c ρ e i r ->
      acbstep U c ρ (Ecase x l ls) i r

  with acbstep_fuel (U : internals) (c : color) (ρ : cenv) : exp -> fuel -> cres -> Prop :=
  | AcbstepF_OOT :
    forall {e},
      internals_monochromatic U c ->
      acbstep_fuel U c ρ e 0 COOT

  | AcbstepF_Step :
    forall {e i r},
      internals_monochromatic U c ->
      acbstep U c ρ e i r ->
      acbstep_fuel U c ρ e (S i) r.

  Hint Constructors acbstep : core.
  Hint Constructors acbstep_fuel : core.

  Scheme acbstep_ind' := Minimality for acbstep Sort Prop
  with acbstep_fuel_ind' := Minimality for acbstep_fuel Sort Prop.

  (* --------------------------------------------------------------- *)
  (* Helper lemmas on [approx_env]                                     *)
  (* --------------------------------------------------------------- *)

  Lemma approx_env_get {c ρ} x v :
    approx_env c ρ ->
    ρ ! x = Some v ->
    approx_in c v (A x).
  Proof. intros Henv Hget. inv Henv. eauto. Qed.

  Lemma approx_env_set {c ρ} x v :
    approx_env c ρ ->
    approx_in c v (A x) ->
    approx_env c (M.set x v ρ).
  Proof.
    intros Henv Hv. constructor. intros y w Hy.
    destruct (M.elt_eq x y) as [<-|Hne].
    - rewrite M.gss in Hy; invc. exact Hv.
    - rewrite M.gso in Hy by auto. inv Henv; eauto.
  Qed.

  Lemma approx_env_get_list {c ρ} xs vs :
    approx_env c ρ ->
    get_list xs ρ = Some vs ->
    Forall2 (fun v x => approx_in c v (A x)) vs xs.
  Proof.
    intros Henv. revert vs.
    induction xs as [|x xs IH]; intros vs Hget; simpl in *.
    - inv Hget; auto.
    - destruct (ρ ! x) as [v|] eqn:Hx; [|discriminate].
      destruct (get_list xs ρ) as [vs0|] eqn:Hxs; [|discriminate].
      inv Hget. constructor; [ eapply approx_env_get; eauto | eapply IH; eauto ].
  Qed.

  (* The pointwise flow [A x \subset A x'] produced by [Acheck_app] carries the
     concrete arguments from the call site to the parameters. *)
  Lemma approx_in_flow {c} vs xs xs' :
    Forall2 (fun v x => approx_in c v (A x)) vs xs ->
    Forall2 (fun x x' => A x \subset A x') xs xs' ->
    Forall2 (fun v x' => approx_in c v (A x')) vs xs'.
  Proof.
    intros Hvs. revert xs'.
    induction Hvs as [| v x vs0 xs0 Hv _ IH]; intros xs' Hflow; inv Hflow; auto.
    constructor; [| eauto].
    destruct Hv as [av [Hav Hap]]. exists av; split; auto.
  Qed.

  Lemma approx_env_set_lists {c ρ ρ'} xs vs :
    approx_env c ρ ->
    Forall2 (fun v x => approx_in c v (A x)) vs xs ->
    set_lists xs vs ρ = Some ρ' ->
    approx_env c ρ'.
  Proof.
    intros Henv Hf2. revert ρ'.
    induction Hf2 as [| v x vs0 xs0 Hv _ IH]; intros ρ' Hset; simpl in *.
    - inv Hset; auto.
    - destruct (set_lists xs0 vs0 ρ) as [ρ0|] eqn:H0; [|discriminate].
      inv Hset. eapply approx_env_set; eauto.
  Qed.

  (* --------------------------------------------------------------- *)
  (* Inversion lemmas on [approx_val]                                  *)
  (* --------------------------------------------------------------- *)

  (* Reading a field out of a value described by [AVconstr l t ys]: the field
     sits in the value set of the corresponding field variable. *)
  Lemma approx_constr_nth {c U l t vs ys n v} :
    approx_val c (CTag U c l (CVconstr t vs)) (AVconstr (c, l) t ys) ->
    nth_error vs n = Some v ->
    exists y, nth_error ys n = Some y /\ approx_in c v (A y).
  Proof.
    revert ys n v.
    induction vs as [|v0 vs IH]; intros ys n v Hap Hnth.
    - destruct n; simpl in Hnth; discriminate.
    - inv Hap.
      destruct n as [|n]; simpl in Hnth.
      + invc. eexists; split; [reflexivity |]. eexists; eauto.
      + edestruct IH as [y0 [Hy0 Hv0]]; eauto.
  Qed.

  (* Reading a field out of a value described by [AVtop]: the field is unknown
     too -- either the value is foreign (fields are [AVtop] by construction), or
     it is one of ours that escaped, and then [escapes_ok] propagates [Esc]
     through the fields. *)
  Lemma approx_top_nth {c U l t vs n v} :
    escapes_ok ->
    approx_val c (CTAG cval U l (CVconstr t vs)) AVtop ->
    nth_error vs n = Some v ->
    approx_val c v AVtop.
  Proof.
  Admitted.

  (* --------------------------------------------------------------- *)
  (* Inversion lemmas on [acheck]                                      *)
  (* --------------------------------------------------------------- *)

  Lemma acheck_case_elim {c x l ls R} :
    acheck c (Ecase x l ls) R ->
    forall av, (av \in A x) -> ((label_of av, (c, l)) \in I).
  Proof. intros H. inv H; eauto. Qed.

  Lemma acheck_find_tag {c x l ls R t e} :
    acheck c (Ecase x l ls) R ->
    find_tag ls t e ->
    acheck c e R.
  Proof.
    revert t e.
    induction ls as [|[t0 e0] ls IH]; intros t e Hchk Hft.
    - inv Hft.
    - inv Hchk. inv Hft; eauto.
  Qed.

  Lemma approx_val_fun_inv {c U l f ρ xs e av} :
    c <> cext ->
    approx_val c (CTag U c l (CVfun f ρ xs e)) av ->
    approx_env c ρ /\
    acheck c e (Ret (c, l)) /\
    (av = AVfun (c, l) f xs e \/
     (av = AVtop /\ (AVfun (c, l) f xs e \in Esc))).
  Proof.
    intros Hne Hap.
    remember (CTag U c l (CVfun f ρ xs e)) as v0 eqn:Heq0.
    revert U l f ρ xs e Heq0.
    induction Hap; intros U0 l0 f0 ρ0 xs0 e0 Heq0;
      unfold CTag in *; try discriminate.
    - (* Approx_escaped *)
      edestruct IHHap as [Henv [Hchk Hd]]; eauto.
      split; [exact Henv |]. split; [exact Hchk |].
      right; split; [reflexivity |].
      destruct Hd as [Heqav | [_ HEsc]]; [subst av |]; assumption.
    - (* Approx_foreign_fun: impossible, the unit's color is not [cext] *)
      inv Heq0. congruence.
    - (* Approx_fun *)
      inv Heq0.
      split; [assumption |]. split; [assumption |]. left; reflexivity.
  Qed.

  (* --------------------------------------------------------------- *)
  (* Soundness of the analysis for the checking semantics              *)
  (* --------------------------------------------------------------- *)

  (* The analysis predicts the result of every run the checking semantics
     accepts.  Since [acbstep]'s elimination rules only ever *check* membership
     in [I], this is what says the checks are the right ones: an [acheck]-valid
     analysis result makes the checking semantics agree with the program. *)
  Theorem acbstep_sound {U c ρ e i r R} :
    c <> cext ->
    escapes_ok ->
    approx_env c ρ ->
    acheck c e R ->
    acbstep U c ρ e i r ->
    approx_res c r R.
  Proof.
  Admitted.

  Theorem acbstep_fuel_sound {U c ρ e i r R} :
    c <> cext ->
    escapes_ok ->
    approx_env c ρ ->
    acheck c e R ->
    acbstep_fuel U c ρ e i r ->
    approx_res c r R.
  Proof.
    intros Hne Hesc Henv Hchk Hstep.
    inv Hstep; [ constructor | eapply acbstep_sound; eauto ].
  Qed.

  (* --------------------------------------------------------------- *)
  (* Checking [U] once, against the static [I]                         *)
  (* --------------------------------------------------------------- *)

  (* The whole point of computing [I] statically: [internals_closed] is
     anti-monotone in the interaction set, so closure under the predicted [I]
     subsumes closure under the interaction set collected by any single trace. *)
  Lemma reachable_subset {J J'} l l' :
    J \subset J' ->
    (l' \in reachable J l) ->
    (l' \in reachable J' l).
  Proof.
    unfold Ensembles.Included, Ensembles.In.
    intros Hsub Hr.
    induction Hr as [x | x y Hin | x y Hin | x y z H1 IH1 H2 IH2];
      [ apply Reachable_refl
      | apply Reachable_interact_l; apply Hsub; exact Hin
      | apply Reachable_interact_r; apply Hsub; exact Hin
      | eapply Reachable_step; eauto ].
  Qed.

  Lemma internals_losed_subset U {J J'} :
    J \subset J' ->
    internals_closed U J' ->
    internals_closed U J.
  Proof.
    unfold internals_closed.
    intros Hsub Hclosed l l' HlU Hr.
    eapply Hclosed; [exact HlU |].
    eapply reachable_subset; eauto.
  Qed.

  (* The unit of color [c] with body [e], analysed modularly:
     - [e]'s free variables are supplied by the context, hence unknown;
     - whatever [e] returns is handed to the context, hence escapes;
     - [Esc] is closed under what the context may do with an escaped value. *)
  Definition vsa_valid (c : color) (e : exp) : Prop :=
    c <> cext /\
    escapes_ok /\
    (forall x, (x \in occurs_free e) -> (AVtop \in A x)) /\
    exists R, acheck c e R /\ (R \subset Esc).

  (* The static counterpart of [cbstep]'s per-trace [internals_closed U I]
     premise: one check, against the predicted interactions. *)
  Definition vsa_checks (U : internals) (c : color) (e : exp) : Prop :=
    internals_monochromatic U c /\
    internals_closed U I /\
    vsa_valid c e.

  (* ... and it implies the per-trace check, for every trace whose collected
     interactions the analysis over-approximates. *)
  Lemma vsa_checks_internals_closed {U c e J} :
    vsa_checks U c e ->
    J \subset I ->
    internals_closed U J.
  Proof.
    intros [_ [Hclosed _]] Hsub.
    eapply internals_closed_subset; eauto.
  Qed.

End ValueSetAnalysis.

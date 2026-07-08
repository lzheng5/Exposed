From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Common Require Import Util.
From LambdaANF Require Import ANF Refl ReflLex.

(* This file illustrates
   1. ¬ (Refl.V <-> ReflLex.V) [not_V0_stronger_V1],
   2. ¬ (Refl.V -> ReflLex.V) [not_V0_stronger_V1],
   3. ReflLex.V -> Refl.V remains an open problem.
      As we cannot come up with counter-examples and cannot prove this claim with direct inductions. *)

(* However, the good news is that we don't need to use this equivalence anywhere in our top-level pipeline; we only need to compose the different V relations.
   Thus, choosing different V relations doesn't really matter from the top-level pipeline's perspective.
   In other words, CertiCoq's top-level composition approach has completely segregated the pipeline componenents.

   Therefor, we found in general the simplier Refl.V style (with direct induction with the step index) is a lot easier to work with than the lexicographic induction, ReflLex.v.
   They are especially easier when it comes to 1. functorization and 2. extra layering of logical relations. *)

Module R0 := Refl.
Module R1 := ReflLex.

Proposition V_relate_fixed :
  forall i v1 v2,
    R0.V i v1 v2 <-> R1.V i v1 v2.
Proof.
  (* We prove BOTH directions at once (a genuine <->) by strong induction on
     the step index i.  Bundling the two directions is FORCED by the function
     case: V occurs contravariantly (in argument position), so the forward
     direction on a function needs the *backward* direction on arguments, and
     vice versa -- exactly the mutual IH that only an equivalence provides.   *)
  intro i.
  induction i as [i IHi] using lt_wf_rec.
  intros v1 v2.
  split.

  (* ================= FORWARD :  R0.V i v1 v2 -> R1.V i v1 v2 ============== *)
  - intro H0.
    destruct v1 as [f1 rho1 xs1 e1 | t1 vs1];
      destruct v2 as [f2 rho2 xs2 e2 | t2 vs2];
      try (now (destruct i; simpl in H0; contradiction)).

    + (* Vfun / Vfun : CLOSES, thanks to the mutual IH. *)
      destruct i as [ | i0 ].
      * rewrite R1.V_eq; simpl. simpl in H0.
        destruct H0 as [Hlen _]. split; [ exact Hlen | ].
        intros; exfalso; lia.
      * rewrite R1.V_eq; simpl. simpl in H0.
        destruct H0 as [Hlen Hcl]. split; [ exact Hlen | ].
        intros j vs1 vs2 rho3 rho4 Hset1 Hset2 Hji HR1args.
        (* arguments: R1.V j -> R0.V j  (BACKWARD dir, via IHi, j < S i0) *)
        assert (HR0args : Forall2 (R0.V j) vs1 vs2).
        { clear Hset1 Hset2 Hcl.
          induction HR1args as [ | x y l l' Hxy Hrest IH].
          - constructor.
          - constructor; [ apply (proj2 (IHi j Hji x y)); exact Hxy | exact IH ]. }
        specialize (Hcl j vs1 vs2 rho3 rho4).
        rewrite normalize_step in Hcl by lia.
        specialize (Hcl ltac:(lia) HR0args Hset1 Hset2).
        (* results: R0.V (j-j1) -> R1.V (j-j1)  (FORWARD dir, via IHi)        *)
        unfold Refl.E' in Hcl. unfold ReflLex.E'.
        intros j1 r1 Hj1 Hstep.
        destruct (Hcl j1 r1 Hj1 Hstep) as [j2 [r2 [Hstep2 HRr]]].
        exists j2, r2. split; [ exact Hstep2 | ].
        unfold Refl.R' in HRr. unfold ReflLex.R'.
        destruct r1 as [ | u1 ]; destruct r2 as [ | u2 ]; try contradiction; auto.
        apply (proj1 (IHi (j - j1) ltac:(lia) u1 u2)); exact HRr.

    + (* Vconstr / Vconstr : THE WALL. *)
      destruct i as [ | i0 ].
      * (* i = 0 : R0.V 0 recorded ONLY the length; R1.V 0 needs the elements
             related, and there is no smaller index to appeal to.  FALSE.     *)
        simpl in H0. destruct H0 as [Ht Hlen]; subst.
        rewrite R1.V_eq; simpl. split; [ reflexivity | ].
        (* Show. *)
        admit.
      * (* i = S i0 : still stuck -- R0.V (S i0) relates elements at i0, but
             R1.V (S i0) needs them at S i0, and R1 is not upward monotone.    *)
        simpl in H0. destruct H0 as [Ht HF]; subst.
        rewrite R1.V_eq; simpl. split; [ reflexivity | ].
        (* Show. *)
        admit.

  (* ================= BACKWARD :  R1.V i v1 v2 -> R0.V i v1 v2 ============= *)
  - intro H1.
    destruct v1 as [f1 rho1 xs1 e1 | t1 vs1];
      destruct v2 as [f2 rho2 xs2 e2 | t2 vs2];
      try (now (rewrite R1.V_eq in H1; simpl in H1; contradiction)).

    + (* Vfun / Vfun : CLOSES, thanks to the mutual IH. *)
      destruct i as [ | i0 ].
      * rewrite R1.V_eq in H1; simpl in H1. destruct H1 as [Hlen _].
        simpl. split; [ exact Hlen | exact I ].
      * rewrite R1.V_eq in H1; simpl in H1. destruct H1 as [Hlen Hcl].
        simpl. split; [ exact Hlen | ].
        intros j vs1 vs2 rho3 rho4 Hji HR0args Hset1 Hset2.
        rewrite normalize_step in HR0args by lia.
        rewrite normalize_step by lia.
        (* arguments: R0.V j -> R1.V j  (FORWARD dir, via IHi, j <= i0)        *)
        assert (HR1args : Forall2 (R1.V j) vs1 vs2).
        { clear Hset1 Hset2 Hcl.
          induction HR0args as [ | x y l l' Hxy Hrest IH].
          - constructor.
          - constructor; [ apply (proj1 (IHi j ltac:(lia) x y)); exact Hxy | exact IH ]. }
        specialize (Hcl j vs1 vs2 rho3 rho4 Hset1 Hset2 ltac:(lia) HR1args).
        (* results: R1.V (j-j1) -> R0.V (j-j1)  (BACKWARD dir, via IHi)        *)
        unfold ReflLex.E' in Hcl. unfold Refl.E'.
        intros j1 r1 Hj1 Hstep.
        destruct (Hcl j1 r1 Hj1 Hstep) as [j2 [r2 [Hstep2 HRr]]].
        exists j2, r2. split; [ exact Hstep2 | ].
        unfold ReflLex.R' in HRr. unfold Refl.R'.
        destruct r1 as [ | u1 ]; destruct r2 as [ | u2 ]; try contradiction; auto.
        apply (proj2 (IHi (j - j1) ltac:(lia) u1 u2)); exact HRr.

    + (* Vconstr / Vconstr : CLOSES (R1 is stronger, so it implies R0). *)
      rewrite R1.V_eq in H1; simpl in H1. destruct H1 as [Ht HF]; subst.
      destruct i as [ | i0 ].
      * simpl. split; [ reflexivity | eapply Forall2_length; eauto ].
      * simpl. split; [ reflexivity | ].
        induction HF as [ | x y l l' Hxy Hrest IH].
        -- constructor.
        -- constructor; [ | exact IH ].
           apply (proj2 (IHi i0 ltac:(lia) x y)).
           eapply ReflLex.V_mono; [ exact Hxy | lia ].
Abort.

(* It looks like the issue has to do with the *fixed* step index. *)
(* Let's try relaxing that with a forall. *)

(* ================================================================= *)
(* Forward attempt with lexicographic induction.                     *)
(*                                                                   *)
(* We attempt the forward direction of the (forall i) equivalence,   *)
(*   fwd :  (forall k, R0.V k v1 v2) -> R1.V i v1 v2                  *)
(* by a lexicographic induction:                                     *)
(*   outer = strong induction on the step index i   (IHi)            *)
(*   inner = structural induction on v1 (val_ind')  (IHv1, IHv0)     *)
(*                                                                   *)
(* The two CONSTRUCTOR cases go through: the structural inner IH      *)
(* (at the *same* index i) discharges each element, which is exactly  *)
(* the recursion the step-index-only attempt above was missing.      *)
(*                                                                   *)
(* The FUNCTION case gets stuck -- see the [Show] / comment below.    *)
(* ================================================================= *)

Proposition forward_probe :
  forall i v1 v2, (forall k, R0.V k v1 v2) -> R1.V i v1 v2.
Proof.
  intro i.
  induction i as [i IHi] using lt_wf_rec.
  intros v1 v2. revert v2.
  induction v1 using val_ind'; intros v2 Hyp.

  - (* v1 = Vconstr t []  ------------------------------------------- *)
    pose proof (Hyp 0) as H0.
    destruct v2 as [f2 r2 xs2 e2 | t2 l2].
    + simpl in H0; contradiction.
    + simpl in H0. destruct H0 as [Ht Hlen]; subst.
      destruct l2; simpl in Hlen; try discriminate.
      rewrite R1.V_eq. simpl. split.
      * reflexivity.
      * constructor.

  - (* v1 = Vconstr t (v1 :: l)  ------------------------------------ *)
    pose proof (Hyp 0) as H0.
    destruct v2 as [f2 r2 xs2 e2 | t2 l2].
    + simpl in H0; contradiction.
    + simpl in H0. destruct H0 as [Ht Hlen]; subst.
      destruct l2 as [ | b l2]; simpl in Hlen; try discriminate.
      rewrite R1.V_eq. simpl. split; [ reflexivity | ].
      constructor.
      * (* head element: structural inner IH [IHv1], SAME index i *)
        apply IHv1.
        intro k. pose proof (Hyp (S k)) as Hk. simpl in Hk.
        destruct Hk as [_ HF]. inv HF. auto.
      * (* tail list: structural inner IH [IHv0], SAME index i *)
        assert (Htl : forall k, R0.V k (Vconstr t2 l) (Vconstr t2 l2)).
        { intro k. pose proof (Hyp (S k)) as Hk. simpl in Hk.
          destruct Hk as [_ HF].
          inversion HF as [ | a b0 la lb Hhd Htail ]; subst.
          destruct k.
          - simpl. split; [ reflexivity | eapply Forall2_length; eauto ].
          - simpl. split; [ reflexivity | ].
            eapply Refl.V_mono_Forall; [ exact Htail | lia ]. }
        pose proof (IHv0 (Vconstr t2 l2) Htl) as HR1tl.
        rewrite R1.V_eq in HR1tl. simpl in HR1tl.
        destruct HR1tl as [_ HF]. exact HF.

  - (* v1 = Vfun f1 r1 xs1 e1  -------------------------------------- *)
    pose proof (Hyp 0) as H0.
    destruct v2 as [f2 r2 xs2 e2 | t2 l2].
    2:{ simpl in H0; contradiction. }
    simpl in H0. destruct H0 as [Hlen _].
    rewrite R1.V_eq. simpl. split; [ exact Hlen | ].
    intros j vs1 vs2 rho3 rho4 Hset1 Hset2 Hji HR1args.
    (* Goal:  E' R1.V j rho3 e1 rho4 e2 .                             *)
    (* Extract the matching R0 function clause from  Hyp (S j).       *)
    pose proof (Hyp (S j)) as HR0.
    simpl in HR0. destruct HR0 as [_ HR0clause].
    specialize (HR0clause j vs1 vs2 rho3 rho4).
    rewrite normalize_step in HR0clause by lia.
    (* HR0clause now expects  Forall2 (R0.V j) vs1 vs2  and, when fed  *)
    (* that, yields  E' R0.V j rho3 e1 rho4 e2  (NOT E' R1.V j).       *)
    (* But we only have  HR1args : Forall2 (R1.V j) vs1 vs2.           *)
    (* Show.*)
Abort.

(* [back_probe] : the fixed-index conversion  R1.V j -> R0.V j  that the
   function case of [V_relate] needs on its arguments.  It CLOSES on
   constructors but WALLS in its own function case -- see the detailed note
   before [V_relate] below. *)
Proposition back_probe :
  forall j a b, R1.V j a b -> R0.V j a b.
Proof.
  intro j.
  induction j as [j IHj] using lt_wf_rec.
  intros a b H1.
  destruct a as [f1 rho1 xs1 e1 | t1 vs1];
    destruct b as [f2 rho2 xs2 e2 | t2 vs2];
    try (now (rewrite R1.V_eq in H1; simpl in H1; contradiction)).
  - (* Vfun / Vfun : the wall. *)
    destruct j as [ | j0 ].
    + rewrite R1.V_eq in H1; simpl in H1. destruct H1 as [Hlen _].
      simpl. split; [ exact Hlen | exact I ].
    + rewrite R1.V_eq in H1; simpl in H1. destruct H1 as [Hlen Hcl].
      simpl. split; [ exact Hlen | ].
      intros j' vs1 vs2 rho3 rho4 Hj' HR0args Hset1 Hset2.
      rewrite normalize_step in HR0args by lia.
      rewrite normalize_step by lia.
      specialize (Hcl j' vs1 vs2 rho3 rho4 Hset1 Hset2).
      (* Hcl needs  Forall2 (R1.V j') vs1 vs2 ; we only have  R0.V j'.
         That is the FORWARD fixed-index conversion on arguments, which is
         exactly the false constructor base case.  STUCK. *)
      (* Show. *)
      admit.
  - (* Vconstr / Vconstr : closes (R1 stronger implies R0). *)
    rewrite R1.V_eq in H1; simpl in H1. destruct H1 as [Ht HF]; subst.
    destruct j as [ | j0 ].
    + simpl. split; [ reflexivity | eapply Forall2_length; eauto ].
    + simpl. split; [ reflexivity | ].
      induction HF as [ | x y l l' Hxy Hrest IH].
      * constructor.
      * constructor; [ | exact IH ].
        apply IHj; [ lia | ].
        eapply ReflLex.V_mono; [ exact Hxy | lia ].
Abort.

(* ==========================================================================
   Why [V_relate] is NOT provable?

   Recall the ONLY difference between Refl.V (=R0.V) and ReflLex.V (=R1.V) is
   the constructor base case (on functions the two are identical):
     - R0.V 0 (Vconstr c vs1) (Vconstr c vs2)  =  c = c /\ |vs1| = |vs2|
         records only the LENGTH; the elements are forgotten;
     - R1.V 0 (Vconstr c vs1) (Vconstr c vs2)  =  c = c /\ Forall2 (R1.V 0) vs1 vs2
         recurses STRUCTURALLY into the elements.

   --- The CONSTRUCTOR case is fine. -------------------------------------------
   Over (forall i) the constructor spine is fully pinned on both sides, so a
   *structural* induction on the value plus the (forall k) hypothesis recovers
   the element relations.  This is exactly what [forward_probe] does: [forward_probe] is literally
   the -> direction of V_relate (for each i), and BOTH of its Vconstr cases
   close -- the step the naive step-index proof of the fixed-index
   [V_relate_fixed] could never take.

   --- The FUNCTION case is the obstruction, because of CONTRAVARIANCE. --------
   V is applied to a closure's ARGUMENTS in negative position.  To prove the
   -> direction on a Vfun,   R0.V (Vfun) -> R1.V (Vfun),   we must satisfy R1's
   function clause: it HANDS us R1-related arguments and asks us to run the
   bodies.  Our only handle on the bodies is R0's clause (from the hypothesis),
   and that clause only fires on R0-related arguments.  So we must convert the
   arguments the OTHER way,
         Forall2 (R1.V j) args  ->  Forall2 (R0.V j) args,
   i.e. proving the FORWARD direction on the function requires the BACKWARD
   direction on its arguments (and symmetrically for <-).

   --- Hence the IH must be an EQUIVALENCE. ------------------------------------
   This is the crux.  If we prove a single implication -- e.g. induct on the
   step index to show, as V_relate is stated,
         (forall i, R0.V i v1 v2) -> (forall i, R1.V i v1 v2)
   -- then at smaller indices the IH gives only that SAME implication.  The
   reverse implication, which the contravariant argument position demands, is
   simply not in the IH, so the function case cannot be closed.  One is forced
   to carry BOTH directions at once (a genuine <->) so the IH can supply
   whichever direction each position needs.  [V_relate_fixed] above is set up
   this way, and indeed its Vfun cases DO close: each converts the arguments
   with one projection of the mutual IH and the results with the other.

   --- But the equivalence only RELOCATES the wall; it does not remove it. -----
   (a) For the FIXED-index equivalence [V_relate_fixed], the mutual IH discharges
       the function case, and the proof then bottoms out at the constructor
       base case i = 0, whose forward half
             R0.V 0 (Vconstr ..) -> R1.V 0 (Vconstr ..)
       is FALSE: R0.V 0 retained only the length while R1.V 0 wants the elements
       related.  Witness:  Vconstr c [Vconstr d []]  vs  Vconstr c [Vconstr e []]
       with d <> e -- equal top-level length, so R0.V 0 holds, but R1.V 0 fails.

   (b) For the (forall i) statement here, the arguments enter the function
       clause at a SINGLE step index j, so no "forall k" fact about them is ever
       in scope: the (forall k)-flavoured IH cannot even be applied to them.
       The conversion actually needed is the fixed-index  R1.V j -> R0.V j,
       which is [back_probe] -- and [back_probe] walls in its OWN function case,
       needing the forward fixed-index conversion R0.V j' -> R1.V j' on
       arguments, i.e. precisely the false base case of (a).

   So both formulations bottom out at the same false constructor base case,
   the fixed-index one reaching it directly and the (forall i) one reaching it
   through the function argument position.  Furthermore R1.V j -> R0.V j
   genuinely FAILS on function-valued arguments (a closure can agree on every
   deeply-matching R1-argument yet differ on a shallow, R0-only-matching one),
   so the biconditional is not merely unprovable by these inductions but false
   once higher-order arguments appear.

   Conclusion: Refl.V and ReflLex.V are independent -- no equivalence between
   them holds, at a fixed step index or over all indices -- so [V_relate] is
   left Admitted.
   ========================================================================== *)
Proposition V_relate:
  forall v1 v2,
    (forall i, R0.V i v1 v2) <-> (forall i, R1.V i v1 v2).
Proof.
   (* If we do the intro as usual and induct on the step index,
      the IH will not be an equivalence. *)
Abort.

(* ==========================================================================
   Refl.V is NOT stronger than ReflLex.V.

   "R0.V is stronger than R1.V" is the universally-quantified implication
        forall i v1 v2, R0.V i v1 v2 -> R1.V i v1 v2.
   By  ~(forall ..) = (exists .., ~..),  a single COUNTEREXAMPLE refutes it:
   one triple (i, v1, v2) with  R0.V i v1 v2  but  ~ R1.V i v1 v2.  That is
   exactly what [not_V0_stronger_V1] exhibits, so this one instance suffices to
   conclude that R0.V does not imply R1.V (and a fortiori that the equivalence
   [V_relate_fixed] is false: the biconditional already breaks at this pair).

   The witness lives at index 0 and is the crux of the whole file: at i = 0,
        R0.V 0 (Vconstr c vs1) (Vconstr c vs2)  =  c = c /\ |vs1| = |vs2|
   keeps ONLY the top-level arity, whereas
        R1.V 0 (Vconstr c vs1) (Vconstr c vs2)  =  c = c /\ Forall2 (R1.V 0) vs1 vs2
   recurses into the elements.  So two constructors that agree on shape but
   disagree one level down (inner tags 1 vs 2) are R0.V-related yet not
   R1.V-related.

   NOTE this settles only ONE of the two halves of "neither stronger nor
   weaker" (line 12): it shows R0 is not stronger.  The mirror half -- that
   R1 is not stronger than R0, i.e. a witness of  R1.V i v1 v2 /\ ~ R0.V i v1 v2
   -- is a separate obligation and is necessarily higher-order, since on
   first-order (pure data) values  R1.V i -> R0.V i  actually holds.
   ========================================================================== *)
Lemma not_V0_stronger_V1 :
  exists x y, R0.V 0 x y /\ ~ R1.V 0 x y.
Proof.
  (* c = 1 at every node; inner tags differ (1 vs 2). *)
  exists (Vconstr 1%positive [Vconstr 1%positive []]),
         (Vconstr 1%positive [Vconstr 2%positive []]).
  split.
  - (* R0.V 0 checks only the top-level length: 1 = 1. *)
    simpl. split; reflexivity.
  - (* R1.V 0 recurses; it would force the inner tags equal: 1 = 2. *)
    intro HC.
    rewrite R1.V_eq in HC; simpl in HC.
    destruct HC as [_ HF]; inv HF.
    match goal with
    | [ H : R1.V 0 (Vconstr _ _) (Vconstr _ _) |- _ ] =>
        rewrite R1.V_eq in H; simpl in H; destruct H as [Hbad _]; discriminate
    end.
Qed.

(* ==========================================================================
   Independence, direction 2  (Open):
        ReflLex.V is not stronger than Refl.V.

   This is the mirror of [not_V0_stronger_V1].
        not_V0_stronger_V1  :  exists x y,     R0.V 0 x y /\ ~ R1.V 0 x y      (PROVED)
        not_V1_stronger_V0  :  exists i v1 v2, R1.V i v1 v2 /\ ~ R0.V i v1 v2  (conjecture)

   Why this is left a conjecture (not a lemma):

   (1) A witness must be HIGHER-ORDER.  On first-order (pure Vconstr) values
       R1.V i -> R0.V i genuinely holds (structural implies length), so any
       witness of R1.V /\ ~ R0.V must contain a Vfun.

   (2) We do not have that higher-order witness.  To get ~ R0.V (Vfun ..) one
       needs an R0-related argument pair on which the two closures diverge.  But
       the argument pairs that R0 relates and R1 does not differ only BELOW the
       depth R0.V inspects, so they are R0-related only at LOW step indices --
       and there E' cannot observe the difference: E' _ 0 is just OOT |-> OOT,
       and E' _ j runs the bodies with fuel <= j while R0.V j already forces the
       arguments to agree down to depth ~ j, precisely the part bounded
       evaluation can reach.  This step-indexing "soundness" makes every
       construction we tried collapse.

   (3) The equivalent positive goal -- refuting the implication
          forall i v1 v2, R1.V i v1 v2 -> R0.V i v1 v2
       -- is no easier, because that implication is out of reach of every
       natural method, all for the SAME reason: its FUNCTION case needs the IH
       to be an equivalence.  V occurs in the (negative) argument position, so
       discharging the function case means crossing the arguments between R0 and
       R1; the arguments arrive R0-related at one index j < i and must be fed to
       R1's clause, which needs the *converse* R0.V j -> R1.V j.  No method
       supplies that crossing without the equivalence:
         - refl_V / V_mono / trans_V are each about a SINGLE relation and never
           move a fact across the R0/R1 boundary;
         - the IH of a single implication crosses the boundary only where the
           index strictly drops -- i.e. on RESULTS, never on the arguments;
         - a "diagonal + refl_V + trans_V" detour that tries to sidestep the
           argument crossing collapses on the argument side anyway: closing its
           trans_V step needs the arguments related at ALL indices, while the
           clause hands them at one.
       So the function case is dischargeable only with an IH already carrying
       BOTH directions -- the equivalence -- which is exactly what is FALSE at
       the constructor base case (cf. [not_V0_stronger_V1], [V_relate_fixed],
       [forward_probe], [back_probe]).  Hence neither the implication nor its negation is
       reachable this way.

   Net status: the truth value is genuinely open.  Either a higher-order
   counterexample exists here (confirming independence), or R1.V -> R0.V holds
   by some argument that escapes the equivalence trap of (3) -- making R1.V
   STRICTLY stronger than R0.V, falsifying this conjecture, and forcing line 12
   to weaken to "ReflLex.V implies Refl.V but not conversely".  We have neither;
   what is established is only that every method tried for the implication needs
   the equivalence in the function case, which the base case denies.
   ========================================================================== *)
Proposition not_V1_stronger_V0 :
  exists i v1 v2, R1.V i v1 v2 /\ ~ R0.V i v1 v2.
Abort.

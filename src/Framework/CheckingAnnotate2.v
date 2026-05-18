From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.
From Hammer Require Import Hammer Tactics Reflect.

From Framework Require Import Util W0 ANF1 ANF Annotate Erase.

Module AS := ANF1.
Module AT := ANF.

(* Annotate Based on The Checking Semantics *)

(* Maps labels to the actual webs. *)
Definition web_map : Type := M.t web.

(* Maps internal webs, `w`, to webs that interact with. `w` *)
Definition internal_web_map : Type := M.t webs.

Definition annotate_info : Type := web_map * internal_web_map.

(* Invariants for [annotate_info] *)
(* 1. Dom of internal_web_map only contains non-exposed web ids (encoded) *)
(* 2. Dom of internal_web_map is isomorphic to (Im of web_map \ Exposed) *)
(* 3. Each set in (Im of internal_web_map) is a subset of (Im of web_map U Exposed) *)

Definition annotate_info_inv (ainfo : annotate_info) : Prop :=
  match ainfo with
  | (wm, im) =>
      (forall w, (w \in Dom_map im) -> ~ (w \in Exposed))
  end.

Section Checking.

  Variable W : annotate_info.

  Definition to_exposed (tv : AS.wval) : Prop :=
    match tv with
    | AS.TAG _ l v => exists w, (fst W) ! l = Some w /\ (w \in Exposed)
    end.

  Definition to_exposed_res (r : AS.res) : Prop :=
    match r with
    | AS.OOT => True
    | AS.Res v => to_exposed v
    end.

  (* Records webs that interact with internal web, `w` *)
  Definition interact_with (w : web) (tv : AS.wval) : Prop :=
    match tv with
    | AS.TAG _ l v =>
        exists w' im,
          (fst W) ! l = Some w' /\
          (snd W) ! w = Some im /\
          (w' \in im)
    end.

  Definition interact_with_res (w : web) (r : AS.res) : Prop :=
    match r with
    | AS.OOT => True
    | AS.Res v => interact_with w v
    end.

  (* `W` is a valid analysis result with respect to the checking big-step semantics *)
  Inductive cbstep (ex : bool) (ρ : AS.env) : AS.exp -> fuel -> AS.res -> Prop :=
  | Cbstep_ret :
    forall {x l w v},
      M.get x ρ = Some (AS.Tag l v) ->
      (fst W) ! l = Some w ->
      cbstep ex ρ (AS.Eret x) 0 (AS.Res (AS.Tag l v))

  | Cbstep_fun :
    forall {f l w xs e k c r},
      (fst W) ! l = Some w ->
      cbstep_fuel ex (M.set f (AS.Tag l (AS.Vfun f ρ xs e)) ρ) k c r ->
      cbstep ex ρ (AS.Efun f l xs e k) c r

  | Cbstep_app :
    forall {f f' l l' w xs ρ' xs' e vs ρ'' c r},
      M.get f ρ = Some (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      (fst W) ! l = Some w ->
      (fst W) ! l' = Some w ->
      (if exposedb w
       then Forall to_exposed vs /\ to_exposed_res r
       else Forall (interact_with w) vs /\ interact_with_res w r) ->
      cbstep_fuel (exposedb w) ρ'' e c r ->
      cbstep ex ρ (AS.Eapp f l xs) c r

  | Cbstep_letapp_Res :
    forall {x f f' l l' w xs k ρ' xs' e vs ρ'' c c' v r},
      M.get f ρ = Some (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      cbstep_fuel (exposedb w) ρ'' e c (AS.Res v) ->
      cbstep_fuel ex (M.set x v ρ) k c' r ->
      (fst W) ! l = Some w ->
      (fst W) ! l' = Some w ->
      (if exposedb w
       then Forall to_exposed vs /\ to_exposed v
       else Forall (interact_with w) vs /\ interact_with_res w r) ->
      cbstep ex ρ (AS.Eletapp x f l xs k) (c + c') r

  | Cbstep_letapp_OOT :
    forall {x f f' l l' w xs k ρ' xs' e vs ρ'' c},
      M.get f ρ = Some (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ->
      get_list xs ρ = Some vs ->
      set_lists xs' vs (M.set f' (AS.Tag l' (AS.Vfun f' ρ' xs' e)) ρ') = Some ρ'' ->
      cbstep_fuel (exposedb w) ρ'' e c AS.OOT ->
      (fst W) ! l = Some w ->
      (fst W) ! l' = Some w ->
      (if exposedb w
       then Forall to_exposed vs
       else Forall (interact_with w) vs) ->
      cbstep ex ρ (AS.Eletapp x f l xs k) c AS.OOT

  | Cbstep_constr :
    forall {x l w t xs e r vs c},
      get_list xs ρ = Some vs ->
      (fst W) ! l = Some w ->
      (if exposedb w
       then Forall to_exposed vs
       else Forall (interact_with w) vs) ->
      cbstep_fuel ex (M.set x (AS.Tag l (AS.Vconstr t vs)) ρ) e c r ->
      cbstep ex ρ (AS.Econstr x l t xs e) c r

  | Cbstep_proj :
    forall {x l l' w t i y e c r v vs},
      M.get y ρ = Some (AS.Tag l' (AS.Vconstr t vs)) ->
      nth_error vs i = Some v ->
      (fst W) ! l = Some w ->
      (fst W) ! l' = Some w ->
      cbstep_fuel ex (M.set x v ρ) e c r ->
      cbstep ex ρ (AS.Eproj x l i y e) c r

  | Cbstep_case :
    forall {x l l' w cl t e r c vs},
      M.get x ρ = Some (AS.Tag l' (AS.Vconstr t vs)) ->
      find_tag cl t e ->
      (fst W) ! l = Some w ->
      (fst W) ! l' = Some w ->
      cbstep_fuel ex ρ e c r ->
      cbstep ex ρ (AS.Ecase x l cl) c r

  with cbstep_fuel (ex : bool) (ρ : AS.env) : AS.exp -> fuel -> AS.res -> Prop :=
  | CbstepF_OOT :
    forall {e},
      cbstep_fuel ex ρ e 0 AS.OOT

  | CbstepF_Step :
    forall {e c r},
      cbstep ex ρ e c r ->
      (if ex then to_exposed_res r else True) ->
      cbstep_fuel ex ρ e (S c) r.

  Hint Constructors cbstep : core.
  Hint Constructors cbstep_fuel : core.

  Scheme cbstep_ind' := Minimality for cbstep Sort Prop
  with cbstep_fuel_ind' := Minimality for cbstep_fuel Sort Prop.

  Theorem cbstep_deterministic v v' {ex ρ e c c' r r'}:
    cbstep ex ρ e c r ->
    cbstep ex ρ e c' r' ->
    r = AS.Res v ->
    r' = AS.Res v' ->
    (v = v' /\ c = c').
  Proof.
    intros H.
    generalize dependent v'.
    generalize dependent r'.
    generalize dependent c'.
    generalize dependent v.
    induction H using cbstep_ind' with (P := fun ex ρ e c r =>
                                              forall v c' r' v',
                                                cbstep ex ρ e c' r' ->
                                                r = AS.Res v -> r' = AS.Res v' ->
                                                v = v' /\ c = c')
                                      (P0 := fun ex ρ e c r =>
                                               forall v c' r' v',
                                                 cbstep_fuel ex ρ e c' r' ->
                                                 r = AS.Res v -> r' = AS.Res v' ->
                                                 v = v' /\ c = c');
      intros; subst.
    - inv H1; inv H2; invc; auto.
    - inv H1.
      edestruct IHcbstep; eauto.
    - inv H6; invc.
      edestruct IHcbstep; eauto.
    - inv H7; invc.
      edestruct IHcbstep; eauto.
      subst.
      edestruct IHcbstep0; eauto.
    - inv H7.
    - inv H3; invc.
      edestruct IHcbstep; eauto.
    - inv H4; invc.
      edestruct IHcbstep; eauto.
    - inv H4; invc.
      destruct (find_tag_deterministic H0 H9); subst.
      edestruct IHcbstep; eauto.
    - inv H0.
    - destruct ex; inv H1.
      + unfold to_exposed_res, to_exposed in *.
        destruct v; destruct v'.
        edestruct IHcbstep; eauto.
      + edestruct IHcbstep; eauto.
  Qed.

  Theorem cbstep_fuel_deterministic v v' {ex ρ e c c' r r'}:
    cbstep_fuel ex ρ e c r ->
    cbstep_fuel ex ρ e c' r' ->
    r = AS.Res v ->
    r' = AS.Res v' ->
    (v = v' /\ c = c').
  Proof.
    intros.
    inv H; inv H0; try discriminate.
    edestruct (cbstep_deterministic v v' H3 H); eauto.
  Qed.

  (* Checking steps refine labeled steps: cbstep adds W-consistency side-conditions,
     so every cbstep derivation projects down to a bstep derivation on the same
     expression with the same fuel and result. *)
  Lemma cbstep_to_bstep ex ρ e c r :
    cbstep ex ρ e c r ->
    AS.bstep ρ e c r.
  Proof.
    intros H.
    induction H using cbstep_ind' with
      (P := fun ex ρ e c r => AS.bstep ρ e c r)
      (P0 := fun ex ρ e c r => AS.bstep_fuel ρ e c r);
      intros; econstructor; eauto.
  Qed.

  Lemma cbstep_fuel_to_bstep_fuel ex ρ e c r :
    cbstep_fuel ex ρ e c r ->
    AS.bstep_fuel ρ e c r.
  Proof.
    intros H.
    inv H.
    - apply AS.BStepF_OOT.
    - eapply AS.BStepF_Step; eauto.
      eapply cbstep_to_bstep; eauto.
  Qed.

  (* Correlation lemmas: bstep and cbstep that both terminate on the same expression
     agree on fuel and value. Follows from cbstep's refinement of bstep plus
     AS.bstep_deterministic. *)
  Lemma cbstep_bstep ex ρ e c1 c2 v1 v2 :
    AS.bstep ρ e c1 (AS.Res v1) ->
    cbstep ex ρ e c2 (AS.Res v2) ->
    c1 = c2 /\ v1 = v2.
  Proof.
    intros Hb Hc.
    apply cbstep_to_bstep in Hc.
    destruct (AS.bstep_deterministic v1 v2 Hb Hc eq_refl eq_refl) as [Hv Hceq].
    split; auto.
  Qed.

  Lemma cbstep_fuel_bstep_fuel ex ρ e c1 c2 v1 v2 :
    AS.bstep_fuel ρ e c1 (AS.Res v1) ->
    cbstep_fuel ex ρ e c2 (AS.Res v2) ->
    c1 = c2 /\ v1 = v2.
  Proof.
    intros Hb Hc.
    apply cbstep_fuel_to_bstep_fuel in Hc.
    destruct (AS.bstep_fuel_deterministic v1 v2 Hb Hc eq_refl eq_refl) as [Hv Hceq].
    split; auto.
  Qed.

End Checking.

Section Approx.

  (* W1 \leq W2 iff W2 over-approximates W1 and annotate_info_inv are preserved *)
  (* We describe over-approximation via a web -> web mapping *)
  Definition leq (W1 W2 : annotate_info) :=
    exists f : web -> web,
      (forall w, w \in Exposed -> f w \in Exposed) /\
      (forall l w, (fst W1) ! l = Some w -> (fst W2) ! l = Some (f w)) /\
      (* (snd W1) -> (snd W2) *)
      (forall w im,
          (snd W1) ! w = Some im ->
          (if exposedb (f w)
           then ((snd W2) ! (f w) = None /\
                 (forall w', (w' \in im) -> (f w' \in Exposed)))
           else exists im',
                  (snd W2) ! (f w) = Some im' /\
                  (* im' ⊆ f(im) *)
                  (forall w', (w' \in im) -> f w' \in im'))) /\
        (* (snd W1) <- (snd W1) *)
        (forall w',
            w' \in Dom_map (snd W2) ->
            exists w,
              w \in Dom_map (snd W1) /\ f w = w').

  Lemma leq_refl W :
    annotate_info_inv W ->
    leq W W.
  Proof.
    destruct W as [wm im]. simpl. intros Hinv.
    unfold leq; simpl.
    exists (fun x => x).
    split; [auto|].
    split; [auto|].
    split.
    - intros w im0 Hsnd.
      destruct (exposed_reflect w) as [Hexp | Hnexp].
      + exfalso. apply (Hinv w); [eexists; eauto | auto].
      + eexists; split; eauto.
    - intros w' [im0 Hget].
      exists w'; split; [eexists; eauto | auto].
  Qed.

  Lemma leq_preserves_annotate_info_inv W1 W2:
    leq W1 W2 ->
    annotate_info_inv W1 ->
    annotate_info_inv W2.
  Proof.
    destruct W1 as [wm1 im1]. destruct W2 as [wm2 im2]. simpl.
    intros [f [Hexp [Hfst [Hsnd Hsurj]]]] Hinv1.
    intros w Hdom Hexpw.
    destruct (Hsurj w Hdom) as [w0 [[im0 Hsnd0] Hfw0]].
    specialize (Hsnd w0 im0 Hsnd0).
    subst w.
    destruct (exposed_reflect (f w0)) as [Hexpfw | Hnexpfw].
    - destruct Hsnd as [Hnone _].
      destruct Hdom as [im2v Hdomw].
      simpl in *.
      rewrite Hnone in Hdomw. discriminate.
    - apply Hnexpfw; exact Hexpw.
  Qed.

End Approx.

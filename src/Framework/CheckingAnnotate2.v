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

(* TODO: name the invariants *)

(* Annotate Based on The Checking Semantics *)

(* Maps labels to the actual webs. *)
Definition web_map : Type := M.t web.

(* Maps internal webs, `w`, to webs that interact with. `w` *)
Definition internal_web_map : Type := M.t webs.

Definition analysis_info : Type := web_map * internal_web_map.

(* Invariants for [analysis_info] *)
(* 1. Dom of internal_web_map only contains non-exposed web ids (encoded) *)
(* 2. Dom of internal_web_map is isomorphic to (Im of web_map \ Exposed) *)
(* 3. Each set in (Im of internal_web_map) is a subset of (Im of web_map U Exposed) *)

Definition analysis_info_inv (ainfo : analysis_info) : Prop :=
  match ainfo with
  | (wm, im) =>
      (forall w, (w \in Dom_map im) -> ~ (w \in Exposed))
  end.

Section Checking.

  Variable W : analysis_info.

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

  (* `W` is valid with respect to the checking big-step semantics *)
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
       else Forall (interact_with w) vs /\ interact_with w v) ->
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

  (* W1 \leq W2 iff W2 over-approximates W1 and analysis_info_inv are preserved *)
  (* We describe over-approximation via a web -> web mapping *)
  Definition leq (W1 W2 : analysis_info) :=
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
      (* (snd W1) <- (snd W2) *)
      (forall w',
          (w' \in Dom_map (snd W2)) ->
          exists w,
            w \in Dom_map (snd W1) /\ f w = w').

  Lemma leq_refl W :
    analysis_info_inv W ->
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

  Lemma leq_preserves_analysis_info_inv W1 W2:
    leq W1 W2 ->
    analysis_info_inv W1 ->
    analysis_info_inv W2.
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

  Lemma leq_trans W1 W2 W3 :
    leq W1 W2 ->
    leq W2 W3 ->
    leq W1 W3.
  Proof.
    destruct W1 as [wm1 im1].
    destruct W2 as [wm2 im2].
    destruct W3 as [wm3 im3].
    simpl.
    intros [f [Hexp12 [Hfst12 [Hsnd12 Hsurj12]]]]
           [g [Hexp23 [Hfst23 [Hsnd23 Hsurj23]]]].
    exists (fun x => g (f x)).
    split; [intros w Hw; apply Hexp23; apply Hexp12; exact Hw |].
    split; [intros l w Hl; apply Hfst23; apply Hfst12; exact Hl |].
    split.
    - (* snd clause *)
      intros w im0 Hsnd1.
      specialize (Hsnd12 w im0 Hsnd1).
      destruct (exposed_reflect (f w)) as [Hfw | Hnfw].
      + (* f w ∈ Exposed => g (f w) ∈ Exposed *)
        assert (Hgfw : g (f w) \in Exposed) by (apply Hexp23; exact Hfw).
        destruct Hsnd12 as [Hnone12 Him12].
        destruct (exposed_reflect (g (f w))); [| contradiction].
        split.
        * (* im3 ! (g (f w)) = None: derive contradiction from any Some via Hsurj23 + Hsnd23 *)
          destruct (im3 ! (g (f w))) as [im3v |] eqn:E; eauto; simpl.
          exfalso.
          assert (Hdom3 : g (f w) \in Dom_map im3) by (eexists; eauto).
          destruct (Hsurj23 _ Hdom3) as [w'' [[im2v Hw''] Hgw'']].
          specialize (Hsnd23 w'' im2v Hw'').
          destruct (exposed_reflect (g w'')) as [Hgw''exp | Hgw''nexp].
          -- destruct Hsnd23 as [Hnone3 _].
             simpl in *.
             rewrite Hgw'' in Hnone3; congruence.
          -- apply Hgw''nexp; rewrite Hgw''; exact Hgfw.
        * intros w' Hw'. apply Hexp23. apply Him12. exact Hw'.
      + (* f w ∉ Exposed *)
        destruct Hsnd12 as [im' [Hsnd2 Him12]].
        specialize (Hsnd23 (f w) im' Hsnd2).
        destruct (exposed_reflect (g (f w))) as [Hgfw | Hngfw].
        * destruct Hsnd23 as [Hnone3 Him23].
          split; [exact Hnone3 |].
          intros w' Hw'. apply Him23. apply Him12. exact Hw'.
        * destruct Hsnd23 as [im3' [Hsnd3 Him23]].
          exists im3'; split; [exact Hsnd3 |].
          intros w' Hw'. apply Him23. apply Him12. exact Hw'.
    - (* surjectivity: chain Hsurj23 then Hsurj12 *)
      intros w' Hdom3.
      destruct (Hsurj23 w' Hdom3) as [w'' [[im2v Hw''] Hgw'']].
      destruct (Hsurj12 w'' (ex_intro _ im2v Hw'')) as [w0 [Hdom1 Hfw0]].
      exists w0; split; [exact Hdom1 |].
      cbn. rewrite Hfw0. exact Hgw''.
  Qed.

  Lemma to_exposed_leq W1 W2 v:
    leq W1 W2 ->
    to_exposed W1 v ->
    to_exposed W2 v.
  Proof.
    intros [f [Hexp [Hfst [Hsnd Hsurj]]]] Hte.
    destruct v as [l vv].
    simpl in *.
    destruct Hte as [w [Hwm Hwexp]].
    exists (f w); split; [apply Hfst; exact Hwm | apply Hexp; exact Hwexp].
  Qed.

  Lemma to_exposed_leq_Forall W1 W2 vs:
    leq W1 W2 ->
    Forall (to_exposed W1) vs ->
    Forall (to_exposed W2) vs.
  Proof.
    intros.
    eapply Forall_impl with (P := to_exposed W1); eauto.
    intros; eapply to_exposed_leq; eauto.
  Qed.

  Lemma to_exposed_res_leq W1 W2 r:
    leq W1 W2 ->
    to_exposed_res W1 r ->
    to_exposed_res W2 r.
  Proof.
    intros.
    destruct r; auto; simpl in *.
    eapply to_exposed_leq; eauto.
  Qed.

  Lemma interact_with_to_exposed_leq W1 W2 (f_map : web -> web) w v:
    (forall l w', (fst W1) ! l = Some w' -> (fst W2) ! l = Some (f_map w')) ->
    (forall w' im,
        (snd W1) ! w' = Some im ->
        if exposedb (f_map w')
        then (snd W2) ! (f_map w') = None /\
               (forall w'', w'' \in im -> f_map w'' \in Exposed)
        else exists im',
            (snd W2) ! (f_map w') = Some im' /\
              (forall w'', w'' \in im -> f_map w'' \in im')) ->
    f_map w \in Exposed ->
    interact_with W1 w v ->
    to_exposed W2 v.
  Proof.
    intros Hfst Hsnd Hfw Hiv.
    destruct v as [lv vv].
    destruct Hiv as [wv [imv [Hlv [Hw_im Hwv_in]]]].
    specialize (Hsnd w imv Hw_im).
    destruct (exposed_reflect (f_map w)); [| contradiction].
    destruct Hsnd as [_ Hexposed].
    exists (f_map wv); split; [apply Hfst; exact Hlv | apply Hexposed; exact Hwv_in].
  Qed.

  Lemma interact_with_to_exposed_leq_Forall W1 W2 (f_map : web -> web) w vs:
    (forall l w', (fst W1) ! l = Some w' -> (fst W2) ! l = Some (f_map w')) ->
    (forall w' im,
        (snd W1) ! w' = Some im ->
        if exposedb (f_map w')
        then (snd W2) ! (f_map w') = None /\
               (forall w'', w'' \in im -> f_map w'' \in Exposed)
        else exists im',
            (snd W2) ! (f_map w') = Some im' /\
              (forall w'', w'' \in im -> f_map w'' \in im')) ->
    f_map w \in Exposed ->
    Forall (interact_with W1 w) vs ->
    Forall (to_exposed W2) vs.
  Proof.
    intros Hfst Hsnd Hfw HF.
    eapply Forall_impl; [| exact HF].
    intros v Hiv.
    eapply interact_with_to_exposed_leq; eauto.
  Qed.

  Lemma interact_with_to_exposed_res_leq W1 W2 (f_map : web -> web) w r:
    (forall l w', (fst W1) ! l = Some w' -> (fst W2) ! l = Some (f_map w')) ->
    (forall w' im,
        (snd W1) ! w' = Some im ->
        if exposedb (f_map w')
        then (snd W2) ! (f_map w') = None /\
               (forall w'', w'' \in im -> f_map w'' \in Exposed)
        else exists im',
            (snd W2) ! (f_map w') = Some im' /\
              (forall w'', w'' \in im -> f_map w'' \in im')) ->
    f_map w \in Exposed ->
    interact_with_res W1 w r ->
    to_exposed_res W2 r.
  Proof.
    intros Hfst Hsnd Hfw Hir.
    destruct r; simpl in *; [exact I |].
    eapply interact_with_to_exposed_leq; eauto.
  Qed.

  Lemma interact_with_leq W1 W2 (f_map : web -> web) w v:
    (forall l w', (fst W1) ! l = Some w' -> (fst W2) ! l = Some (f_map w')) ->
    (forall w' im,
        (snd W1) ! w' = Some im ->
        if exposedb (f_map w')
        then (snd W2) ! (f_map w') = None /\
               (forall w'', w'' \in im -> f_map w'' \in Exposed)
        else exists im',
            (snd W2) ! (f_map w') = Some im' /\
              (forall w'', w'' \in im -> f_map w'' \in im')) ->
    ~ f_map w \in Exposed ->
    interact_with W1 w v ->
    interact_with W2 (f_map w) v.
  Proof.
    intros Hfst Hsnd Hnfw Hiv.
    destruct v as [lv vv].
    destruct Hiv as [wv [imv [Hlv [Hw_im Hwv_in]]]].
    specialize (Hsnd w imv Hw_im).
    destruct (exposed_reflect (f_map w)); [contradiction |].
    destruct Hsnd as [im' [Him' Himf]].
    exists (f_map wv), im'.
    split; [apply Hfst; exact Hlv | split; [exact Him' | apply Himf; exact Hwv_in]].
  Qed.

  Lemma interact_with_leq_Forall W1 W2 (f_map : web -> web) w vs:
    (forall l w', (fst W1) ! l = Some w' -> (fst W2) ! l = Some (f_map w')) ->
    (forall w' im,
        (snd W1) ! w' = Some im ->
        if exposedb (f_map w')
        then (snd W2) ! (f_map w') = None /\
               (forall w'', w'' \in im -> f_map w'' \in Exposed)
        else exists im',
            (snd W2) ! (f_map w') = Some im' /\
              (forall w'', w'' \in im -> f_map w'' \in im')) ->
    ~ f_map w \in Exposed ->
    Forall (interact_with W1 w) vs ->
    Forall (interact_with W2 (f_map w)) vs.
  Proof.
    intros Hfst Hsnd Hnfw HF.
    eapply Forall_impl; [| exact HF].
    intros v Hiv.
    eapply interact_with_leq; eauto.
  Qed.

  Lemma interact_with_res_leq W1 W2 (f_map : web -> web) w r:
    (forall l w', (fst W1) ! l = Some w' -> (fst W2) ! l = Some (f_map w')) ->
    (forall w' im,
        (snd W1) ! w' = Some im ->
        if exposedb (f_map w')
        then (snd W2) ! (f_map w') = None /\
               (forall w'', w'' \in im -> f_map w'' \in Exposed)
        else exists im',
            (snd W2) ! (f_map w') = Some im' /\
              (forall w'', w'' \in im -> f_map w'' \in im')) ->
    ~ f_map w \in Exposed ->
    interact_with_res W1 w r ->
    interact_with_res W2 (f_map w) r.
  Proof.
    intros Hfst Hsnd Hnfw Hir.
    destruct r; simpl in *; [exact I |].
    eapply interact_with_leq; eauto.
  Qed.

  Lemma cbstep_to_exposed_res W ex ρ e c r :
    cbstep W ex ρ e c r ->
    to_exposed_res W r ->
    cbstep W true ρ e c r.
  Proof.
    intros Hstep.
    induction Hstep using cbstep_ind' with
      (P  := fun ex ρ e c r =>
               to_exposed_res W r -> cbstep W true ρ e c r)
      (P0 := fun ex ρ e c r =>
               to_exposed_res W r -> cbstep_fuel W true ρ e c r);
      intros; econstructor; eauto.
  Qed.

  Lemma cbstep_fuel_to_exposed_res W ex ρ e c r :
    cbstep_fuel W ex ρ e c r ->
    to_exposed_res W r ->
    cbstep_fuel W true ρ e c r.
  Proof.
    intros Hfuel Hto.
    inversion Hfuel; subst; econstructor; eauto.
    eapply cbstep_to_exposed_res; eauto.
  Qed.

  Lemma cbstep_approx W1 W2 ex ρ e i r :
    leq W1 W2 ->
    cbstep W1 ex ρ e i r ->
    cbstep W2 ex ρ e i r.
  Proof.
    intros.
    generalize dependent W2.
    induction H0 using cbstep_ind' with
      (P  := fun ex ρ e i r =>
               forall W2,
                 leq W1 W2 ->
                 cbstep W2 ex ρ e i r)
      (P0 := fun ex ρ e i r =>
               forall W2,
                 leq W1 W2 ->
                 cbstep_fuel W2 ex ρ e i r); intros.
    - (* Cbstep_ret *)
      destruct H1 as [f_map [_ [Hfst _]]].
      eapply Cbstep_ret; [exact H | apply Hfst; exact H0].
    - (* Cbstep_fun *)
      pose proof H1 as Hleq.
      destruct H1 as [f_map [_ [Hfst _]]].
      eapply Cbstep_fun; [apply Hfst; exact H | apply IHcbstep; exact Hleq].
    - (* Cbstep_app *)
      pose proof H6 as Hleq.
      destruct H6 as [f_map [Hexp [Hfst [Hsnd Hsurj]]]].
      eapply Cbstep_app; eauto.
      + destruct (exposed_reflect (f_map w)) as [Hfw | Hnfw].
        * split.
          { destruct (exposed_reflect w) as [Hw | Hnw].
            - destruct H4 as [Hfal _]. eapply to_exposed_leq_Forall; eauto.
            - destruct H4 as [Hfal _]. eapply interact_with_to_exposed_leq_Forall; eauto. }
          { destruct (exposed_reflect w) as [Hw | Hnw].
            - destruct H4 as [_ Hres]. simpl in Hres. eapply to_exposed_res_leq; eauto.
            - destruct H4 as [_ Hres]. eapply interact_with_to_exposed_res_leq; eauto. }
        * assert (Hnw : ~ w \in Exposed) by (intro Hw; apply Hnfw; apply Hexp; exact Hw).
          destruct (exposed_reflect w) as [Hw | _]; [contradiction |].
          destruct H4 as [Hfal Hiwres].
          split.
          { eapply interact_with_leq_Forall; eauto. }
          { eapply interact_with_res_leq; eauto. }
      + specialize (IHcbstep _ Hleq).
        destruct (exposed_reflect w) as [Hw | Hnw];
          destruct (exposed_reflect (f_map w)) as [Hfw | Hnfw]; eauto.
        * exfalso. apply Hnfw. apply Hexp. exact Hw.
        * eapply cbstep_fuel_to_exposed_res; eauto.
          destruct H4 as [_ Hres].
          eapply interact_with_to_exposed_res_leq; eauto.
    - (* Cbstep_letapp_Res *)
      pose proof H7 as Hleq.
      destruct H7 as [f_map [Hexp [Hfst [Hsnd Hsurj]]]].
      eapply Cbstep_letapp_Res with (w := (f_map w)); eauto.
      + (* cbstep_fuel (exposedb (f_map w)) ρ'' e c (Res v) *)
        specialize (IHcbstep _ Hleq).
        destruct (exposed_reflect w) as [Hw | Hnw];
          destruct (exposed_reflect (f_map w)) as [Hfw | Hnfw]; eauto.
        * exfalso. apply Hnfw. apply Hexp. exact Hw.
        * eapply cbstep_fuel_to_exposed_res; eauto.
          destruct H6 as [_ Hv]. simpl.
          eapply interact_with_to_exposed_leq; eauto.
      + destruct (exposed_reflect (f_map w)) as [Hfw | Hnfw].
        * split.
          { destruct (exposed_reflect w) as [Hw | Hnw].
            - destruct H6 as [Hfal _]. eapply to_exposed_leq_Forall; eauto.
            - destruct H6 as [Hfal _]. eapply interact_with_to_exposed_leq_Forall; eauto. }
          { destruct (exposed_reflect w) as [Hw | Hnw].
            - destruct H6 as [_ Hv]. eapply to_exposed_leq; eauto.
            - destruct H6 as [_ Hv]. eapply interact_with_to_exposed_leq; eauto. }
        * assert (Hnw : ~ w \in Exposed) by (intro Hw; apply Hnfw; apply Hexp; exact Hw).
          destruct (exposed_reflect w) as [Hw | _]; [contradiction |].
          destruct H6 as [Hfal Hv].
          split.
          { eapply interact_with_leq_Forall; eauto. }
          { eapply interact_with_leq; eauto. }
    - (* Cbstep_letapp_OOT *)
      pose proof H6 as Hleq.
      destruct H6 as [f_map [Hexp [Hfst [Hsnd Hsurj]]]].
      eapply Cbstep_letapp_OOT with (w := (f_map w)); eauto.
      + (* cbstep_fuel (exposedb (f_map w)) ρ'' e c OOT *)
        specialize (IHcbstep _ Hleq).
        destruct (exposed_reflect w) as [Hw | Hnw];
          destruct (exposed_reflect (f_map w)) as [Hfw | Hnfw]; eauto.
        * exfalso. apply Hnfw. apply Hexp. exact Hw.
        * eapply cbstep_fuel_to_exposed_res; eauto. exact I.
      + destruct (exposed_reflect (f_map w)) as [Hfw | Hnfw].
        * destruct (exposed_reflect w) as [Hw | Hnw].
          { eapply to_exposed_leq_Forall; eauto. }
          { eapply interact_with_to_exposed_leq_Forall; eauto. }
        * assert (Hnw : ~ w \in Exposed) by (intro Hw; apply Hnfw; apply Hexp; exact Hw).
          destruct (exposed_reflect w) as [Hw | _]; [contradiction |].
          eapply interact_with_leq_Forall; eauto.
    - (* Cbstep_constr *)
      pose proof H3 as Hleq.
      destruct H3 as [f_map [Hexp [Hfst [Hsnd Hsurj]]]].
      eapply Cbstep_constr; eauto.
      + destruct (exposed_reflect (f_map w)) as [Hfw | Hnfw].
        * destruct (exposed_reflect w) as [Hw | Hnw].
          { eapply to_exposed_leq_Forall; eauto. }
          { eapply interact_with_to_exposed_leq_Forall; eauto. }
        * assert (Hnw : ~ w \in Exposed) by (intro Hw; apply Hnfw; apply Hexp; exact Hw).
          destruct (exposed_reflect w) as [Hw | _]; [contradiction |].
          eapply interact_with_leq_Forall; eauto.
    - (* Cbstep_proj *)
      pose proof H4 as Hleq.
      destruct H4 as [f_map [_ [Hfst _]]].
      eapply Cbstep_proj;
        [exact H | exact H0 | apply Hfst; exact H1 | apply Hfst; exact H2
        | apply IHcbstep; exact Hleq].
    - (* Cbstep_case *)
      pose proof H4 as Hleq.
      destruct H4 as [f_map [_ [Hfst _]]].
      eapply Cbstep_case;
        [exact H | exact H0 | apply Hfst; exact H1 | apply Hfst; exact H2
        | apply IHcbstep; exact Hleq].
    - (* CbstepF_OOT *)
      constructor.
    - (* CbstepF_Step *)
      pose proof H1 as Hleq.
      destruct H1 as [f_map [_ [Hfst _]]].
      eapply CbstepF_Step; [apply IHcbstep; exact Hleq |].
      destruct ex; [| exact I].
      eapply to_exposed_res_leq; eauto.
  Qed.

  Lemma cbstep_fuel_approx W1 W2 ex ρ e i r :
    leq W1 W2 ->
    cbstep_fuel W1 ex ρ e i r ->
    cbstep_fuel W2 ex ρ e i r.
  Proof.
    intros Hleq Hfuel.
    inversion Hfuel; subst.
    - constructor.
    - eapply CbstepF_Step.
      + eapply cbstep_approx; eauto.
      + destruct ex; [| exact I].
        eapply to_exposed_res_leq; eauto.
  Qed.

  Definition W_trivial (W : analysis_info) : Prop :=
    match W with
    | (wm, im) => (forall l, wm ! l = Some w0) /\ im = M.empty _
    end.

  Lemma W_trivial_analysis_info_inv WT :
    W_trivial WT ->
    analysis_info_inv WT.
  Proof.
    destruct WT as [wm im].
    intros [_ Him]. simpl.
    intros w [v Hv].
    rewrite Him, M.gempty in Hv. discriminate.
  Qed.

  Lemma W_trivial_leq_top WT :
    W_trivial WT ->
    forall W, leq W WT.
  Proof.
    destruct WT as [wm im].
    intros [Hwm Him] W.
    exists (fun _ => w0).
    split; [intros w _; exact w0_exposed |].
    split; [intros l w' Hl; simpl; rewrite Hwm; reflexivity |].
    split.
    - intros w' im' Hget. simpl. rewrite w0_exposedb.
      split.
      + rewrite Him. apply M.gempty.
      + intros w'' _. exact w0_exposed.
    - intros w' [v Hv]. simpl in Hv. rewrite Him, M.gempty in Hv. discriminate.
  Qed.

End Approx.

Section Trans.

  Variable W : analysis_info.

  (* Transformation Specification *)
  Inductive trans (Γ : vars) : AS.exp -> AT.exp -> Prop :=
  | Trans_ret :
    forall x,
      (x \in Γ) ->
      trans Γ (AS.Eret x) (AT.Eret x)

  | Trans_fun :
    forall {f l w xs e k e' k'},
      (fst W) ! l = Some w ->
      trans (FromList xs :|: (f |: Γ)) e e' ->
      trans (f |: Γ) k k' ->
      trans Γ (AS.Efun f l xs e k) (AT.Efun f w xs e' k')

  | Trans_app :
    forall {f l w xs},
      (fst W) ! l = Some w ->
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans Γ (AS.Eapp f l xs) (AT.Eapp f w xs)

  | Trans_letapp :
    forall {x f l w xs k k'},
      (fst W) ! l = Some w ->
      (f \in Γ) ->
      (FromList xs \subset Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (AS.Eletapp x f l xs k) (AT.Eletapp x f w xs k')

  | Trans_constr :
    forall {x l w t xs k k'},
      (fst W) ! l = Some w ->
      (FromList xs \subset Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (AS.Econstr x l t xs k) (AT.Econstr x w t xs k')

  | Trans_proj :
    forall {l w x y k k' n},
      (fst W) ! l = Some w ->
      (y \in Γ) ->
      trans (x |: Γ) k k' ->
      trans Γ (AS.Eproj x l n y k) (AT.Eproj x w n y k')

  | Trans_case_nil :
    forall {l w x},
      (fst W) ! l = Some w ->
      (x \in Γ) ->
      trans Γ (AS.Ecase x l []) (AT.Ecase x w [])

  | Trans_case_cons :
    forall {x l w e e' t cl cl'},
      (fst W) ! l = Some w ->
      (x \in Γ) ->
      trans Γ e e' ->
      trans Γ (AS.Ecase x l cl) (AT.Ecase x w cl') ->
      trans Γ (AS.Ecase x l ((t, e) :: cl)) (AT.Ecase x w ((t, e') :: cl')).

  Hint Constructors trans : core.

  Lemma trans_exp_inv {Γ e e'} :
    trans Γ e e' ->
    (AT.occurs_free e') \subset (AS.occurs_free e).
  Proof.
    unfold Ensembles.Included, Ensembles.In.
    intros H.
    induction H; simpl; intros; auto.
    - inv H0; auto.
    - inv H2; auto.
    - inv H2; auto.
    - inv H3; auto.
    - inv H2; auto.
    - inv H2; auto.
    - inv H1; auto.
    - inv H3; auto.
  Qed.

End Trans.

Section Relation.

  (* Cross-language Logical Relations *)
  Definition R' (P : nat -> analysis_info -> AS.wval -> AT.wval -> Prop) (i : nat) (W : analysis_info) (r1 : AS.res) (r2 : AT.res) :=
    match r1, r2 with
    | AS.OOT, AT.OOT => True
    | AS.Res v1, AT.Res v2 => P i W v1 v2
    | _, _ => False
    end.

  Definition E' (P : nat -> analysis_info -> AS.wval -> AT.wval -> Prop) (ex : bool) (i : nat) (W : analysis_info) (ρ1 : AS.env) (e1 :AS.exp) (ρ2 : AT.env) (e2 : AT.exp) : Prop :=
    forall j1 r1,
      j1 <= i ->
      AS.bstep_fuel ρ1 e1 j1 r1 ->
      exists j2 r2,
        AT.bstep_fuel ex ρ2 e2 j2 r2 /\
        R' P (i - j1) W r1 r2.

  (* An expression is well-annotated with respect to some analysis info, `W` *)
  Definition well_annotated ex W ρ e :=
    forall i r,
      AS.bstep_fuel ρ e i r ->
      cbstep_fuel W ex ρ e i r.

  Fixpoint V (i : nat) (W : analysis_info) (wv1 : AS.wval) (wv2 : AT.wval) {struct i} : Prop :=
    wf_val wv2 /\
    match wv1, wv2 with
    | AS.TAG _ l1 v1, AT.TAG _ w2 v2 =>
        (fst W) ! l1 = Some w2 /\
        (w2 \in Exposed -> exposed wv2) /\
        match v1, v2 with
        | AS.Vconstr c1 vs1, AT.Vconstr c2 vs2 =>
            c1 = c2 /\
            match i with
            | 0 => length vs1 = length vs2
            | S i0 => Forall2 (V i0 W) vs1 vs2
            end

        | AS.Vfun f1 ρ1 xs1 e1, AT.Vfun f2 ρ2 xs2 e2 =>
            length xs1 = length xs2 /\
            match i with
            | 0 => True
            | S i0 =>
                forall j W1 vs1 vs2 ρ3 ρ4,
                  j <= i0 ->
                  leq W W1 -> (* Specify all overapproximation of `W` works for the function body *)
                  (* REVISIT: vs1 and W1? Also r1 (result of applying e1)? *)
                  (w2 \in Exposed -> Forall exposed vs2) ->
                  Forall2 (V (i0 - (i0 - j)) W1) vs1 vs2 ->
                  set_lists xs1 vs1 (M.set f1 (AS.Tag l1 (AS.Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                  set_lists xs2 vs2 (M.set f2 (AT.Tag w2 (AT.Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                  well_annotated (exposedb w2) W1 ρ3 e1 ->
                  E' V (exposedb w2) (i0 - (i0 - j)) W1 ρ3 e1 ρ4 e2
            end

        | _, _ => False
        end
    end.

  Definition R := (R' V).

  Definition E := (E' V).

  (* Monotonicity Lemmas *)
  Lemma V_mono_Forall_aux :
    forall i j W (V : nat -> analysis_info -> AS.wval -> AT.wval -> Prop) vs1 vs2,
      (forall k : nat,
          k < S i ->
          forall (j : nat) v1 v2, V k W v1 v2 -> j <= k -> V j W v1 v2) ->
      Forall2 (V i W) vs1 vs2 ->
      j <= i ->
      Forall2 (V j W) vs1 vs2.
  Proof.
    intros.
    revert vs2 H0.
    induction vs1; intros; inv H0; auto.
    rename l' into vs2.
    constructor; auto.
    eapply H; eauto; lia.
  Qed.

  Lemma V_mono i W :
    forall {j v1 v2},
      V i W v1 v2 ->
      j <= i ->
      V j W v1 v2.
  Proof.
    induction i using lt_wf_rec; intros.
    destruct v1; destruct v2.
    destruct i; simpl in H0;
      destruct j; simpl; intros;
      destruct H0 as [Hv1 [Hl [Hex HV]]]; subst.
    - repeat (split; auto).
    - inv H1.
    - repeat (split; auto).
      destruct v; destruct v0; try contradiction.
      + destruct HV.
        destruct (exposed_reflect w); fcrush.
      + destruct HV as [Hc HV]; subst.
        repeat split; auto.
        eapply Forall2_length; eauto.
    - repeat (split; auto).
      destruct v; destruct v0; try contradiction.
      + destruct HV as [Hlen HV]; subst.
        repeat split; auto; intros.
        destruct (exposed_reflect w).
        * specialize (HV j0 W1 vs1 vs2 ρ3 ρ4).
          rewrite normalize_step in *; try lia.
          eapply HV; eauto; lia.
        * specialize (HV j0 W1 vs1 vs2 ρ3 ρ4).
          rewrite normalize_step in *; try lia.
          eapply HV; eauto; lia.
      + destruct HV as [Heqc HV]; subst.
        repeat split; auto.
        eapply V_mono_Forall_aux; eauto; lia.
  Qed.

  Lemma well_annotated_approx W1 W2 ex ρ e:
    leq W1 W2 ->
    well_annotated ex W1 ρ e ->
    well_annotated ex W2 ρ e.
  Proof.
    unfold well_annotated.
    intros.
    eapply H0 in H1; eauto.
    eapply cbstep_fuel_approx; eauto.
  Qed.

  Lemma V_mono_W i W :
    forall {W1 v1 v2},
      V i W v1 v2 ->
      leq W W1 ->
      exists v3, V i W1 v1 v3.
  Proof.
  Admitted.

End Relation.

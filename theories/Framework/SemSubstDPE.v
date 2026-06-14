From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF DPE SemSubst.

(* DPE

let f_work = fun [w_work] (x) ->
               let g0 = fun [w_g0] () ->
                          [[ let f_wrap = fun [w_wrap] (x y) -> {f_work} [w_work] x (* the hole doesn't need to be at the elimination site *)
                             in f_wrap ]]
               let f = g0 [w_g0] ()
               in x + 1
let g1 = fun [w_g1] () ->
           let f_wrap = fun [w_wrap] (x y) -> f_work [w_work] x
           in f_wrap
let f = g1 [w_g1] ()
let h1 = fun [w_h1] (f') -> f' [w_wrap] (1, 2)
let h2 = fun [w_h2] (f') -> let r = f' [w_wrap] (1, 2) in r + 1
in h1 [w_h1] f
   h2 [w_h2] f

~~>

let f_work = fun [w_work] (x) ->
               let g0 = fun [w_g0] () -> f_work
               let f = g0 [w_g0] ()
               in x + 1
let g1 = fun [w_g1] () -> f_work
let f = g1 [w_g1] ()
let h1 = fun [w_h1] (f') ->
          let g3 = fun [w_g3] () ->
                    let f'_wrap = fun [w_wrap] (x, y) -> f' [w_work] x
                    in f'_wrap
          let f'_wrap = g3 [w_g3] ()
          in f'_wrap [w_wrap] (1, 2)
let h2 = fun [w_h2] (f') ->
          let g3 = fun [w_g3] () ->
                    let f'_wrap = fun [w_wrap] (x, y) -> f' [w_work] x
                    in f'_wrap
          let f'_wrap = g3 [w_g3] ()
          let r = f'_wrap [w_wrap] (1, 2)
          in r + 1
in h1 [w_h1] f
   h2 [w_h2] f

*)

Module DPEWrap <: WrapSig.

  Definition trans_info_t := list bool.

  Definition wrapper_info_t := list var.

  Definition wrap
    (bs : trans_info_t) (ys : wrapper_info_t)
    (f_work : var) (w_work : web)
    (f_wrap : var) (w_wrap : web) : exp :=
    (Efun f_wrap w_wrap ys (Eapp f_work w_work (live_args ys bs))
       (Eret f_wrap)).

  Definition wrap_prop
    (bs : trans_info_t) (ys : wrapper_info_t)
    (f_work : var) (w_work : web)
    (f_wrap : var) (w_wrap : web) : Prop :=
    length bs = length ys /\
    (~ In f_wrap ys) /\
    NoDup ys.

  Lemma free_vars_wrap bs ys w_work f_wrap w_wrap f:
    let wrapper := (wrap bs ys f w_work f_wrap w_wrap) in
    (~ f \in (bound_var wrapper)) ->
    (occurs_free wrapper <--> [set f]).
  Proof.
    unfold wrap, Same_set, Ensembles.Included, Ensembles.In.
    intros.
    split; intros.
    - inv H0.
      + inv H8; contradiction.
      + inv H9.
        * constructor.
        * exfalso.
          apply H8.
          eapply live_args_In; eauto.
    - inv H0.
      eapply Free_fun2; eauto.
      intros Hc; subst.
      apply H; auto.
  Qed.

  Lemma bstep_fuel_wf_wrap bs ys f_work w_work f_wrap w_wrap v_work ρ:
    let wrapper := (wrap bs ys f_work w_work f_wrap w_wrap) in
    (~ f_work \in bound_var wrapper) ->
    exists k ρ' xs e,
      bstep_fuel false (M.set f_work v_work ρ) wrapper k (Res (Tag w_wrap (Vfun f_wrap ρ' xs e))).
  Proof.
    unfold wrap.
    exists 2, (M.set f_work v_work ρ), ys, (Eapp f_work w_work (live_args ys bs)).
    repeat (constructor; auto).
    rewrite M.gss; auto.
  Qed.

  Lemma bound_vars_wrap_inv bs ys f w f_wrap w_wrap :
    let wrapper := (wrap bs ys f w f_wrap w_wrap) in
    (~ f \in bound_var wrapper) ->
    (f <> f_wrap) /\ (~ In f ys).
  Proof.
    unfold wrap.
    intros.
    split; intros Hc; subst;
      apply H; auto.
  Qed.

  Lemma bstep_fuel_wrap_inv' {bs ys f_work w_work f_wrap w_wrap v_work ρ k v_wrap}:
    let wrapper := (wrap bs ys f_work w_work f_wrap w_wrap) in
    bstep_fuel false (M.set f_work v_work ρ) wrapper k (Res v_wrap) ->
    v_wrap = Tag w_wrap (Vfun f_wrap (M.set f_work v_work ρ) ys (Eapp f_work w_work (live_args ys bs))).
  Proof.
    unfold wrap.
    intros.
    inv H.
    inv H0.
    inv H8.
    inv H.
    rewrite M.gss in *.
    inv H5; auto.
  Qed.

End DPEWrap.

Module SemSubstDPE <: SemSubstSig DPEWrap.

  Module SV := SemSubstV DPEWrap.
  Import SV DPEWrap.

  Lemma get_list_live_args {A} :
    forall xs bs vs ρ,
      length xs = length bs ->
      @get_list A xs ρ = Some vs ->
      get_list (live_args xs bs) ρ = Some (live_args vs bs).
  Proof.
    intros xs.
    induction xs; simpl; intros;
      destruct bs; inv H.
    - inv H0; auto.
    - destruct (ρ ! a) eqn:Heq1; try discriminate.
      destruct (get_list xs ρ) eqn:Heq2; try discriminate.
      inv H0.
      destruct b; simpl.
      + rewrite Heq1.
        erewrite IHxs; eauto.
      + erewrite IHxs; eauto.
  Qed.

  Lemma get_list_live_args_Forall :
    forall (V : nat -> wval -> wval -> Prop) ys vs1 ρ0 ρ1 vs2 vs bs i,
      NoDup ys ->
      length ys = length bs ->
      set_lists ys vs1 ρ0 = Some ρ1 ->
      get_list (live_args ys bs) ρ1 = Some vs ->
      Forall2 (V i) vs1 vs2 ->
      Forall2 (V i) vs (live_args vs2 bs).
  Proof.
    intros V ys.
    induction ys; simpl; intros;
      destruct bs; inv H0;
      simpl in *.
    - destruct vs1; try discriminate.
      inv H1; inv H2; inv H3; auto.
    - destruct vs1; try discriminate.
      destruct (set_lists ys vs1 ρ0) eqn:Heq1; try discriminate.
      inv H; inv H1.
      assert (~ In a (live_args ys bs)) by (eapply live_args_not_In; eauto).

      destruct b; simpl in *.
      + rewrite M.gss in *.
        destruct (get_list (live_args ys bs) (map_util.M.set a w t)) eqn:Heq2; try discriminate.
        inv H2; inv H3.
        erewrite get_list_set_neq in Heq2; eauto.
        constructor; eauto.
      + erewrite get_list_set_neq in H2; eauto.
        inv H3; simpl; eauto.
  Qed.

  Lemma V_wrapper_refl bs ys f_work f_work' w_work f_wrap f_wrap' w_wrap :
    let wrapper := (wrap bs ys f_work w_work f_wrap w_wrap) in
    let wrapper' := (wrap bs ys f_work' w_work f_wrap' w_wrap) in

    (~ f_work \in bound_var wrapper) ->
    (~ f_work' \in bound_var wrapper') ->
    (~ w_work \in Exposed) ->

    wrap_prop bs ys f_work w_work f_wrap w_wrap ->

    forall i ρ ρ' v_work v_work' k k' v_wrap v_wrap',
      wf_env ρ ->
      wf_env ρ' ->

      bstep_fuel false (M.set f_work (Tag w_work v_work) ρ) wrapper k (Res (Tag w_wrap v_wrap)) ->
      bstep_fuel false (M.set f_work' (Tag w_work v_work') ρ') wrapper' k' (Res (Tag w_wrap v_wrap')) ->

      match i with
      | 0 =>
          V_refl0 v_wrap v_wrap'
      | S i0 =>
          V_refl (fun j => V (i0 - (i0 - j))) (fun j => E' V false (i0 - (i0 - j))) i0 w_work v_work v_work' ->
          V_refl (fun j => V (i0 - (i0 - j))) (fun j => E' V false (i0 - (i0 - j))) i0 w_wrap v_wrap v_wrap'
      end.
  Proof.
    intros Hwrapper Hwrapper' Hf_work Hf_work' Hw_work Hwrap_prop i.
    destruct Hwrap_prop as [Hinfo [_ Hinfo1]].
    edestruct bound_vars_wrap_inv with (f := f_work) as [Hf_work1 Hf_work2]; eauto.
    edestruct bound_vars_wrap_inv with (f := f_work') as [Hf_work'1 Hf_work'2]; eauto.

    induction i using lt_wf_rec1.
    intros ρ ρ' v_work v_work' k k' v_wrap v_wrap' Hwfρ Hwfρ' Hwrap1 Hwrap2.
    subst Hwrapper.
    subst Hwrapper'.
    eapply bstep_fuel_wrap_inv' in Hwrap1; eauto; inv Hwrap1.
    eapply bstep_fuel_wrap_inv' in Hwrap2; eauto; inv Hwrap2.
    destruct i.
    unfold V_refl0; auto.
    intros.
    unfold V_refl.
    split; auto; intros.
    unfold E'; intros.
    inv H8.
    exists 0, OOT; split; simpl; auto.

    inv H9.
    erewrite <- (set_lists_not_In _ _ _ _ f_work H5) in H13; eauto.
    rewrite M.gso in H13; auto.
    rewrite M.gss in H13.
    inv H13.

    unfold V_refl in H0.
    destruct v_work'; try contradiction.
    destruct H0 as [Hlen HV_work].
    unfold E' in HV_work.
    destruct (exposed_reflect w_work); try contradiction.

    rename t into ρ0.

    edestruct (set_lists_length3 (M.set v (Tag w_work (Vfun v ρ0 l e0)) ρ0) l (live_args vs2 bs)) as [ρ0' Heqρ0']; eauto.
    unfold var in *.
    rewrite <- Hlen.
    rewrite (set_lists_length_eq _ _ _ _ H15).
    rewrite <- (get_list_length_eq _ _ _ H14).
    eapply live_args_length; eauto.
    rewrite (set_lists_length_eq _ _ _ _ H6); auto.

    rewrite_math ((i - (i - j) - S c) = (i - (i - (j - 1)) - c)).

    edestruct (HV_work (j - 1) vs (live_args vs2 bs) ρ'' ρ0') with (j1 := c) as [j2 [r2 [He0 HR]]]; eauto; try lia.
    - intros; contradiction.
    - intros; contradiction.
    - eapply get_list_live_args_Forall with (ρ1 := ρ3); eauto.
      eapply V_mono_Forall; eauto; lia.
    - exists (S j2), r2; split; eauto.
      constructor; auto.
      econstructor; eauto.
      + erewrite <- (set_lists_not_In _ _ _ _ f_work' H6); eauto.
        rewrite M.gso; auto.
        rewrite M.gss; auto.
      + eapply get_list_live_args; eauto.
        eapply get_list_set_lists; eauto.
      + destruct (exposed_reflect w_work); try contradiction; auto.
      + intros; contradiction.
  Qed.

End SemSubstDPE.

Module SE := SemSubstExposed DPEWrap SemSubstDPE.
Import SE.

(* Specification *)
Inductive trans (Γ : Ensemble var) : exp -> exp -> Prop :=
| Trans_fun :
  forall {bs f f_wrap w xs ys e k e' k' f_temp w_temp w_wrap},
    let wrapper := (wrap bs ys f w f_wrap w_wrap) in

    trans (FromList xs :|: (f |: Γ)) e e' ->
    trans (f |: Γ) k k' ->

    (* worker spec *)
    L ! w = None ->
    (~ w \in Exposed) ->
    (~ In f xs) ->
    (~ f \in bound_var wrapper) ->

    (* temp binder spec *)
    L ! w_temp = None ->
    (~ w_temp \in Exposed) ->
    (~ f_temp \in (occurs_free e)) ->
    (~ f_temp \in (occurs_free k)) ->
    (~ f_temp \in Γ) ->
    f_temp <> f ->
    (~ In f_temp xs) ->

    (* wrapper spec *)
    L ! w_wrap = Some (bs, ys, w) ->
    wrap_prop bs ys f w f_wrap w_wrap ->

    trans Γ (Efun f w xs
               (Efun f_temp w_temp [] wrapper
                  (Eletapp f f_temp w_temp [] e))
               (Efun f_temp w_temp [] wrapper
                  (Eletapp f f_temp w_temp [] k)))
      (Efun f w xs e' k') (* turn the wrapper into the worker *)

| Trans_app :
  forall {bs f w xs ys f_temp w_temp f_wrap w_wrap},
    let wrapper := (wrap bs ys f w f_wrap w_wrap) in

    (f \in Γ) ->
    (FromList xs \subset Γ) ->

    (* worker spec *)
    L ! w = None ->
    (~ w \in Exposed) ->
    (~ f \in bound_var wrapper) ->

    (* temp binder spec *)
    L ! w_temp = None ->
    (~ w_temp \in Exposed) ->
    f_temp <> f ->
    (~ In f_temp xs) ->

    (* wrapper spec *)
    L ! w_wrap = Some (bs, ys, w) ->
    wrap_prop bs ys f w f_wrap w_wrap ->

    trans Γ (Eapp f w_wrap xs)
      (Efun f_temp w_temp [] wrapper
         (Eletapp f_temp f_temp w_temp [] (* turn the worker into the wrapper *)
            (Eapp f_temp w_wrap xs))).

Hint Constructors trans : core.

(* Invariants about [trans] *)
Lemma trans_exp_inv {Γ e e'} :
  trans Γ e e' ->
  (occurs_free e') \subset (occurs_free e).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros H.
  induction H; intros; subst; auto.
  - inv H14.
    + eapply IHtrans2 in H22; eauto.
      econstructor; eauto.
      econstructor; eauto.
      intros Hc; subst.
      apply H8; auto.
    + eapply IHtrans1 in H23; eauto.
      eapply Free_fun2; eauto.
      eapply Free_fun1; eauto.
      intros Hc; subst.
      apply H7; auto.
  - destruct H9 as [? [? ?]].
    inv H10.
    + inv H20; try contradiction.
      inv H21; auto; contradiction.
    + inv H21; auto.
      * inv H22; contradiction.
      * inv H23; auto.
        exfalso.
        apply H22.
        eapply live_args_In; eauto.
Qed.

(* Fundamental Property *)
Lemma fundamental_property {Γ e e'} :
  trans Γ e e' -> trans_correct Γ e e'.
Proof.
  intro H.
  induction H.
  - eapply fun_compat_trans; eauto.
    eapply trans_exp_inv; eauto.
    eapply trans_exp_inv; eauto.
  - eapply app_compat_trans; eauto.
Qed.

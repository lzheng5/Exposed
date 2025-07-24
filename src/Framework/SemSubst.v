From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF Exposed.

(* Semantic Substitution *)

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

(* Defunc

[[ let gf = fun [w_gf] () {f_work}
   let t = gf [w_gf] ()
   in case [w_work] t
      C => let t' = proj [w_work] t in t'
      ... ]]

let f_wrap = fun [w_wrap] (x) ->
                let f_work = C [w_work] f_wrap
                let g0 = fun [w_g0] () ->
                           [[ case [w_work] {f_work}
                              C => let t = proj [w_work] {f_work}
                                   in t
                              ... ]]
                let f = g0 [w_g0] ()
                in x + 1
let f_work = C [w_work] f_wrap
let g1 = fun [w_g1] () ->
            [[ case [w_work] {f_work}
               C => let t = proj [w_work] {f_work}
                    in t
               ... ]]
let f = g1 [w_g1] ()
let h = fun [w_h] (f') -> f' [w_wrap] 0
in h [w_h] f

~~>

let f_wrap = fun [w_wrap] (x) ->
                let f_work = C [w_work] f_wrap
                let g0 = fun [w_g0] () -> f_work
                let f = g0 [w_g0] ()
                in x + 1
let f_work = C [w_work] f_wrap
let g1 = fun [w_g1] () -> f_work
let f = g1 [w_g1] ()
let h = fun [w_h] (f') ->
          let g2 = fun [w_g2] () ->
                     case [w_work] f'
                     C => let t = proj [w_work] f'
                          in t
                     ...
          let f' = g2 [w_g2] ()
          f' [w_wrap] 0
in h [w_h] f

*)

Module Type WrapSig.

  (* transformation specific information *)
  Parameter trans_info_t : Type.

  (* wrapper specific information *)
  Parameter wrapper_info_t : Type.

  Parameter wrap : trans_info_t -> wrapper_info_t -> var -> web -> var -> web -> exp.

  (* wrapper property *)
  Parameter wrap_prop : trans_info_t -> wrapper_info_t -> var -> web -> var -> web -> Prop.

  Parameter free_vars_wrap :
    forall tinfo winfo w_work f_wrap w_wrap f,
      let wrapper := (wrap tinfo winfo f w_work f_wrap w_wrap) in
      (~ f \in (bound_var wrapper)) ->
      (occurs_free wrapper <--> [set f]).

  Parameter bstep_fuel_wf_wrap:
    forall tinfo winfo f_work w_work f_wrap w_wrap v_work ρ,
      let wrapper := (wrap tinfo winfo f_work w_work f_wrap w_wrap) in
      (~ f_work \in bound_var wrapper) ->
      exists k ρ' xs e,
        bstep_fuel false (M.set f_work v_work ρ) wrapper k (Res (Tag w_wrap (Vfun f_wrap ρ' xs e))).

End WrapSig.

Module WrapUtils (WM : WrapSig).

  Import WM.

  Lemma bstep_fuel_wrap_inv {tinfo winfo f_work w_work f_wrap w_wrap v_work ρ k v_wrap}:
    let wrapper := (wrap tinfo winfo f_work w_work f_wrap w_wrap) in
    (~ f_work \in bound_var wrapper) ->
    bstep_fuel false (M.set f_work v_work ρ) wrapper k (Res v_wrap) ->
    exists ρ' xs e, v_wrap = Tag w_wrap (Vfun f_wrap ρ' xs e).
  Proof.
    intros Hwrapper Hf_work Hstep.
    subst Hwrapper.
    edestruct bstep_fuel_wf_wrap with (v_work := v_work) (ρ := ρ) as [k' [ρ' [xs [e Hstep']]]]; eauto.
    edestruct (bstep_fuel_deterministic v_wrap (Tag w_wrap (Vfun f_wrap ρ' xs e)) Hstep Hstep') as [Heq1 Heq2]; eauto.
  Qed.

End WrapUtils.

Module SemSubstV (WM : WrapSig).

  Export WM.
  Module LT <: Exposed.LTy. Definition t : Type := (trans_info_t * wrapper_info_t * web). End LT.
  Module LM := Exposed.DefaultL LT.
  Export LM.

  (* Logical Relations *)
  Module VTransM <: Exposed.VTrans LM.

    (* Relating wrapper and worker *)
    Definition V_trans
      (V' : nat -> wval -> wval -> Prop)
      (E' : nat -> env -> exp -> env -> exp -> Prop)
      (i0 : nat) (d : trans_info_t * wrapper_info_t * web)
      (w_wrap : web) (v_wrap : val) (w_work' : web) (v_work : val) :=
      let '(tinfo, winfo, w_work) := d in
      w_work = w_work' /\
        match v_wrap with
        | Vfun f1 ρ1 xs1 e1 =>
            forall f_work f_wrap ρ,
              let wrapper := (wrap tinfo winfo f_work w_work f_wrap w_wrap) in
              (~ f_work \in bound_var wrapper) ->
              wf_env ρ ->

              exists k ρ2 xs2 e2,
                bstep_fuel false (M.set f_work (Tag w_work v_work) ρ) wrapper k (Res (Tag w_wrap (Vfun f_wrap ρ2 xs2 e2))) /\
                  length xs1 = length xs2 /\

                  forall j vs1 vs2 ρ3 ρ4,
                    j <= i0 ->
                    Forall wf_val vs1 ->
                    Forall2 (V' j) vs1 vs2 ->
                    set_lists xs1 vs1 (M.set f1 (Tag w_wrap (Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
                    set_lists xs2 vs2 (M.set f_wrap (Tag w_wrap (Vfun f_wrap ρ2 xs2 e2)) ρ2) = Some ρ4 ->
                    E' j ρ3 e1 ρ4 e2

        | _ => False
        end.

    Lemma V_trans_mono V E i j d w1 v1 w2 v2 :
      (forall k : nat,
          k < S i ->
          forall (j : nat) (v1 v2 : wval), V k v1 v2 -> j <= k -> V j v1 v2) ->
      V_trans (fun i' => V (i - (i - i'))) (fun i' => E (i - (i - i'))) i d w1 v1 w2 v2 ->
      j <= i ->
      V_trans (fun j' => V (j - (j - j'))) (fun j' => E (j - (j - j'))) j d w1 v1 w2 v2.
    Proof.
      intros HI. intros.
      destruct v1; auto;
        simpl in *; try contradiction.
      rename l into xs1.
      unfold V_trans in *.
      destruct d.
      destruct p.
      destruct H as [Hw HV]; subst.
      repeat split; eauto; intros.
      edestruct (HV f_work f_wrap ρ) as [k [ρ2 [xs2 [e2 [Hstep [Hlen HV']]]]]]; eauto.
      exists k, ρ2, xs2, e2; repeat (split; auto); intros.
      specialize (HV' j0 vs1 vs2 ρ3 ρ4).
      rewrite normalize_step in *; try lia.
      eapply HV'; eauto; try lia.
    Qed.

  End VTransM.
  Export VTransM.

  Module EM := Exposed.Exposed LM VTransM.
  Export EM.

End SemSubstV.

Module Type SemSubstSig (WM : WrapSig).

  Module SV := SemSubstV WM.
  Import WM SV.

  Parameter V_wrapper_refl :
    forall tinfo winfo f_work f_work' w_work f_wrap f_wrap' w_wrap,
      let wrapper := (wrap tinfo winfo f_work w_work f_wrap w_wrap) in
      let wrapper' := (wrap tinfo winfo f_work' w_work f_wrap' w_wrap) in

      (~ f_work \in bound_var wrapper) ->
      (~ f_work' \in bound_var wrapper') ->
      (~ w_work \in Exposed) ->

      wrap_prop tinfo winfo f_work w_work f_wrap w_wrap ->

      forall i ρ ρ' v_work v_work' k k' v_wrap v_wrap',
        wf_env ρ ->
        wf_env ρ' ->

        bstep_fuel false (M.set f_work (Tag w_work v_work) ρ) wrapper k (Res (Tag w_wrap v_wrap)) ->
        bstep_fuel false (M.set f_work' (Tag w_work v_work') ρ') wrapper' k' (Res (Tag w_wrap v_wrap')) ->

        match i with
        | 0 =>
            V_refl0 v_wrap v_wrap'
        | S i0 =>
            V_refl (fun j => V (i0 - (i0 - j))) (fun j => E false (i0 - (i0 - j))) i0 w_work v_work v_work' ->
            V_refl (fun j => V (i0 - (i0 - j))) (fun j => E false (i0 - (i0 - j))) i0 w_wrap v_wrap v_wrap'
        end.

End SemSubstSig.

Module SemSubstExposed (WM : WrapSig) (SS : SemSubstSig WM).

  Import WM.
  Export SS SS.SV.

  Lemma V_wrapper_refl' tinfo winfo f_work f_work' w_work f_wrap f_wrap' w_wrap :
    let wrapper := (wrap tinfo winfo f_work w_work f_wrap w_wrap) in
    let wrapper' := (wrap tinfo winfo f_work' w_work f_wrap' w_wrap) in

    (~ f_work \in bound_var wrapper) ->
    (~ f_work' \in bound_var wrapper') ->

    L ! w_work = None ->
    (~ w_work \in Exposed) ->

    wrap_prop tinfo winfo f_work w_work f_wrap w_wrap ->

    forall i ρ ρ' v_work v_work' k k' v_wrap v_wrap',
      wf_env ρ ->
      wf_env ρ' ->

      bstep_fuel false (M.set f_work (Tag w_work v_work) ρ) wrapper k (Res (Tag w_wrap v_wrap)) ->
      bstep_fuel false (M.set f_work' (Tag w_work v_work') ρ') wrapper' k' (Res (Tag w_wrap v_wrap')) ->

      V i (Tag w_work v_work) (Tag w_work v_work') ->

      match i with
      | 0 => V_refl0 v_wrap v_wrap'
      | S i0 => V_refl (fun j => V (i0 - (i0 - j))) (fun j => E false (i0 - (i0 - j))) i0 w_wrap v_wrap v_wrap'
      end.
  Proof.
    intros.
    subst wrapper.
    subst wrapper'.

    assert (match i with
            | 0 =>
                V_refl0 v_wrap v_wrap'
            | S i0 =>
                V_refl (fun j => V (i0 - (i0 - j))) (fun j => E false (i0 - (i0 - j))) i0 w_work v_work v_work' ->
                V_refl (fun j => V (i0 - (i0 - j))) (fun j => E false (i0 - (i0 - j))) i0 w_wrap v_wrap v_wrap'
            end).
    {
      eapply V_wrapper_refl with (k := k) (k' := k')
                                 (f_work := f_work) (f_work' := f_work')
                                 (ρ := ρ) (ρ' := ρ')
                                 (v_wrap := v_wrap) (v_wrap' := v_wrap')
                                 (v_work := v_work) (v_work' := v_work'); eauto.
    }

    destruct i; auto.
    apply H9.
    simpl in H8.
    rewrite H1 in H8.
    destruct H8 as [Hv1 [Hv2 [_ HV]]].
    destruct (exposed_reflect w_work); try contradiction; auto.
  Qed.

  Module WU := WrapUtils WM.
  Export WU.

  Lemma V_wrapper tinfo winfo f_work w_work f_wrap w_wrap k i v_work v_work' ρ wv_wrap :
    L ! w_wrap = Some (tinfo, winfo, w_work) ->
    let wrapper := (wrap tinfo winfo f_work w_work f_wrap w_wrap) in

    (~ f_work \in bound_var wrapper) ->
    L ! w_work = None ->
    (~ w_work \in Exposed) ->
    V i (Tag w_work v_work') (Tag w_work v_work) ->

    wrap_prop tinfo winfo f_work w_work f_wrap w_wrap ->

    wf_env ρ ->
    bstep_fuel false (M.set f_work (Tag w_work v_work') ρ) wrapper k (Res wv_wrap) ->

    V i wv_wrap (Tag w_work v_work).
  Proof.
    intros Hw_wrap Hwrapper Hf_work Hw_work Hw_work1 HVv_work Hwrap_prop Hρ Hk.
    subst Hwrapper.

    edestruct (bstep_fuel_wrap_inv Hf_work Hk) as [ρ' [xs [e Heqv_wrap]]]; eauto; subst.
    pose proof HVv_work as HVv_work'.

    destruct i; simpl in HVv_work; simpl;
      rewrite Hw_work in *;
      destruct HVv_work as [Hv_work [Hv_work' [_ HVv_work]]];
      assert (Hwv_wrap : wf_res (Res (Tag w_wrap (Vfun f_wrap ρ' xs e)))) by (eapply (bstep_fuel_wf_res (M.set f_work (Tag w_work v_work') ρ)); eauto;
                                                                              eapply wf_env_set; eauto;
                                                                              inv H; auto);
      inv Hwv_wrap;
      repeat (split; auto);
      rewrite Hw_wrap; auto.

    unfold V_trans.
    repeat (split; auto); intros.
    edestruct (bstep_fuel_wf_wrap tinfo winfo f_work0 w_work f_wrap0 w_wrap (Tag w_work v_work) ρ0) as [k' [ρ'' [xs' [e' Hstep]]]]; eauto.

    eapply V_wrapper_refl' with (k := k) (k' := k')
                                (f_work := f_work) (f_work' := f_work0)
                                (ρ := ρ) (ρ' := ρ0)
                                (v_work := v_work') (v_work' := v_work)
      in HVv_work'; eauto.
    unfold V_refl in HVv_work'.
    destruct HVv_work' as [Hlenxs HVv_work'].
    eexists; eexists; eexists; eexists; repeat (split; eauto); intros.

    eapply (HVv_work' j vs1 vs2 ρ3 ρ4); eauto;
      intros;
      apply L_inv_Some in Hw_wrap; contradiction.
  Qed.

  Lemma V_worker_refl {Γ2 xs Γ1 e e' f_temp w_temp f_wrap w_wrap f_work w_work tinfo winfo} :
    let wrapper := (wrap tinfo winfo f_work w_work f_wrap w_wrap) in
    trans_correct (FromList xs :|: (f_work |: Γ1)) e e' ->

    (* worker spec *)
    L ! w_work = None ->
    (~ w_work \in Exposed) ->
    (~ f_work \in bound_var wrapper) ->
    (~ In f_work xs) ->

    (* temp binder spec *)
    L ! w_temp = None ->
    (~ w_temp \in Exposed) ->
    (~ f_temp \in (occurs_free e)) ->
    (~ f_temp \in Γ1) ->
    f_temp <> f_work ->
    (~ In f_temp xs) ->

    (* wrapper spec *)
    L ! w_wrap = Some (tinfo, winfo, w_work) ->
    wrap_prop tinfo winfo f_work w_work f_wrap w_wrap ->

    forall i ρ1 ρ2,
      G i Γ1 ρ1 Γ2 ρ2 ->
      occurs_free e' \subset (FromList xs :|: (f_work |: Γ2)) ->

      V i (Tag w_work
             (Vfun f_work ρ1 xs
                (Efun f_temp w_temp [] wrapper
                   (Eletapp f_work f_temp w_temp [] e))))
        (Tag w_work (Vfun f_work ρ2 xs e')).
  Proof.
    unfold trans_correct.
    intros He Hw_work Hw_work1 Hf_work Hf_work1 Hw_temp Hw_temp1 Hf_temp Hf_temp1 Hf_temp2 Hf_temp3 Hw_wrap Hwrap_prop i; subst.

    induction i; simpl; intros ρ1 ρ2 HG HS;
      assert (wf_env ρ1) by (eapply G_wf_env_l; eauto);
      assert (wf_env ρ2) by (eapply G_wf_env_r; eauto);
      repeat (split; auto);
      rewrite Hw_work;
      repeat (split; auto); intros.
    unfold E, E' in *.
    intros.
    inv H8.
    exists 0, OOT; split; simpl; auto.
    inv H9.

    inv H17.
    exists 0, OOT; split; simpl; auto.
    inv H8.
    2 : { exists 0, OOT; split; simpl; auto. }

    simpl in *.
    inv H17.
    rewrite M.gss in *.
    inv H16; simpl in *.
    inv H20.

    destruct (exposed_reflect w_work); try contradiction.
    destruct (exposed_reflect w_temp); try contradiction.
    rename f' into f_temp.
    rename ρ' into ρ3.

    pose proof H5 as Hρ3.

    eapply (set_lists_set f_work v) in Hρ3; eauto.
    erewrite set_set_eq in Hρ3; eauto.

    eapply (set_lists_set f_temp
              (Tag w_temp
                 (Vfun f_temp ρ3 []
                    (wrap tinfo winfo f_work w_work f_wrap w_wrap)))) in Hρ3; eauto.
    rewrite (set_set f_temp f_work) in Hρ3; eauto.
    rewrite (set_set f_temp f_work) in Hρ3; eauto.

    unfold wval in *.
    remember (M.set f_work v
                (M.set f_temp
                   (Tag w_temp
                      (Vfun f_temp ρ3 []
                         (wrap tinfo winfo f_work w_work f_wrap w_wrap))) ρ3)) as ρ3'.

    assert (Hwfρ3 : wf_env ρ3).
    {
      eapply (wf_env_set_lists
                (M.set f_work
                   (Tag w_work
                      (Vfun f_work ρ1 xs
                         (Efun f_temp w_temp []
                            (wrap tinfo winfo f_work w_work f_wrap w_wrap)
                            (Eletapp f_work f_temp w_temp [] e)))) ρ1)) with (xs := xs) (vs := vs1); eauto.
      eapply wf_env_set; eauto.
      eapply V_wf_val_Forall_l; eauto.
    }

    assert (Hwfρ3' : wf_env ρ3').
    {
      eapply (wf_env_set_lists
                (M.set f_work v
                   (M.set f_temp
                      (Tag w_temp
                         (Vfun f_temp ρ3 []
                            (wrap tinfo winfo f_work w_work f_wrap w_wrap))) ρ1))) with (xs := xs) (vs := vs1); eauto.
      eapply wf_env_set; eauto.
      eapply wf_env_set; eauto.
      eapply bstep_fuel_wf_res in H21; eauto.
      inv H21; auto.
      eapply wf_env_set; eauto.
      eapply V_wf_val_Forall_l; eauto.
    }

    assert (Hmath : (i - (i - j) - (S (S (c + c')))) = (((i - (i - j) - 2 - c) - c'))) by lia.
    rewrite Hmath; clear Hmath.

    eapply (He false ((i - (i - j) - 2 - c)) ρ3' ρ4) with (j1 := c'); eauto; try lia.
    eapply G_subset with (Γ1 := (FromList xs :|: (f_work |: Γ1))) (Γ2 := (FromList xs :|: (f_work |: Γ2))); eauto.
    eapply G_set_lists with (xs := xs) (vs1 := vs1) (vs2 := vs2); eauto.
    eapply G_set; eauto.
    - unfold G.
      split.
      eapply wf_env_set; eauto.

      split; auto; intros.
      destruct (var_dec f_temp x); subst; try contradiction.
      rewrite M.gso in *; auto.
      edestruct (G_get HG) as [v2 [Heqv2 HV]]; eauto.
      eexists; split; eauto.
      eapply V_mono; eauto; lia.
    - edestruct (set_lists_set_inv H5) as [ρ1' [Heqρ1' Heqρ3'']]; eauto.
      subst ρ3.
      erewrite set_set in H21; eauto.
      eapply V_wrapper with (k := c)
                            (v_work' := (Vfun f_work ρ1 xs
                                           (Efun f_temp w_temp []
                                              (wrap tinfo winfo f_work w_work f_wrap w_wrap)
                                              (Eletapp f_work f_temp w_temp [] e))))
                            (ρ := (M.set f_temp
                                     (Tag w_temp
                                        (Vfun f_temp
                                           (map_util.M.set f_work
                                              (Tag w_work
                                                 (Vfun f_work ρ1 xs
                                                    (Efun f_temp w_temp []
                                                       (wrap tinfo winfo f_work w_work f_wrap
                                                          w_wrap)
                                                       (Eletapp f_work f_temp w_temp []
                                                          e)))) ρ1') []
                                           (wrap tinfo winfo f_work w_work f_wrap w_wrap)))
                                     ρ1')); eauto.
      + eapply V_mono with i; eauto; try lia.
        eapply IHi; eauto.
        eapply G_mono; eauto; try lia.
      + eapply wf_env_set; eauto.
        eapply (wf_env_set_lists ρ1) with (xs := xs) (vs := vs1); eauto.
        eapply V_wf_val_Forall_l; eauto.
    - eapply V_mono_Forall; eauto; try lia.
    - apply Included_refl.
  Qed.

  Lemma fun_compat_trans Γ1 e e' tinfo k k' f w xs w_temp f_temp w_wrap f_wrap winfo :
    let wrapper := (wrap tinfo winfo f w f_wrap w_wrap) in
    trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
    occurs_free e' \subset occurs_free e ->

    trans_correct (f |: Γ1) k k' ->
    occurs_free k' \subset occurs_free k ->

    (* worker spec *)
    M.get w L = None ->
    (~ w \in Exposed) ->
    (~ In f xs) ->
    (~ f \in bound_var wrapper) ->

    (* temp binder spec *)
    L ! w_temp = None ->
    (~ w_temp \in Exposed) ->
    (~ f_temp \in (occurs_free e)) ->
    (~ f_temp \in (occurs_free k)) ->
    (~ f_temp \in Γ1) ->
    f_temp <> f ->
    (~ In f_temp xs) ->

    (* wrapper spec *)
    L ! w_wrap = Some (tinfo, winfo, w) ->
    wrap_prop tinfo winfo f w f_wrap w_wrap ->

    trans_correct Γ1 (Efun f w xs
                        (Efun f_temp w_temp [] wrapper
                           (Eletapp f f_temp w_temp [] e))
                        (Efun f_temp w_temp [] wrapper
                           (Eletapp f f_temp w_temp [] k)))
      (Efun f w xs e' k').
  Proof.
    unfold trans_correct, E, E'.
    intros He Hes Hk Hks Hw Hw1 Hf Hf_bv Hw_temp Hw_temp1 Hf_temp Hf_temp1 Hf_temp2 Hf_temp3 Hf_temp4 Hw_wrap Hwrap_prop.

    intros.
    inv H1.
    exists 0, OOT; split; simpl; eauto.
    inv H2.

    inv H10.
    exists 0, OOT; split; simpl; eauto.
    inv H1.

    inv H11.
    exists 0, OOT; split; simpl; eauto.
    inv H1.
    2 : { exists 0, OOT; split; simpl; eauto. }

    simpl in *.
    rewrite M.gss in *; auto.
    inv H10; inv H11; simpl in *.
    inv H14.

    rename f' into f_temp.
    erewrite (set_set f_temp f) in H17; eauto.
    erewrite set_set_eq in H17; eauto.

    edestruct (Hk ex (i - 1)
                 (M.set f v
                    (M.set f_temp
                       (Tag w_temp
                          (Vfun f_temp
                             (M.set f
                                (Tag w
                                   (Vfun f ρ1 xs
                                      (Efun f_temp w_temp []
                                         (wrap tinfo winfo f w f_wrap w_wrap)
                                         (Eletapp f f_temp w_temp [] e))))
                                ρ1) [] (wrap tinfo winfo f w f_wrap w_wrap))) ρ1)) (M.set f (Tag w (Vfun f ρ2 xs e')) ρ2)) with (j1 := c') (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
    - assert (wf_env ρ1) by (eapply G_wf_env_l; eauto).
      assert (wf_env ρ2) by (eapply G_wf_env_r; eauto).
      assert (wf_env (M.set f_temp
                        (Tag w_temp
                           (Vfun f_temp
                              (M.set f
                                 (Tag w
                                    (Vfun f ρ1 xs
                                       (Efun f_temp w_temp []
                                          (wrap tinfo winfo f w f_wrap w_wrap)
                                          (Eletapp f f_temp w_temp [] e)))) ρ1)
                              [] (wrap tinfo winfo f w f_wrap w_wrap))) ρ1)).
      {
        eapply wf_env_set; eauto.
        constructor; auto.
        constructor; auto.
        eapply wf_env_set; eauto.
      }

      eapply G_subset with (Γ1 := (f |: (f_temp |: Γ1))) (Γ2 := (f |: (occurs_free (Efun f w xs e' k')))); eauto.
      eapply G_set; eauto.
      + unfold G.
        repeat (split; auto); intros.
        destruct (var_dec f_temp x); subst.
        * rewrite M.gss in *.
          inv H8.
          inv H9.
          -- exfalso.
             apply Hf_temp1; auto.
          -- exfalso.
             apply Hf_temp; auto.
        * rewrite M.gso in *; auto.
          eapply (@G_get Γ1 (occurs_free (Efun f w xs e' k'))); eauto.
          eapply G_mono; eauto; lia.
          inv H7; auto.
          inv H10; contradiction.
      + erewrite set_set in H15; eauto.
        destruct (exposed_reflect w_temp); try contradiction.
        eapply V_wrapper; eauto.
        eapply V_worker_refl; eauto.
        eapply G_mono; eauto; try lia.
        eapply free_fun_e_subset; eauto.
      + eapply Included_Union_compat; eauto.
        apply Included_refl.
        apply Included_Union_r; auto.
      + apply free_fun_k_subset; auto.
    - exists (S j2), r2; split; auto.
      + constructor; auto.
        destruct ex; auto.
        eapply R_exposed; eauto.
      + apply R_mono with ((i - 1) - c'); try lia; auto.
  Qed.

  Lemma free_wrap_xs_subset xs wrapper f_temp w_temp w_wrap :
    (~ In f_temp xs) ->
    FromList xs \subset
      occurs_free
      (Efun f_temp w_temp [] wrapper
         (Eletapp f_temp f_temp w_temp []
            (Eapp f_temp w_wrap xs))).
  Proof.
    unfold Ensembles.Included, Ensembles.In, FromList.
    intros.
    eapply Free_fun1; eauto.
    intros Hc; subst; contradiction.
    eapply Free_letapp1; eauto.
    intros Hc; subst; contradiction.
  Qed.

  Lemma app_compat_trans Γ tinfo f w xs w_temp f_temp w_wrap f_wrap winfo :
    let wrapper := (wrap tinfo winfo f w f_wrap w_wrap) in

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
    L ! w_wrap = Some (tinfo, winfo, w) ->
    (* wrap_prop tinfo winfo f w f_wrap w_wrap -> *)

    trans_correct Γ (Eapp f w_wrap xs)
      (Efun f_temp w_temp [] wrapper
         (Eletapp f_temp f_temp w_temp [] (* turn the worker into the wrapper *)
            (Eapp f_temp w_wrap xs))).
  Proof.
    unfold trans_correct, E, E'.
    intros Hf Hxs Hw Hw1 Hf_bv Hw_temp Hw_temp1 Hf_temp Hf_temp2 Hw_wrap.

    intros.
    inv H1.
    exists 0, OOT; split; simpl; auto.

    inv H2.
    edestruct (G_get H) as [fv2 [Heqfv2 HVfv]]; eauto.
    eapply Free_fun2; eauto.
    eapply free_vars_wrap; eauto.

    destruct fv2.
    destruct i.
    inv H0.
    simpl in HVfv.
    destruct HVfv as [Hfv1 [Hfv2 HV]]; subst.
    rewrite Hw_wrap in HV.
    unfold VTransM.V_trans in HV.
    destruct HV as [Heqw HV]; subst.

    assert (wf_env ρ1) by (eapply G_wf_env_l; eauto).
    assert (wf_env ρ2) by (eapply G_wf_env_r; eauto).

    destruct (HV f f_wrap (M.set f_temp
                             (Tag w_temp
                                (Vfun f_temp ρ2 [] (wrap tinfo winfo f w0 f_wrap w_wrap))) ρ2)) as [k [ρ3 [xs2 [e2 [Hstep [Hlen HV']]]]]]; eauto.
    eapply wf_env_set; eauto.

    erewrite set_set in Hstep; eauto.
    rewrite (get_set_eq f) in Hstep.

    edestruct (G_get_list H xs) as [vs2 [Heqvs2 HVvs]]; eauto.
    eapply free_wrap_xs_subset; eauto.

    destruct (set_lists_length3 (M.set f_wrap (Tag w_wrap (Vfun f_wrap ρ3 xs2 e2)) ρ3) xs2 vs2) as [ρ4 Heqρ4].
    unfold var in *.
    rewrite <- Hlen.
    rewrite (set_lists_length_eq _ _ _ _ H8); auto.
    apply (Forall2_length _ _ _ HVvs).

    assert (HE : E false (i - (i - i)) ρ'' e ρ4 e2).
    {
      eapply (HV' i vs vs2); eauto.
      eapply V_wf_val_Forall_l; eauto.
      apply V_mono_Forall with (S i); auto; lia.
    }

    unfold E, E' in *.
    destruct (exposed_reflect w_wrap).
    apply L_inv_Some in Hw_wrap; try contradiction.
    edestruct (HE c r1) as [j2 [r2 [He HR]]]; eauto; try lia.

    rewrite normalize_step in *; try lia.
    assert (Hmath : S i - S c = i - c) by lia.
    rewrite Hmath; clear Hmath.

    assert (if ex then exposed_res r2 else True).
    {
      destruct ex; auto.
      eapply R_exposed; eauto.
    }

    destruct r1.
    exists 0, OOT; split; simpl; eauto.

    exists (S (S (S (k + j2)))), r2; split; eauto.

    constructor; auto.
    2 : { unfold wval in *.
          rewrite Heqfv2; auto. }

    constructor; auto.
    constructor; auto.
    assert (Hmath : (S (k + j2)) = k + (S j2)) by lia.
    rewrite Hmath; clear Hmath.

    eapply BStep_letapp_Res with (v := (Tag w_wrap (Vfun f_wrap ρ3 xs2 e2))); simpl; eauto.
    - rewrite M.gss; eauto.
    - simpl; eauto.
    - destruct (exposed_reflect w_temp); try contradiction; auto.
    - intros; contradiction.
    - erewrite set_set_eq; eauto.
      constructor; auto.
      econstructor; eauto.
      + rewrite M.gss; auto.
      + rewrite get_list_set_neq; auto.
      + destruct (exposed_reflect w_wrap); auto.
        apply L_inv_Some in Hw_wrap; contradiction.
      + intros; contradiction.
  Qed.

End SemSubstExposed.

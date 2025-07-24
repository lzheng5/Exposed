From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF Exposed.

(* Semantic Substitution for DPE *)

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

(* Map from web identifier to transformation specific information and worker web *)
Definition trans_info_t := list bool.

Module LT <: Exposed.LTy. Definition t : Type := (trans_info_t * web). End LT.
Module LM := Exposed.DefaultL LT.
Export LM.

Definition wrapper_info_t := list var.

(* Apply bit mask to argument list *)
Fixpoint live_args {A} (ys : list A) (bs : list bool) : list A :=
  match bs, ys with
  | [], [] => ys
  | b :: bs', y :: ys' =>
    if b then y :: (live_args ys' bs')
    else live_args ys' bs'
  | _, _ => ys
  end.

(* Lemmas about [live_args] *)
Lemma live_args_incl {A xs bs} :
  incl (@live_args A xs bs) xs.
Proof.
  revert bs.
  induction xs; intros.
  - destruct bs; simpl; apply incl_nil_l.
  - destruct bs; simpl.
    + apply incl_refl.
    + destruct b.
      * apply incl_cons.
        apply in_eq; auto.
        apply incl_tl; auto.
      * apply incl_tl; auto.
Qed.

Lemma live_args_In : forall {A xs bs a}, In a (@live_args A xs bs) -> In a xs.
Proof.
  intros; eapply live_args_incl; eauto.
Qed.

Lemma live_args_not_In : forall {A xs a} bs, ~ In a xs -> ~ In a (@live_args A xs bs).
Proof.
  intros.
  intro Hc.
  apply H.
  eapply live_args_In; eauto.
Qed.

Lemma live_args_length {A B} xs ys bs :
  length xs = length ys ->
  length (@live_args A xs bs) = length (@live_args B ys bs).
Proof.
  revert ys bs. induction xs; intros; eauto.
  - destruct ys; try (simpl in * ; congruence).
    destruct bs; reflexivity.
  - simpl.
    destruct ys; try (simpl in * ; congruence). inv H.
    destruct bs. simpl. congruence.
    destruct b0; simpl; eauto.
Qed.

Definition wrap
  (bs : trans_info_t) (ys : wrapper_info_t)
  (f_work : var) (w_work : web)
  (f_wrap : var) (w_wrap : web) : exp :=
  (Efun f_wrap w_wrap ys (Eapp f_work w_work (live_args ys bs))
     (Eret f_wrap)).

Lemma free_vars_wrap_inv tinfo winfo w_work f_wrap w_wrap f:
  let wrapper := (wrap tinfo winfo f w_work f_wrap w_wrap) in
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

Lemma bstep_fuel_wrap_inv bs ys f_work w_work f_wrap w_wrap v_work ρ:
  let wrapper := (wrap bs ys f_work w_work f_wrap w_wrap) in
  exists k v_wrap,
    bstep_fuel false (M.set f_work v_work ρ) wrapper k (Res v_wrap).
Proof.
  unfold wrap.
  exists 2, (Tag w_wrap (Vfun f_wrap (M.set f_work v_work ρ) ys (Eapp f_work w_work (live_args ys bs)))).
  repeat (constructor; auto).
  rewrite M.gss; auto.
Qed.

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

    (* temp binder spec *)
    L ! w_temp = None ->
    (~ w_temp \in Exposed) ->
    (~ f_temp \in (occurs_free e)) ->
    (~ f_temp \in (occurs_free k)) ->
    (~ f_temp \in Γ) ->
    f_temp <> f ->
    (~ In f_temp ys) ->

    (* wrapper spec *)
    L ! w_wrap = Some (bs, w) ->
    (* TODO: wrap_prop bs ys ... *)
    length bs = length ys ->
    (~ In f_wrap ys) ->
    NoDup ys ->

    (* worker wrapper spec *)
    (~ f \in bound_var wrapper) ->
    xs = live_args ys bs ->

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

    (* temp binder spec *)
    L ! w_temp = None ->
    (~ w_temp \in Exposed) ->
    f_temp <> f ->
    (~ In f_temp xs) ->

    (* wrapper spec *)
    L ! w_wrap = Some (bs, w) ->
    (~ f \in bound_var wrapper) ->
    (~ In f_wrap ys) ->
    NoDup ys ->
    length ys = length bs ->

    trans Γ (Eapp f w_wrap xs)
      (Efun f_temp w_temp [] wrapper
         (Eletapp f_temp f_temp w_temp [] (* turn the worker into the wrapper *)
            (Eapp f_temp w_wrap xs))).

Hint Constructors trans : core.

(* Logical Relations *)
Module VTransM <: Exposed.VTrans LM.

  (* Relating wrapper and worker *)
  Definition V_trans
    (V' : nat -> wval -> wval -> Prop)
    (E' : nat -> env -> exp -> env -> exp -> Prop)
    (i0 : nat) (d : list bool * web)
    (w1 : web) (v1 : val) (w2 : web) (v2 : val) :=
    let (bs, w) := d in
    w2 = w /\
    match v1, v2 with
    | Vfun f1 ρ1 xs1 e1, Vfun f2 ρ2 xs2 e2 =>
        length xs1 = length bs /\
        xs2 = live_args xs1 bs /\

        forall j vs1 vs2 ρ3 ρ4,
          j <= i0 ->
          Forall wf_val vs1 ->
          Forall2 (V' j) (live_args vs1 bs) vs2 ->
          set_lists xs1 vs1 (M.set f1 (Tag w1 (Vfun f1 ρ1 xs1 e1)) ρ1) = Some ρ3 ->
          set_lists xs2 vs2 (M.set f2 (Tag w2 (Vfun f2 ρ2 xs2 e2)) ρ2) = Some ρ4 ->
          E' j ρ3 e1 ρ4 e2

    | _, _ => False
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
    destruct v1; destruct v2; auto;
      simpl in *; try contradiction;
      rename l into xs1;
      rename l0 into xs2.
    unfold V_trans in *.
    destruct d.
    destruct H as [Hw [Hlen [Heq HV]]]; subst.
    repeat split; eauto; intros.
    specialize (HV j0 vs1 vs2 ρ3 ρ4).
    rewrite normalize_step in *; try lia.
    eapply HV; eauto; try lia.
  Qed.

End VTransM.

Import VTransM ExposedUtil.

Module EM := Exposed.Exposed LM VTransM.
Import EM.

(* Addtional Lemmas about [live_args] *)
Lemma get_list_live_args_set_lists {A} :
  forall ys bs vs1 vs0 ρ0 ρ0' ρ1 ρ2,
    NoDup ys ->
    length ys = length bs ->
    @get_list A (live_args ys bs) ρ1 = Some vs1 ->
    set_lists ys vs0 ρ0 = Some ρ1 ->
    set_lists ys vs0 ρ0' = Some ρ2 ->
    get_list (live_args ys bs) ρ2 = Some vs1.
Proof.
  intros ys.
  induction ys; simpl; intros.
  - destruct bs; inv H0.
    simpl in *.
    inv H1; auto.
  - destruct bs; inv H0.
    destruct vs0; try discriminate.
    destruct (set_lists ys vs0 ρ0) eqn:Heq1; try discriminate.
    destruct (set_lists ys vs0 ρ0') eqn:Heq2; try discriminate.
    inv H; inv H2; inv H3.
    assert (~ In a (live_args ys bs)) by (eapply live_args_not_In; eauto).

    destruct b; simpl in *.
    + rewrite M.gss in *.
      destruct (get_list (live_args ys bs) (map_util.M.set a a0 t)) eqn:Heq3; try discriminate.
      inv H1.
      erewrite get_list_set_neq in Heq3; eauto.
      erewrite get_list_set_neq; eauto.
      erewrite IHys; eauto.
    + erewrite get_list_set_neq in H1; eauto.
      erewrite get_list_set_neq; eauto.
Qed.

Lemma get_list_live_args_Forall :
  forall {ys vs1 ρ0 ρ1 vs2 vs bs i},
    NoDup ys ->
    length ys = length bs ->
    set_lists ys vs1 ρ0 = Some ρ1 ->
    get_list (live_args ys bs) ρ1 = Some vs ->
    Forall2 (V i) (live_args vs1 bs) vs2 ->
    Forall2 (V i) vs vs2.
Proof.
  intros ys.
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
    + erewrite get_list_set_neq in H2; eauto.
Qed.

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

Lemma Forall2_live_args i xs ys:
  Forall2 (V i) xs ys ->
  forall bs,
    length xs = length bs ->
    Forall2 (V i) (live_args xs bs) (live_args ys bs).
Proof.
  intros H.
  induction H; simpl; intros.
  - destruct bs; inv H; auto.
  - destruct bs; inv H1.
    destruct b; auto.
Qed.

(* Invariants about [trans] *)
Lemma trans_exp_inv {Γ e e'} :
  trans Γ e e' ->
  (occurs_free e') \subset (occurs_free e).
Proof.
  unfold Ensembles.Included, Ensembles.In.
  intros H.
  induction H; intros; subst; auto.
  - inv H16.
    + eapply IHtrans2 in H23; eauto.
      econstructor; eauto.
      econstructor; eauto.
      intros Hc; subst.
      apply H6; auto.
    + eapply IHtrans1 in H24; eauto.
      eapply Free_fun2; eauto.
      eapply Free_fun1; eauto.
      intros Hc; subst.
      apply H5; auto.
  - inv H12.
    + inv H20; try contradiction.
      inv H21; auto; contradiction.
    + inv H21; auto.
      * inv H22; contradiction.
      * inv H23; auto.
        exfalso.
        apply H22.
        eapply live_args_In; eauto.
Qed.

(* Compatibility Lemmas *)
Lemma V_wrapper :
  forall tinfo winfo f_work w_work f_wrap w_wrap k i v_work v_work' ρ wv_wrap,
    L ! w_wrap = Some (tinfo, w_work) ->
    let wrapper := (wrap tinfo winfo f_work w_work f_wrap w_wrap) in

    (~ f_work \in bound_var wrapper) ->
    L ! w_work = None ->
    (~ w_work \in Exposed) ->
    V i (Tag w_work v_work') (Tag w_work v_work) ->

    wf_env ρ ->
    bstep_fuel false (M.set f_work (Tag w_work v_work') ρ) wrapper k (Res wv_wrap) ->

    (* TODO: refactor DPE specfic information *)
    length winfo = length tinfo ->
    NoDup winfo ->
    (exists ρ' e', v_work = Vfun f_work ρ' (live_args winfo tinfo) e') ->

    V i wv_wrap (Tag w_work v_work).
Proof.
  unfold wrap.
  intros tinfo winfo f_work w_work f_wrap w_wrap k i v_work v_work' ρ wv_wrap.
  intros Hw_wrap Hf_work Hw_work Hw_work1 Hv_work Hρ Hk Hlen Hn [ρ' [e Heqv_work]].

  destruct i; simpl in *;
    rewrite Hw_work in *;
    destruct Hv_work as [Hv_work [Hv_work' [_ HVv_work]]];
    assert (Hwv_wrap : wf_res (Res wv_wrap)) by (eapply (bstep_fuel_wf_res (M.set f_work (Tag w_work v_work') ρ)); eauto;
                                                 eapply wf_env_set; eauto;
                                                 inv H; auto);
    inv Hwv_wrap;
    repeat (split; auto).
  - inv Hk.
    inv H.
    inv H9.
    inv H.
    rewrite M.gss in *.
    inv H6; simpl.
    rewrite Hw_wrap; auto.
  - inv Hk.
    inv H.
    inv H9.
    inv H.
    rewrite M.gss in *.
    inv H6; simpl.
    rewrite Hw_wrap; auto.
    destruct v_work'; try contradiction.
    unfold V_trans, V_refl in *.
    repeat (split; auto); intros.
    destruct HVv_work as [Hlen' HVv_work].
    unfold E' in *.
    intros.
    inv H8.
    exists 0, OOT; split; simpl; auto.
    inv H9.
    erewrite <- (set_lists_not_In _ _ _ _ f_work H5) in H13; eauto.
    rewrite M.gso in *; auto.
    2 : { intros Hc; subst.
          apply Hf_work; auto. }

    rewrite M.gss in *.
    inv H13.
    destruct (exposed_reflect w_work); try contradiction.
    edestruct (HVv_work j vs vs2 ρ'' ρ4) with (j1 := c) as [j2 [r2 [He HR]]]; eauto; try lia.
    + intros; contradiction.
    + intros; contradiction.
    + eapply get_list_live_args_Forall; eauto.
    + exists j2, r2; split; eauto.
      eapply R_mono; eauto; lia.
Qed.

Lemma V_worker {Γ2 xs Γ1 e e' f_temp w_temp f_wrap w_wrap f_work w_work bs ys} :
  let wrapper := (wrap bs ys f_work w_work f_wrap w_wrap) in
  trans_correct (FromList xs :|: (f_work |: Γ1)) e e' ->

  (* worker spec *)
  L ! w_work = None ->
  (~ w_work \in Exposed) ->
  (~ f_work \in bound_var wrapper) ->

  (* temp binder spec *)
  L ! w_temp = None ->
  (~ w_temp \in Exposed) ->
  (~ f_temp \in (occurs_free e)) ->
  (~ f_temp \in Γ1) ->
  f_temp <> f_work ->
  (~ In f_temp ys) ->

  (* wrapper spec *)
  L ! w_wrap = Some (bs, w_work) ->
  (~ In f_wrap ys) ->
  NoDup ys ->
  length ys = length bs ->

  (* worker wrapper spec *)
  xs = live_args ys bs ->
  (~ f_work \in bound_var wrapper) ->

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
  intros He Hw_work Hw_work1 Hf_work Hw_temp Hw_temp1 Hf_temp Hf_temp1 Hf_temp2 Hf_temp3 Hw_wrap Hf_wrap1 Hnys Hlenys Heqxs Hf_work1 i; subst.
  edestruct bound_vars_wrap_inv as [Hf_wrap Hf_work2]; eauto.

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

  assert (Hf_work3 : ~ In f_work (live_args ys bs)) by (eapply live_args_not_In; eauto).
  apply (set_lists_set f_work v Hf_work3) in Hρ3.
  erewrite set_set_eq in Hρ3; eauto.

  assert (Hf_temp4 : ~ In f_temp (live_args ys bs)) by (eapply live_args_not_In; eauto).
  apply (set_lists_set f_temp
           (Tag w_temp
              (Vfun f_temp ρ3 []
                 (wrap bs ys f_work w_work f_wrap w_wrap))) Hf_temp4) in Hρ3.
  rewrite (set_set f_temp f_work) in Hρ3; eauto.
  rewrite (set_set f_temp f_work) in Hρ3; eauto.

  unfold wval in *.
  remember (M.set f_work v
             (M.set f_temp
                (Tag w_temp
                   (Vfun f_temp ρ3 []
                      (wrap bs ys f_work w_work f_wrap w_wrap))) ρ3)) as ρ3'.

  assert (Hwfρ3 : wf_env ρ3).
  {
    eapply (wf_env_set_lists
              (M.set f_work
                 (Tag w_work
                    (Vfun f_work ρ1 (live_args ys bs)
                       (Efun f_temp w_temp []
                          (wrap bs ys f_work w_work f_wrap w_wrap)
                          (Eletapp f_work f_temp w_temp [] e)))) ρ1)) with (xs := live_args ys bs) (vs := vs1); eauto.
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
                          (wrap bs ys f_work w_work f_wrap w_wrap))) ρ1))) with (xs := live_args ys bs) (vs := vs1); eauto.
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
  eapply G_subset with (Γ1 := (FromList (live_args ys bs) :|: (f_work |: Γ1))) (Γ2 := (FromList (live_args ys bs) :|: (f_work |: Γ2))); eauto.
  eapply G_set_lists with (xs := (live_args ys bs)) (vs1 := vs1) (vs2 := vs2); eauto.
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
                          (v_work' := (Vfun f_work ρ1 (live_args ys bs)
                                         (Efun f_temp w_temp []
                                            (wrap bs ys f_work w_work f_wrap w_wrap)
                                            (Eletapp f_work f_temp w_temp [] e))))
                          (ρ := (M.set f_temp
                                   (Tag w_temp
                                      (Vfun f_temp
                                         (map_util.M.set f_work
                                            (Tag w_work
                                               (Vfun f_work ρ1
                                                  (live_args ys bs)
                                                  (Efun f_temp w_temp []
                                                     (wrap bs ys f_work w_work f_wrap
                                                        w_wrap)
                                                     (Eletapp f_work f_temp w_temp []
                                                        e)))) ρ1') []
                                         (wrap bs ys f_work w_work f_wrap w_wrap)))
                                   ρ1')); eauto.
    + eapply V_mono with i; eauto; try lia.
      eapply IHi; eauto.
      eapply G_mono; eauto; try lia.
    + eapply wf_env_set; eauto.
      eapply (wf_env_set_lists ρ1) with (xs := live_args ys bs) (vs := vs1); eauto.
      eapply V_wf_val_Forall_l; eauto.
  - eapply V_mono_Forall; eauto; try lia.
  - apply Included_refl.
Qed.

Lemma fun_compat_trans Γ1 e e' bs k k' f w xs w_temp f_temp w_wrap f_wrap ys :
  let wrapper := (wrap bs ys f w f_wrap w_wrap) in
  trans_correct (FromList xs :|: (f |: Γ1)) e e' ->
  occurs_free e' \subset occurs_free e ->

  trans_correct (f |: Γ1) k k' ->
  occurs_free k' \subset occurs_free k ->

  (* worker spec *)
  M.get w L = None ->
  (~ w \in Exposed) ->

  (* temp binder spec *)
  L ! w_temp = None ->
  (~ w_temp \in Exposed) ->
  (~ f_temp \in (occurs_free e)) ->
  (~ f_temp \in (occurs_free k)) ->
  (~ f_temp \in Γ1) ->
  f_temp <> f ->
  (~ In f_temp ys) ->

  (* wrapper spec *)
  L ! w_wrap = Some (bs, w) ->
  length bs = length ys ->
  (~ In f_wrap ys) ->
  NoDup ys ->

  (* worker wrapper spec *)
  xs = live_args ys bs ->
  (~ f \in bound_var wrapper) ->

  trans_correct Γ1 (Efun f w xs
                      (Efun f_temp w_temp [] wrapper
                         (Eletapp f f_temp w_temp [] e))
                      (Efun f_temp w_temp [] wrapper
                         (Eletapp f f_temp w_temp [] k)))
    (Efun f w xs e' k').
Proof.
  unfold trans_correct, E, E'.
  intros He Hes Hk Hks Hw Hw1 Hw_temp Hw_temp1 Hf_temp Hf_temp1 Hf_temp2 Hf_temp3 Hf_temp4 Hw_wrap Hbs Hf_wrap Hn Hxs Hf_bv.
  edestruct bound_vars_wrap_inv as [Hf_wrap1 Hf_ys]; eauto.

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
                                 (Vfun f ρ1 (live_args ys bs)
                                    (Efun f_temp w_temp []
                                       (wrap bs ys f w f_wrap w_wrap)
                                       (Eletapp f f_temp w_temp [] e))))
                              ρ1) [] (wrap bs ys f w f_wrap w_wrap))) ρ1)) (M.set f (Tag w (Vfun f ρ2 (live_args ys bs) e')) ρ2)) with (j1 := c') (r1 := r1) as [j2 [r2 [Hk2 Rr]]]; eauto; try lia.
  - assert (wf_env ρ1) by (eapply G_wf_env_l; eauto).
    assert (wf_env ρ2) by (eapply G_wf_env_r; eauto).
    assert (wf_env (M.set f_temp
                      (Tag w_temp
                         (Vfun f_temp
                            (M.set f
                               (Tag w
                                  (Vfun f ρ1 (live_args ys bs)
                                     (Efun f_temp w_temp []
                                        (wrap bs ys f w f_wrap w_wrap)
                                        (Eletapp f f_temp w_temp [] e)))) ρ1)
                            [] (wrap bs ys f w f_wrap w_wrap))) ρ1)).
    {
      eapply wf_env_set; eauto.
      constructor; auto.
      constructor; auto.
      eapply wf_env_set; eauto.
    }

    eapply G_subset with (Γ1 := (f |: (f_temp |: Γ1))) (Γ2 := (f |: (occurs_free (Efun f w (live_args ys bs) e' k')))); eauto.
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
        eapply (@G_get Γ1 (occurs_free (Efun f w (live_args ys bs) e' k'))); eauto.
        eapply G_mono; eauto; lia.
        inv H7; auto.
        inv H10; contradiction.
    + erewrite set_set in H15; eauto.
      destruct (exposed_reflect w_temp); try contradiction.
      eapply V_wrapper; eauto.
      eapply V_worker; eauto.
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

Lemma app_compat_trans Γ bs f w xs w_temp f_temp w_wrap f_wrap ys :
  let wrapper := (wrap bs ys f w f_wrap w_wrap) in

  (f \in Γ) ->
  (FromList xs \subset Γ) ->

  (* worker spec *)
  L ! w = None ->
  (~ w \in Exposed) ->

  (* temp binder spec *)
  L ! w_temp = None ->
  (~ w_temp \in Exposed) ->
  f_temp <> f ->
  (~ In f_temp xs) ->

  (* wrapper spec *)
  L ! w_wrap = Some (bs, w) ->
  (~ f \in bound_var wrapper) ->
  (~ In f_wrap ys) ->
  NoDup ys ->
  length ys = length bs ->

  trans_correct Γ (Eapp f w_wrap xs)
    (Efun f_temp w_temp [] wrapper
       (Eletapp f_temp f_temp w_temp [] (* turn the worker into the wrapper *)
          (Eapp f_temp w_wrap xs))).
Proof.
  unfold trans_correct, E, E'.
  intros Hf Hxs Hw Hw1 Hw_temp Hw_temp1 Hf_temp Hf_temp2 Hw_wrap Hf_bv Hf_wrap Hn Hlenys.
  edestruct bound_vars_wrap_inv as [Hf_wrap1 Hf_xs]; eauto.

  intros.
  inv H1.
  exists 0, OOT; split; simpl; auto.

  inv H2.
  edestruct (G_get H) as [fv2 [Heqfv2 HVfv]]; eauto.
  eapply Free_fun2; eauto.
  eapply free_vars_wrap_inv; eauto.

  destruct fv2.
  destruct i.
  inv H0.
  simpl in HVfv.
  destruct HVfv as [Hfv1 [Hfv2 HV]]; subst.
  rewrite Hw_wrap in HV.
  unfold VTransM.V_trans in HV.
  destruct HV as [Heqw HV]; subst.
  destruct v; try contradiction.
  destruct HV as [Hlen [Heqxs HV]]; subst; try discriminate.

  edestruct (G_get_list H xs) as [vs2 [Heqvs2 HVvs]]; eauto.
  eapply free_wrap_xs_subset; eauto.

  destruct (set_lists_length3 (M.set v (Tag w (Vfun v t (live_args xs' bs) e0)) t) (live_args xs' bs) (live_args vs2 bs)) as [ρ4 Heqρ4].
  unfold wval in *.
  apply live_args_length.
  rewrite <- (Forall2_length _ _ _ HVvs).
  rewrite <- (set_lists_length_eq _ _ _ _ H8); auto.

  assert (HE : E false (i - (i - i)) ρ'' e ρ4 e0).
  {
    eapply (HV i vs (live_args vs2 bs)); eauto.
    eapply wf_env_get_list; eauto.
    eapply G_wf_env_l; eauto.
    eapply Forall2_live_args; eauto.
    apply V_mono_Forall with (S i); auto; lia.
    rewrite <- Hlen.
    rewrite <- (set_lists_length_eq _ _ _ _ H8); auto.
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

  destruct r2.
  exists 0, OOT; split; simpl; eauto.

  assert (if (exposedb w_wrap) then exposed_res (Res w0) else True) by (destruct (exposed_reflect w_wrap); try contradiction; auto).

  exists (S (S (S (S (S (S j2)))))), (Res w0); split; eauto.

  constructor; auto.
  constructor; auto.
  constructor; auto.
  assert (Hmath : S (S (S (S j2))) = 2 + (S (S j2))) by lia.
  rewrite Hmath; clear Hmath.

  eapply BStep_letapp_Res with (v := (Tag w_wrap
                                        (Vfun f_wrap
                                           (M.set f_temp
                                              (Tag w_temp
                                                 (Vfun f_temp ρ2 []
                                                    (wrap bs ys f w f_wrap w_wrap))) ρ2) ys
                                           (Eapp f w (live_args ys bs))))); simpl; eauto.
  - rewrite M.gss; eauto.
  - simpl; eauto.
  - destruct (exposed_reflect w_temp); try contradiction.
    repeat (econstructor; eauto).
    rewrite M.gss; eauto.
  - intros; split; auto; try contradiction.
  - constructor; auto.
    edestruct (set_lists_length3
                 (M.set f_wrap
                    (Tag w_wrap
                       (Vfun f_wrap
                          (M.set f_temp
                             (Tag w_temp
                                (Vfun f_temp ρ2 []
                                   (wrap bs ys f w f_wrap w_wrap))) ρ2) ys
                          (Eapp f w (live_args ys bs))))
                    (M.set f_temp
                       (Tag w_temp
                          (Vfun f_temp ρ2 []
                             (wrap bs ys f w f_wrap w_wrap))) ρ2))
                 ys vs2) as [ρ4' Heqρ4']; eauto.
    unfold wval in *.
    erewrite <- (Forall2_length _ _ _ HVvs); eauto.
    rewrite <- (set_lists_length_eq _ _ _ _ H8).
    unfold var in Hlen.
    rewrite Hlen; auto.

    eapply BStep_app with (ρ' := (M.set f_temp
                                    (Tag w_temp
                                       (Vfun f_temp ρ2 []
                                          (wrap bs ys f w f_wrap w_wrap))) ρ2)); eauto.
    + rewrite M.gss; eauto.
    + erewrite get_list_set_neq; eauto.
      erewrite get_list_set_neq; eauto.
    + constructor; auto.
      econstructor; eauto.
      * erewrite <- (set_lists_not_In ys vs2 _ _ f Heqρ4'); eauto.
        rewrite M.gso; auto.
        rewrite M.gso; eauto.
      * eapply get_list_live_args; eauto.
        eapply get_list_set_lists; eauto.
      * destruct (exposed_reflect w); try contradiction; auto.
      * intros; contradiction.
    + intros; contradiction.
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

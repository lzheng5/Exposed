From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF Exposed.

(* Defunc

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

(* Map f_wrap to the corresponding constructor *)
Definition trans_info_t := M.t ctor_tag.

Definition wrapper_info_t := unit.

Module LT <: Exposed.LTy. Definition t : Type := (trans_info_t * wrapper_info_t * web). End LT.
Module LM := Exposed.DefaultL LT.
Export LM.

Definition tail_cases (cs : list (var * ctor_tag)) f_work w_work :=
  List.map (fun (p : var * ctor_tag) =>
              let (c, f_wrap) := p in
              (c, Eproj f_wrap w_work 0 f_work (* project out the function *)
                    (Eret f_wrap))) (* ret it *)
    cs.

Definition wrap
  (C : trans_info_t) (_ : wrapper_info_t)
  (f_work : var) (w_work : web)
  (f_wrap : var) (w_wrap : web) : exp :=
  Ecase f_work w_work (tail_cases (M.elements C) f_work w_work).

Definition values {A} (m : M.t A) : list A :=
  List.map snd (M.elements m).

Definition wrap_prop
  (C : trans_info_t) (_ : wrapper_info_t)
  (f_work : var) (w_work : web)
  (f_wrap : var) (w_wrap : web) : Prop :=
  NoDup (values C).

(* Specification *)
Inductive trans (Γ : Ensemble var) : exp -> exp -> Prop :=
| Trans_fun :
  forall {f f_wrap w xs C u c e k e' k' f_temp w_temp w_wrap},
    let wrapper := (wrap C u f w f_wrap w_wrap) in

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
    L ! w_wrap = Some (C, u, w) ->
    wrap_prop C u f w f_wrap w_wrap ->
    C ! f_wrap = Some c ->

    trans Γ (Efun f_wrap w_wrap xs
               (Econstr f w c [f_wrap]
                  (Efun f_temp w_temp [] wrapper
                     (Eletapp f f_temp w_temp [] e)))
               (Econstr f w c [f_wrap]
                  (Efun f_temp w_temp [] wrapper
                     (Eletapp f f_temp w_temp [] k))))
      (Efun f_wrap w_wrap xs
         (Econstr f w c [f_wrap] e')
         (Econstr f w c [f_wrap] k')) (* turn the wrapper into the worker *)

| Trans_app :
  forall {C u f w xs f_temp w_temp f_wrap w_wrap},
    let wrapper := (wrap C u f w f_wrap w_wrap) in

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
    L ! w_wrap = Some (C, u, w) ->
    wrap_prop C u f w f_wrap w_wrap ->

    trans Γ (Eapp f w_wrap xs)
      (Efun f_temp w_temp [] wrapper
         (Eletapp f_temp f_temp w_temp [] (* turn the worker into the wrapper *)
            (Eapp f_temp w_wrap xs))).

Hint Constructors trans : core.

(*
Lemma free_vars_wrap C u w_work f_wrap w_wrap f:
  let wrapper := (wrap C u f w_work f_wrap w_wrap) in
  (~ f \in (bound_var wrapper)) ->
  (occurs_free wrapper <--> [set f]).
Proof.
  unfold wrap, Same_set, Ensembles.Included, Ensembles.In.
  intro cs.
  induction cs; simpl; split; intros.
  - inv H0; constructor.
  - inv H0; auto.
  - inv H0; try constructor.
    + inv H7; try constructor.
      inv H8; contradiction.
    + destruct IHcs; eauto.
      intros Hc.
      apply H.
      inv Hc.
      eapply Bound_Ecase; eauto.
      eapply in_cons; eauto.
  - inv H0; auto.
Qed.
 *)


(* Logical Relations *)
Module VTransM <: Exposed.VTrans LM.

  (* Relating wrapper and worker *)
  Definition V_trans
    (V' : nat -> wval -> wval -> Prop)
    (E' : nat -> env -> exp -> env -> exp -> Prop)
    (i0 : nat) (d : trans_info_t * wrapper_info_t * web)
    (w_wrap : web) (v_wrap : val) (w_work' : web) (v_work : val) :=
    let '(C, u, w_work) := d in
    w_work = w_work' /\
    match v_wrap with
    | Vfun f1 ρ1 xs1 e1 =>
        forall f_work f_wrap ρ,
          let wrapper := (wrap C u f_work w_work f_wrap w_wrap) in
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

Import VTransM ExposedUtil.

Module EM := Exposed.Exposed LM VTransM.
Import EM.

(* Compatibility Lemmas *)
Lemma fun_compat_trans Γ1 e e' C u c k k' f w xs w_temp f_temp w_wrap f_wrap :
  let wrapper := (wrap C u f w f_wrap w_wrap) in
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
  L ! w_wrap = Some (C, u, w) ->
  wrap_prop C u f w f_wrap w_wrap ->
  C ! f_wrap = Some c ->

  trans_correct Γ1
    (Efun f_wrap w_wrap xs
       (Econstr f w c [f_wrap]
          (Efun f_temp w_temp [] wrapper
             (Eletapp f f_temp w_temp [] e)))
       (Econstr f w c [f_wrap]
          (Efun f_temp w_temp [] wrapper
             (Eletapp f f_temp w_temp [] k))))
    (Efun f_wrap w_wrap xs
       (Econstr f w c [f_wrap] e')
       (Econstr f w c [f_wrap] k')).
Proof.
  unfold trans_correct, E, E'.
  intros He Hes Hk Hks Hw Hw1 Hf Hf_bv Hw_temp Hw_temp1 Hf_temp Hf_temp1 Hf_temp2 Hf_temp3 Hf_temp4 Hw_wrap Hwrap_prop HC.

  intros.
  inv H1.
  exists 0, OOT; split; simpl; eauto.
  inv H2.

  inv H10.
  exists 0, OOT; split; simpl; eauto.
  inv H1.

  inv H13.
  exists 0, OOT; split; simpl; eauto.
  inv H1.

  inv H14.
  exists 0, OOT; split; simpl; eauto.
  inv H1.
  2 : { exists 0, OOT; split; simpl; eauto. }

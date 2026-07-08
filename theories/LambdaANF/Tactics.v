Require Import Lia.
From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.

Ltac try_eq_rewrites :=
  match goal with
  | [H : _ = true |- _] => try rewrite H in *
  | [H : _ = false |- _] => try rewrite H in *
  end.

Ltac break_single :=
  match goal with
    | [H : True |- _] => clear H
    | [H : ?x = ?x |- _] => clear H
    | [H: False |- _] => contradiction
    | [H: unit|-_]=> destruct H
    | [H : match ?x with | [] => _ | (_ :: _) => False end |- _] => let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | [] => False | (_ :: _) => _ end |- _] => let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | false => _ | true => False end |- _] =>  let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | false => False | true => _ end |- _] =>  let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | None => _ | Some _ => False end |- _] =>  let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | None => False | Some _ => _ end |- _] =>  let H' := fresh in destruct x eqn:H'
    | [H : ?x = ?y, H' : ?x = ?z |- _] => rewrite H in H'
    | [H : context[?x - 0] |- _] => rewrite (Nat.sub_0_r x) in H
    | [ |- context[?x - 0]] => rewrite (Nat.sub_0_r x)
    (* | [H: _ <-> _|-_]=> destruct H *)
    | [H: _*_|-_]=> destruct H
    | [H: _/\_|-_]=> destruct H
    | [H: exists x, _|-_]=> destruct H
    | [H : S _ = S _ |- _] => inversion H; clear H
    | [H : (_, _) = (_, _) |- _] => inversion H; clear H
    | [H : None = Some _ |- _] => inversion H
    | [H : Some _ = Some _ |- _] => inversion H; clear H
    | [H : Some _ = None |- _] => inversion H
    | [H : _ :: _ = _ :: _ |- _] => inversion H; clear H
    | [H := _ |- _] => unfold H in *; clear H
    | [H : ~(_ \/ _) |- _] => apply Decidable.not_or in H
    | [H : Forall _ (_ :: _) |- _] => inversion H; clear H
    | [H : Forall _ [] |- _] => clear H
    | [H : Forall2 _ [] _ |- _] => inversion H; clear H
    | [H : Forall2 _ _ [] |- _] => inversion H; clear H
    | [H : Forall2 _ (_ :: _) _ |- _] => inversion H; clear H
    | [H : Forall2 _ _ (_ :: _) |- _] => inversion H; clear H
    | [H : ?x <= 0 |- _] => assert (x = 0) as ?H by lia; clear H
    | [H : 0 <= _ |- _] => clear H
    | [H : ?x = _ |- context[match ?x with _ => _ end]] => rewrite H
    | [H : ?x = _, H' : context[match ?x with _ => _ end] |- _] => rewrite H in H'
    | [H : NoDup (_ :: _) |- _] => inversion H; clear H
    | [ |- NoDup (_ :: _) ] => constructor
    | [H : set_lists (_ :: _) (_ :: _) _ = _ |- _] => inversion H; clear H
    | [H : set_lists (_ :: _) _ _ = _ |- _] => inversion H; clear H
    | [H : set_lists [] _ _ = _ |- _] => inversion H; clear H
    | [H : set_lists ?xs [] _ = _ |- _] => destruct xs
    | [H : set_lists ?xs (_ :: _) _ = _ |- _] => destruct xs
    | [H : get_list [] _ = _ |- _] => inversion H; clear H
    | [H : get_list (_ :: _) _ = _ |- _] => inversion H; clear H
    | [H : context[(M.set ?x _ _) ! ?x] |- _] => rewrite M.gss in H
    | [ |- context[(M.set ?x _ _) ! ?x]] => rewrite M.gss
    | [H' : ?y <> ?x, H : context[(M.set ?x _ _) ! ?y] |- _] => rewrite (M.gso _ _ H') in H
    | [H' : ?y <> ?x |- context[(M.set ?x _ _) ! ?y]] => rewrite (M.gso _ _ H')
    | [H' : ?x <> ?y, H : context[(M.set ?x _ _) ! ?y] |- _] => rewrite (M.gso _ _ (not_eq_sym H')) in H
    | [H' : ?x <> ?y |- context[(M.set ?x _ _) ! ?y]] => rewrite (M.gso _ _ (not_eq_sym H'))
    | [ |- context[(M.set ?x _ (M.set ?x _ _))]] => rewrite M.set2
    | [H : context[(M.set ?x _ (M.set ?x _ _))] |- _] => rewrite M.set2 in H
    | [ |- Included _ ?x ?x] => eapply Included_refl
    | [H : Ensembles.In positive [set _] _ |- _] => inversion H; clear H
    | [H : context[FromList (_ :: _)] |- _] => rewrite FromList_cons in H
    | [ |- context[FromList (_ :: _)]] => rewrite FromList_cons
    | [H : context[FromList []] |- _] => rewrite FromList_nil in H
    | [ |- context[FromList []]] => rewrite FromList_nil
    | [H : context[_ :|: Empty_set _] |- _] => rewrite Union_Empty_set_neut_r in H
    | [ |- context[_ :|: Empty_set _]] => rewrite Union_Empty_set_neut_r
    | [H : context[Empty_set _ :|: _] |- _] => rewrite Union_Empty_set_neut_l in H
    | [ |- context[Empty_set _ :|: _]] => rewrite Union_Empty_set_neut_l
    | [ |- Empty_set _ \subset _] => apply Included_Empty_set
    | [H : _ :|: _ \subset _ |- _] => (let H' := fresh in specialize (Union_Included_l _ _ _ H) as H';
                                       let H'' := fresh in specialize (Union_Included_r _ _ _ H) as H'';
                                       clear H)
    | [H : ?m ! ?x = Some ?v, H' : ?m ! ?x = Some ?v' |- _] => rewrite H in H'; inversion H'; clear H'
    | [H : match ?x with | [] => _ | _ :: _ => None end = Some _ |- _] => let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | [] => None | _ :: _ => _ end = Some _ |- _] => let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | [] => _ | _ :: _ => Some _ end = None |- _] => let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | [] => Some _ | _ :: _ => _ end = None |- _] => let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | None => _ | Some _ => None end = Some _ |- _] => let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | None => None | Some _ => _ end = Some _ |- _] => let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | None => _ | Some _ => Some _ end = None |- _] => let H' := fresh in destruct x eqn:H'
    | [H : match ?x with | None => Some _ | Some _ => _ end = None |- _] => let H' := fresh in destruct x eqn:H'
    | [H : 0 = length ?x |- _] => let H' := fresh in destruct (length_zero_iff_nil x) as
[H' _]; specialize (H' (eq_sym H)); clear H
    | [H : length ?x = 0 |- _] => let H' := fresh in destruct (length_zero_iff_nil x) as
[H' _]; specialize (H' H); clear H
    | [H : context[length []] |- _] => simpl in H
    | [ |- context[length []] ] => simpl
    | [H : context[if _ then ?x else ?x] |- _] => rewrite Tauto.if_same in H
    | [ |- context[if _ then ?x else ?x]] => rewrite Tauto.if_same
    end.

Ltac break := repeat break_single.

Ltac break_goal :=
  repeat match goal with
         | [ |- _ /\ _] => constructor; intros
         (* | [ |- _ <-> _] => constructor; intros *)
         | [ |- Forall _ []] => constructor
         | [ |- Forall _ (_ :: _)] => constructor
         | [ |- Forall2 _ [] _] => constructor
         | [ |- Forall2 _ _ []] => constructor
         | [ |- Forall2 _ (_ :: _) _] => constructor
         | [ |- Forall2 _ _ (_ :: _)] => constructor
         | [ |- Some _ = Some _] => f_equal
         | [ |- _ :: _ = _ :: _] => f_equal
         end.

Ltac cases exp :=
  let casevar := fresh "casevar" in
  let eqnname := fresh "caseeq" in
  remember exp as casevar eqn:eqnname;
  destruct casevar; symmetry in eqnname; clear eqnname.

Ltac case_match :=match goal with
  | [H : context[match ?e with _ => _ end] |- _ ]
    => let e':= fresh in
       let eqnname := fresh in
       remember e as e' eqn:eqnname; symmetry in eqnname; destruct e'
  end.
Ltac case_match_goal :=match goal with
  | [ |- context[match ?e with _ => _ end] ]
    => let e':= fresh in
       let eqnname := fresh in
       remember e as e' eqn:eqnname; symmetry in eqnname; destruct e'
  end.

Create HintDb custom_automation discriminated.
(* the hints repeatly shelve and unshelve goals, and this forms a queue
   evars are also part of these goals, which will be wrongly instantiated by auto.
   So we re-shelve any goals not of type Prop
 *)
Ltac shelve_non_Prop :=
  repeat match goal with
    | [ |- ?T] =>
        let t := type of T in match t with | Prop => idtac | _ => shelve end
    end.

Hint Extern 1 => (repeat shelve_non_Prop) : custom_automation.

Remove Hints Forall_nil : core.
Remove Hints Forall_cons : core.
Remove Hints Forall2_nil : core.
Remove Hints Forall2_cons : core.

Ltac normalize_types :=
  try cbv [map_util.M.elt] in *.


Ltac prog := repeat (repeat shelve_non_Prop; try lia; auto; try tauto; repeat try_eq_rewrites; break; subst; break_goal; intros; normalize_types; repeat (shelve_non_Prop; unshelve auto 1 with custom_automation)).

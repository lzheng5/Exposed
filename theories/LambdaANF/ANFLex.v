From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Common Require Import Base Util.
From LambdaANF Require Import Util Tactics ANF.
Export Base.

Section ValInduct.
Context {P : val -> Prop}
        {IHfun : forall f ρ xs e, P (Vfun f ρ xs e)}
        {IHconstr : forall c vs, Forall P vs -> P (Vconstr c vs)}.

Fixpoint val_ind_inner (v : val) {struct v} : P v :=
  match v with
  | Vfun f ρ xs e => IHfun f ρ xs e
  | Vconstr c vs =>
      let fix loop (vs : list val) : Forall P vs :=
        match vs return Forall P vs with
       | [] => @Forall_nil val P
       | v :: vs => @Forall_cons val P v vs (val_ind_inner v) (loop vs)
       end in
     IHconstr c vs (loop vs)
  end.
End ValInduct.

Combined Scheme val_ind'' from val_ind_inner.

Hint Extern 1 =>
       (match goal with
        | [H : match ?v with | Vfun _ _ _ _ => _ | Vconstr _ _ => False end |- _] => destruct v
        | [H : match ?v with | Vfun _ _ _ _ => False | Vconstr _ _ => _ end |- _] => destruct v
        end; shelve) : custom_automation.

Hint Constructors val : core.


Section ValInduct'.
Context {P_val : val -> Prop}
        {P_env : env -> Prop}
        {IHVfun : forall f ρ xs e, P_env ρ -> P_val (Vfun f ρ xs e)}
        {IHVconstr : forall c vs, Forall P_val vs -> P_val (Vconstr c vs)}
        {IHenv : forall ρ, (forall x v, ρ ! x = Some v -> P_val v) -> P_env ρ}.

Fixpoint val_ind_inner'' (v : val) {struct v} : P_val v :=
  match v with
  | Vfun f ρ xs e =>
      let prf (m : M.t val) : @tree_Forall val P_val m :=
        match m with
        | M.Empty => Forall_Empty
        | M.Nodes m' =>
            let fix loop (m' : M.tree' val) : @tree_Forall' val P_val m' :=
              match m' with
              | M.Node001 r => Forall_Node001 r (loop r)
              | M.Node010 x => Forall_Node010 x (val_ind_inner'' x)
              | M.Node011 x r => Forall_Node011 x r (val_ind_inner'' x) (loop r)
              | M.Node100 l => Forall_Node100 l (loop l)
              | M.Node101 l r => Forall_Node101 l r (loop l) (loop r)
              | M.Node110 l x => Forall_Node110 l x (loop l) (val_ind_inner'' x)
              | M.Node111 l x r => Forall_Node111 l x r (loop l) (val_ind_inner'' x) (loop r)
              end in
            Forall_Nodes m' (loop m')
        end in
      let prf : P_env ρ := IHenv ρ (tree_Forall_prop ρ (prf ρ)) in
      IHVfun f ρ xs e prf
  | Vconstr c vs =>
      let fix loop (vs : list val) : Forall P_val vs :=
        match vs return Forall P_val vs with
        | [] => @Forall_nil val P_val
        | v :: vs => @Forall_cons val P_val v vs (val_ind_inner'' v) (loop vs)
        end in
      IHVconstr c vs (loop vs)
  end.
End ValInduct'.

Combined Scheme val_ind''' from val_ind_inner''.

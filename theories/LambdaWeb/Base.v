From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.

Module M := Maps.PTree.

(* Web Identifiers *)
Definition web := M.elt.
Definition webs := Ensemble web.

(* Exposed webs *)
Parameter Exposed : webs.

Parameter exposed_dec : Decidable Exposed.

Parameter exposedb : web -> bool.

Axiom exposed_reflect : forall w, Bool.reflect (w \in Exposed) (exposedb w).

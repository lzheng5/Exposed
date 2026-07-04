From Coq Require Import ZArith.ZArith Sets.Ensembles.
From CertiCoq.LambdaANF Require Import Ensembles_util.

From LambdaWeb Require Import Base.

(* We annotate function values with some Exposed web id based on their arities. *)
Definition arity_to_web (n : nat) : web := Pos.of_nat n.

(* We annotate constructor values with a single Exposed web id, since the sum and prod types get merged together in the language definition. But this matches with CertiCoq. *)
(* Annotate constructor values with `wc`.
   This works since closure and constructor values live in different web universes. *)
(* TODO: rename *)
Definition wc := arity_to_web 0.

Parameter w_constr_exposed : (wc \in Exposed).

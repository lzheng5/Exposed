From Coq Require Import ZArith.ZArith.
From LambdaWeb Require Import ANF.

(* We annotate function values with some Exposed web id based on their arities. *)
Definition arity_to_web (n : nat) : web := Pos.of_nat n.

(* We annotate constructor values with a single Exposed web id, since the sum and prod types get merged together in the language definition. But this matches with CertiCoq. *)
(* Annotate constructor values with `wc`.
   This works since closure and constructor values live in different web universes. *)
Definition wc := arity_to_web 0.

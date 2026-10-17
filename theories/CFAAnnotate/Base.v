From Coq Require Import ZArith.ZArith Sets.Ensembles.
From CertiCoq.LambdaANF Require Import Ensembles_util.

From LambdaWeb Require Import Base UniqueExposed.

(* Two Web Ids *)

(* Everything imported from or exported to the context lives in the exposed web `w_ext`.
   Everything that never interacts with the context lives in the internal web `w_int`. *)
Definition w_ext : web := w0.

Lemma w_ext_exposed : w_ext \in Exposed.
Proof. apply w0_exposed. Qed.

Lemma w_ext_exposedb : exposedb w_ext = true.
Proof. apply w0_exposedb. Qed.

Lemma w_ext_unique w : w \in Exposed -> w = w_ext.
Proof. apply Exposed_singleton. Qed.

Parameter w_int : web.

Parameter w_int_not_exposed : ~ (w_int \in Exposed).

Lemma w_int_exposedb : exposedb w_int = false.
Proof.
  destruct (exposed_reflect w_int); auto.
  exfalso; apply w_int_not_exposed; auto.
Qed.

Lemma w_int_neq_w_ext : w_int <> w_ext.
Proof.
  intro Heq.
  apply w_int_not_exposed.
  rewrite Heq.
  apply w_ext_exposed.
Qed.

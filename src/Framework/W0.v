From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.

From Framework Require Import ANF.

(* Single Exposed Web Id *)

Module W0.

  (* Assume single exposed web id for convienience *)

  Parameter w0 : web.
  Parameter w0_exposed : w0 \in Exposed.
  Parameter Exposed_singleton : forall w, w \in Exposed -> w = w0.

  Lemma w0_exposedb : exposedb w0 = true.
  Proof.
    destruct (exposed_reflect w0); auto.
    exfalso.
    apply n.
    apply w0_exposed; auto.
  Qed.

  Theorem Exposed_nonempty : exists w, w \in Exposed.
  Proof. exists w0. apply w0_exposed. Qed.

End W0.


Require Export SystemF_inf.
Require Export Fii_inf.
Require Export Infrastructure.

(* ********************************************************************** *)
(** * Strong Normalization *)

Definition halts t  :=
  exists t',  value t' /\ t ->* t'.

Theorem normalization : forall t T,
    typ nil nil t T ->
    halts t.
Admitted.

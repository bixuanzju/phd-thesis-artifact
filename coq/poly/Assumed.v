
Require Import SystemF_inf.
Require Import Fii_inf.
Require Import Infrastructure.
Require Import Algorithm.


(* ********************************************************************** *)
(** * Strong Normalization *)

Definition halts t  :=
  exists t',  value t' /\ t ->* t'.

Theorem normalization : forall t T,
    typ nil nil t T ->
    halts t.
Admitted.



(* ********************************************************************** *)
(** * Hairy Renaming *)

Lemma asub_rename : forall X Y Q A B C c,
    asub A (Q ++ [qs_all X C]) (open_sty_wrt_sty B (sty_var_f X)) c ->
    X `notin` fv_sty_in_sty B \u fv_sty_in_sty A ->
    Y `notin` fv_sty_in_sty B \u fv_sty_in_sty A  ->
    wf_fs Q ->
    asub A (Q ++ [qs_all Y C]) (open_sty_wrt_sty B (sty_var_f Y)) c.
Admitted.

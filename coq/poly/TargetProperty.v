
Require Import Infrastructure.


(* ********************************************************************** *)
(** * Type Safety *)


Theorem progress : forall t T,
  typ nil nil t  T ->
  value t \/ exists t', step t t'.
Proof with eauto.
  introv Typ. lets Typ': Typ. inductions Typ; try solve [left*].

  - Case "var".
    inverts H0...

  - Case "app".
    destruct IHTyp1 as [Val1 | [t1' Red1]]...
    destruct IHTyp2 as [Val2 | [t2' Red2]]...

    inverts Typ1; inverts Val1...
    inverts H0...
    inverts H0...
    forwards (v1 & v2 & ? & ? & ?): prod_canonical H...
    substs...
    inverts H0...
    forwards : unit_canonical H...
    forwards : unit_canonical Typ2...
    substs...

  - Case "pair".
    destruct IHTyp1 as [Val1 | [t1' Red1]]...
    destruct IHTyp2 as [Val2 | [t2' Red2]]...

  - Case "tapp".
    destruct IHTyp as [Val | [t1 Red]]...

    inverts Typ; inverts Val...
    inverts H1...
    inverts H1...
    inverts H1...

  - Case "capp".

    destruct IHTyp as [Val | [t1 Red]]...
    inverts H...

    forwards (v1 & v2 & ? & ? & ?): prod_canonical Typ...
    substs...

    forwards (v1 & v2 & ? & ? & ?): prod_canonical Typ...
    substs...
Qed.





Theorem preservation : forall Δ Γ e e' T,
    typ Δ Γ e T ->
    step e e' ->
    typ Δ Γ e' T.
Proof with eauto.
  introv Typ.
  gen e'.
  induction Typ; try solve [introv J; inverts~ J].

  + Case "app".
    introv Step.
    inverts* Step.

    inverts* Typ2.
    inverts* Typ1.
    inverts* H2.
    inverts* H5.


    inverts* Typ1.
    inverts* H7.
    inverts* H3.

    inverts* Typ1.
    inverts* H6.

    inverts* Typ1.
    pick fresh x.
    rewrite* (@subst_exp_in_exp_intro x).
    rewrite_env (nil ++ gg).
    eapply typing_through_subst_exp_in_exp...

  + Case "tapp".
    introv Step.

    inverts* Step.

    inverts* Typ.
    inverts* H7.
    inverts* H9.
    lets (? & ? & ?) : typing_regular H3.
    pick_fresh X.
    rewrite* (@subst_ty_in_ty_intro X).
    eapply typ_capp...
    rewrite* (@subst_ty_in_ty_intro X)...
    rewrite_env (nil ++ dd).
    eapply ctyp_through_subst_typ_in_typ...
    rewrite_env (nil ++ dd).
    eapply wft_subst_tb...

    inverts* Typ.
    pick fresh X.
    rewrite* (@subst_ty_in_ty_intro X).
    rewrite* (@subst_ty_in_exp_intro X).
    rewrite_env (nil ++ dd).
    asserts_rewrite (gg = map (subst_ty_in_ty T X) gg).
    eapply map_subst_typ_in_binding_id...
    eapply typing_through_subst_typ_in_exp...

  + Case "capp".

    introv J. inverts J; try solve [inverts* H].


    inverts* Typ.
    inverts* H.

    inverts* Typ.
    inverts* H.

Qed.


Theorem preservation_multi_step : forall e e' T,
    typ nil nil e T ->
    e ->* e' ->
    typ nil nil e' T.
Proof with eauto using preservation.
  introv ? Red.
  gen T.
  induction Red; introv Typ; simpls...
Qed.

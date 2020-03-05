Require Import Declarative.BasicProperties.
Require Import Declarative.KindReasoning.

Theorem transitivity : forall e2 Γ e1 e3 A B,
  Γ ⊢ e1 <: e2 : A -> Γ ⊢ e2 <: e3 : B -> Γ ⊢ e1 <: e3 : A.
Proof.
  intro. assert (lc_expr e2) by admit.
  induction H; intros Γ e1' e3' A' B' Hsubl;
    generalize dependent e3'; generalize dependent B'.
  - dependent induction Hsubl; intros B' e3' Hsubr.
    + dependent induction Hsubr.
      * auto.
      * assert ( binds x * G ) by now apply var_star_inversion.
        apply binds_inversion in H0.
        destruct H0 as [Γ1 [Γ2 E]].
        rewrite E in H3, H.
        assert ( * = A ) by (eapply binds_type_equal; eassumption).
        rewrite <- H0 in *. apply s_forall_r with L k; eauto.
      * eauto 3.
    + eauto.
    + eauto.
  - dependent induction Hsubl; intros B' e3' Hsubr.
    + dependent induction Hsubr.
      * auto.
      * apply star_type_inversion in Hsubr2. inversion Hsubr2.
      * apply IHHsubr1; auto.
    + eauto.
    + eauto.
  - dependent induction Hsubl; intros B' e3' Hsubr.
    + dependent induction Hsubr.
      * eauto 3.
      * apply num_not_of_star in Hsubr2. contradiction.
      * eauto 3.
    + eauto 3.
    + eauto 3.
  - dependent induction Hsubl; intros B' e3' Hsubr.
    + dependent induction Hsubr; eauto 3.
    + eauto 3.
    + eauto 3.
  - dependent induction Hsubl; intros B' e3' Hsubr.
    + dependent induction Hsubr.
      * eauto 3.
      * admit.
      * eauto 3.
    + eauto 3.
    + eauto 3.
  - dependent induction Hsubl; intros B' e3' Hsubr.
    + dependent induction Hsubr.
      * apply s_abs with (L `union` L1 `union` L0); eauto 1.
        intros. apply H1 with x (B0 <^> x); auto 2.
      * apply abs_not_of_star in Hsubr2. contradiction.
      * eauto 2.
    + eauto 3.
    + eauto 3.
  - dependent induction Hsubl; intros B' e3' Hsubr.
    + dependent induction Hsubr.
      * apply s_pi with (L `union` L0 `union` L1) k3; admit.
      * admit.
      * eauto 2.
    + eauto 3.
    + eauto 3.
  - dependent induction Hsubl; intros B' e3' Hsubr.
    + eauto 3.
    + admit.
    + admit.
    + eauto 3.
  - dependent induction Hsubl; intros B' e3' Hsubr.
    + dependent induction Hsubr.
      * apply s_forall with (L `union` L0 `union` L1) k; eauto 3.
        intros. eapply H1. eauto. auto. apply H5. auto.
      * apply bind_not_of_star in Hsubr2. contradiction.
      * eauto 2.
    + eauto 3.
    + eauto 3.
Admitted.

Theorem transitivity' : forall e2 Γ e1 e3 A,
  Γ ⊢ e1 <: e2 : A -> Γ ⊢ e2 <: e3 : A -> Γ ⊢ e1 <: e3 : A.
Proof.
  intro. assert (lc_expr e2) by admit.
  induction H; intros Γ e1' e3' A' Hsubl;
    generalize dependent e3'.
  - dependent induction Hsubl; intros e3' Hsubr.
    + assumption.
    + eauto.
    + admit.
Admitted.

Lemma binds_var_consistent : forall Γ x A B,
    Γ ⊢ e_var_f x <: e_var_f x : A -> x : B ∈ Γ -> Γ ⊢ B <: A : *.
Proof.
  intros.
  dependent induction H.
  - induction G.
    + inversion H0.
    + destruct a. unfold binds in *. simpl in *.
      destruct H0.
      * inversion H0. subst. destruct H1; inversion H; subst.
        ** inversion H1. subst.
           now apply weakening_cons.
        ** now apply binds__in_dom in H1.
      * destruct H1; inversion H; subst.
        ** inversion H1. subst.
           now apply binds__in_dom in H0.
        ** apply weakening_cons; auto.
  - admit. (* need transitivity *)
Admitted.

Theorem type_consistency : forall Γ e1 e2 A B,
  Γ ⊢ e1 : A -> Γ ⊢ e1 <: e2 : B -> Γ ⊢ e1 <: e2 : A.
Proof.
  intros Γ e1 e2 A B Hsub1 Hsub.
  generalize dependent A.
  induction Hsub; intros.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - generalize dependent L.
    dependent induction Hsub1; intros.
    + apply s_abs with (L `union` L0).
      * assumption.
      * intros.
        apply H2. auto.
        apply H. auto.
    + apply s_sub with A0.
      * apply IHHsub1_1 with L; auto.
      * assumption.
  - dependent induction Hsub0.
    + apply s_pi with (L `union` L0); auto.
    + apply s_sub with A.
      * apply IHHsub0_1; auto.
      * assumption.
  - dependent induction Hsub0.
    + apply s_app with A0.
      * assumption.
      * apply IHHsub2. assumption.
    + apply s_sub with A0.
      * apply IHHsub0_1; auto.
      * assumption.
  - dependent induction Hsub1.
    + apply s_forall with (L0 `union` L).
      * assumption.
      * assumption.
      * intros. apply H1; auto.
    + apply s_sub with A0; auto.
  - dependent induction Hsub0.
    + apply s_forall_l with L e; assumption.
    + apply s_forall_l with L e; assumption.
    + apply s_forall_l with L e; assumption.
    + apply s_sub with A0.
      * apply IHHsub0_1; auto.
      * assumption.
  - dependent induction Hsub0; eauto 3.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - dependent induction Hsub1; eauto 3.
  - auto.
Admitted.

Theorem type_correct : forall Γ A B C, Γ ⊢ A <: B : C -> Γ ⊢ C : *.
Proof.
Admitted.

Theorem substitution : forall Γ1 Γ2 x A B e1 e2 e3,
  Γ1 , x : B ,, Γ2 ⊢ e1 <: e2 : A ->
  Γ1 ⊢ e3 : B ->
  Γ1 ,, subst_context x e3 Γ2 ⊢
    subst_expr e3 x e1 <: subst_expr e3 x e2 : subst_expr e3 x A.
Proof.
Admitted.

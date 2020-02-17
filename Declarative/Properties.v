Require Import Declarative.LanguageUtil.
Require Import Program.Equality.
Import ListNotations.

Theorem ctx_weakening : forall Γ1 Γ2 Γ3 e1 e2 A,
    Γ1 ,, Γ3 ⊢ e1 <: e2 : A ->
    ⊢ Γ1 ,, Γ2 ,, Γ3 ->
    Γ1 ,, Γ2 ,, Γ3 ⊢ e1 <: e2 : A.
Proof.
  intros until A. intro Hsub.
  dependent induction Hsub; intro Hwf.
  - apply s_var.
    + assumption.
    + now apply var_in_ctx_weakening.
  - now apply s_lit.
  - now apply s_star.
  - now apply s_int.
  - apply s_abs with (L `union` dom (Γ1 ,, Γ2 ,, Γ3)).
    + now apply IHHsub.
    + intros. distribute_ctx. apply H0.
      * auto.
      * reflexivity.
      * apply wf_cons.
        ** exact Hwf.
        ** auto.
        ** now apply IHHsub.
  - apply s_pi with (L `union` dom (Γ1 ,, Γ2 ,, Γ3)).
    + now apply IHHsub1.
    + now apply IHHsub2.
    + now apply IHHsub3.
    + intros. distribute_ctx. apply H0.
      * auto.
      * reflexivity.
      * apply wf_cons.
        ** assumption.
        ** auto.
        ** now apply IHHsub1.
    + intros. distribute_ctx. apply H2.
      * auto.
      * reflexivity.
      * apply wf_cons.
        ** assumption.
        ** auto.
        ** now apply IHHsub2.
  - apply s_app with A.
    + now apply IHHsub1.
    + now apply IHHsub2.
  - apply s_forall with (L `union` dom (Γ1 ,, Γ2 ,, Γ3)).
    + assumption.
    + now apply IHHsub.
    + intros. distribute_ctx. apply H1.
      * auto.
      * reflexivity.
      * apply wf_cons.
        ** assumption.
        ** auto.
        ** now apply IHHsub.
  - apply s_forall_l with (L `union` dom (Γ1 ,, Γ2 ,, Γ3)) e.
    + assumption.
    + assumption.
    + now apply IHHsub1.
    + now apply IHHsub2.
    + now apply IHHsub3.
    + intros. distribute_ctx. apply H2.
      * auto.
      * reflexivity.
      * apply wf_cons.
        ** assumption.
        ** auto.
        ** now apply IHHsub1.
  - apply s_forall_r with (L `union` dom (Γ1 ,, Γ2 ,, Γ3)).
    + assumption.
    + now apply IHHsub.
    + intros. distribute_ctx. apply H1.
      * auto.
      * reflexivity.
      * apply wf_cons.
        ** assumption.
        ** auto.
        ** now apply IHHsub.
    + intros. apply H2. auto.
  - apply s_sub with A.
    + now apply IHHsub1.
    + now apply IHHsub2.
Qed.

Corollary ctx_weakening_cons : forall Γ x X e1 e2 A,
    Γ ⊢ e1 <: e2 : A ->
    ⊢ Γ , x : X ->
    Γ , x : X ⊢ e1 <: e2 : A.
Proof.
  intros.
  replace (Γ , x : X) with (Γ ,, (x ~ X) ,, []) in * by reflexivity.
  now apply ctx_weakening.
Qed.

Theorem reflexivity_r : forall Γ e1 e2 A, Γ ⊢ e1 <: e2 : A -> Γ ⊢ e2 : A.
Proof.
  intros.
  induction H.
  - auto.
  - auto.
  - auto.
  - auto.
  - apply s_abs with L.
    + assumption.
    + intros. now apply H1.
  - apply s_pi with L.
    + assumption.
    + assumption.
    + assumption.
    + auto.
    + auto.
  - apply s_app with A.
    + assumption.
    + assumption.
  - apply s_forall with L.
    + assumption.
    + assumption.
    + auto.
  - assumption.
  - apply s_forall_r with (L `union` dom G `union` (fv_expr (e_all B C))).
    + assumption.
    + assumption.
    + intros.
      apply s_forall_l with (add x (L `union` dom G)) (e_var_f x).
      * auto.
      * assumption.
      * apply ctx_weakening_cons; auto.
      * auto.
      * auto.
      * intros.
        replace (G , x : B , x0 : B) with (G ,, x ~ B ,, x0 ~ B) by reflexivity.
        apply ctx_weakening.
        ** apply H2. auto.
        ** apply wf_cons.
          ++ apply wf_cons; auto.
          ++ auto.
          ++ apply ctx_weakening_cons; auto.
    + auto.
  - apply s_sub with A.
    + assumption.
    + assumption.
Qed.

Theorem transitivity : forall Γ x y z A,
    Γ ⊢ x <: y : A -> Γ ⊢ y <: z : A -> Γ ⊢ x <: z : A.
Proof.
Admitted.

Theorem wf_strengthening : forall Γ1 Γ2 x A,
    ⊢ Γ1 , x : A ,, Γ2 ->
    context_fresh x Γ2 ->
    ⊢ Γ1 ,, Γ2.
Proof.
Admitted.

Lemma var_in_ctx_strengthening : forall Γ1 Γ2 x y (A B : expr),
    x : A ∈ Γ1 , y : B ,, Γ2 ->
    y <> x ->
    x : A ∈ Γ1 ,, Γ2.
Proof.
  intros Γ1 Γ2. generalize dependent Γ1.
  induction Γ2; intros.
  - destruct H.
    + inversion H. contradiction.
    + assumption.
  - destruct a. destruct H.
    + inversion H. subst. auto.
    + unfold binds, In. right.
      now apply IHΓ2 with y B.
Qed.

Theorem ctx_strengthening : forall Γ1 Γ2 x A e1 e2 B,
    Γ1 , x : A ,, Γ2 ⊢ e1 <: e2 : B ->
    context_fresh x Γ2 ->
    x # e1 -> x # e2 -> x # B ->
    Γ1 ,, Γ2 ⊢ e1 <: e2 : B.
Proof.
  intros until B. intros Hsub.
  remember (Γ1 , x : A ,, Γ2) as Γ eqn: Heq.
  generalize dependent Γ2.
  generalize dependent A.
  generalize dependent x.
  generalize dependent Γ1.
  apply sub_mut with
      (P := fun (Γ : context) (e1 e2 B : expr) (Hsub : Γ ⊢ e1 <: e2 : B) =>
              forall Γ1 x A Γ2, Γ = Γ1 , x : A ,, Γ2 -> context_fresh x Γ2 ->
                 x # e1 -> x # e2 -> x # B -> Γ1 ,, Γ2 ⊢ e1 <: e2 : B)
      (P0 := fun (Γ : context) (Hwf : ⊢ Γ) =>
               forall Γ1 Γ2 x A, Γ = Γ1 , x : A ,, Γ2 -> context_fresh x Γ2 ->
                 ⊢ Γ1 ,, Γ2).
  all: intros; subst; simpl in *.
  - apply s_var. now apply H with x0 A0.
    apply var_in_ctx_strengthening with x0 A0; auto 2.
  - apply s_lit . eauto.
  - apply s_star. eauto.
  - apply s_int . eauto.
  - apply s_abs with (add x (fv_expr A0 `union` L)).
    + eapply H; eauto.
    + intros. distribute_ctx.
      apply H0 with x A0; auto 3.
  - apply s_pi with (add x (fv_expr A `union` L)).
    + eapply H ; eauto.
    + eapply H0; eauto.
    + eapply H1; eauto.
    + intros. distribute_ctx.
      apply H2 with x A; auto 3.
    + intros. distribute_ctx.
      apply H3 with x A; auto 3.
  - admit. (* s_app *)
  - apply s_forall with (add x (fv_expr A0 `union` L)).
    + assumption.
    + eapply H; eauto.
    + intros. distribute_ctx.
      apply H0 with x A0; eauto.
  - admit. (* s_forall_l *)
  - apply s_forall_r with (add x (fv_expr A0 `union` L)).
    + assumption.
    + eapply H; eauto.
    + intros. distribute_ctx.
      apply H0 with x A0; auto 3.
    + auto.
  - admit. (* s_sub *)

  (* ⊢ Γ1 , x : A ,, Γ2 → context_fresh x Γ2 → ⊢ Γ1 ,, Γ2 *)
  - destruct Γ2; inversion H.
  - destruct Γ2.
    + inversion H1. now subst.
    + destruct p. inversion H1. subst; simpl in H2; destruct H2.
      apply wf_cons.
      * eapply H; eauto.
      * auto.
      * eapply H0; eauto.
  - assumption.
Admitted.

Theorem reflexivity_l : forall Γ e1 e2 A, Γ ⊢ e1 <: e2 : A -> Γ ⊢ e1 : A.
Proof.
  intros. induction H.
  - now apply s_var.
  - now apply s_lit.
  - now apply s_star.
  - now apply s_int.
  - eapply s_abs.
    + assumption.
    + intros x Hxl.
      apply H1.
      eassumption.
  - eapply s_pi; auto.
  - now apply s_app with A.
  - now apply s_forall with L.
  - apply s_forall_r with (L `union` dom G `union` fv_expr (e_all A B)).
    + assumption.
    + assumption.
    + intros. apply s_forall_l with (add x (dom G `union` L)) (e_var_f x).
      * auto.
      * assumption.
      * apply ctx_weakening_cons; auto.
      * auto.
      * apply H4. auto.
      * intros.
        replace (G , x : A , x0 : A) with (G ,, x ~ A ,, x0 ~ A) by reflexivity.
        apply ctx_weakening.
        ** simpl. apply H4. auto.
        ** apply wf_cons. apply wf_cons; auto.
           simpl. auto.
           apply ctx_weakening_cons; auto.
    + intros. auto.
  - admit. (* MOST TRICKY CASE *)
  - eauto.
Admitted.


Theorem ctx_narrowing : forall Γ1 Γ2 x A B C e1 e2,
  Γ1 , x : B ,, Γ2 ⊢ e1 <: e2 : C ->
  Γ1 ⊢ A <: B : * ->
  ⊢ Γ1 , x : A ,, Γ2 ->
  Γ1 , x : A ,, Γ2 ⊢ e1 <: e2 : C.
Proof.
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
    + apply s_forall with L0.
      * assumption.
      * assumption.
      * admit. (* problem here *)
    + apply s_sub with A0; auto.
  - dependent induction Hsub0.
    + admit.
    + admit.
    + apply s_sub with A0.
      * apply IHHsub0_1; auto.
      * assumption.
  - admit.
  - auto.
Admitted.

Theorem transitivity : forall Γ e1 e2 e3 A,
  Γ ⊢ e1 <: e2 : A -> Γ ⊢ e2 <: e3 : A -> Γ ⊢ e1 <: e3 : A.
Proof.
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

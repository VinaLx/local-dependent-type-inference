Require Export Declarative.LanguageUtil.
Require Import Program.Equality.

Import ListNotations.

Theorem weakening : forall Γ1 Γ2 Γ3 e1 e2 A,
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
  - apply s_abs with (L `union` dom (Γ1 ,, Γ2 ,, Γ3)) k.
    + now apply IHHsub.
    + intros. distribute_ctx. apply H0.
      * auto.
      * reflexivity.
      * eapply wf_cons.
        ** exact Hwf.
        ** auto.
        ** now apply IHHsub.
  - apply s_pi with (L `union` dom (Γ1 ,, Γ2 ,, Γ3)) k1.
    + now apply IHHsub1.
    + now apply IHHsub2.
    + now apply IHHsub3.
    + intros. distribute_ctx. apply H0.
      * auto.
      * reflexivity.
      * eapply wf_cons.
        ** assumption.
        ** auto.
        ** now apply IHHsub1.
    + intros. distribute_ctx. apply H2.
      * auto.
      * reflexivity.
      * eapply wf_cons.
        ** assumption.
        ** auto.
        ** now apply IHHsub2.
  - apply s_app with A.
    + now apply IHHsub1.
    + now apply IHHsub2.
  - apply s_forall with (L `union` dom (Γ1 ,, Γ2 ,, Γ3)) k.
    + now apply IHHsub.
    + intros. distribute_ctx. apply H0.
      * auto.
      * reflexivity.
      * eapply wf_cons.
        ** assumption.
        ** auto.
        ** now apply IHHsub.
  - apply s_forall_l with (L `union` dom (Γ1 ,, Γ2 ,, Γ3)) e k.
    + assumption.
    + now apply IHHsub1.
    + now apply IHHsub2.
    + now apply IHHsub3.
    + intros. distribute_ctx. apply H1.
      * auto.
      * reflexivity.
      * eapply wf_cons.
        ** assumption.
        ** auto.
        ** now apply IHHsub1.
  - apply s_forall_r with (L `union` dom (Γ1 ,, Γ2 ,, Γ3)) k.
    + now apply IHHsub1.
    + now apply IHHsub2.
    + intros. distribute_ctx. apply H0.
      * auto.
      * reflexivity.
      * eapply wf_cons.
        ** assumption.
        ** auto.
        ** now apply IHHsub1.
  - apply s_forall_2 with (L `union` dom (Γ1 ,, Γ2 ,, Γ3)) k.
    + now apply IHHsub.
    + intros. distribute_ctx. apply H0.
      * auto.
      * reflexivity.
      * eapply wf_cons.
        ** assumption.
        ** auto.
        ** now apply IHHsub.
  - apply s_sub with A k.
    + now apply IHHsub1.
    + now apply IHHsub2.
Qed.

Corollary weakening_cons : forall Γ x X e1 e2 A,
    Γ ⊢ e1 <: e2 : A ->
    ⊢ Γ , x : X ->
    Γ , x : X ⊢ e1 <: e2 : A.
Proof.
  intros.
  replace (Γ , x : X) with (Γ ,, (x ~ X) ,, nil)  by reflexivity.
  now apply weakening.
Qed.

Hint Resolve weakening_cons : core.

Corollary weakening_app : forall Γ Γ' e1 e2 A,
    Γ ⊢ e1 <: e2 : A ->
    ⊢ Γ ,, Γ' ->
    Γ ,, Γ' ⊢ e1 <: e2 : A.
Proof.
  intros.
  replace (Γ ,, Γ') with (Γ ,, Γ' ,, nil) by reflexivity.
  now apply weakening.
Qed.

Theorem reflexivity_r : forall Γ e1 e2 A, Γ ⊢ e1 <: e2 : A -> Γ ⊢ e2 : A.
Proof.
  intros.
  induction H.
  - auto.
  - auto.
  - auto.
  - auto.
  - apply s_abs with L k.
    + assumption.
    + intros. now apply H1.
  - apply s_pi with L k1.
    + assumption.
    + assumption.
    + assumption.
    + auto.
    + auto.
  - apply s_app with A.
    + assumption.
    + assumption.
  - apply s_forall with L k.
    + assumption.
    + auto.
  - assumption.
  - apply s_forall_2 with L k.
    + assumption.
    + assumption.
  - apply s_forall_2 with L k.
    + assumption.
    + apply H1.
  - apply s_sub with A k.
    + assumption.
    + assumption.
Qed.

Theorem reflexivity_l : forall Γ e1 e2 A, Γ ⊢ e1 <: e2 : A -> Γ ⊢ e1 : A.
Proof.
  intros. induction H.
  - now apply s_var.
  - now apply s_lit.
  - now apply s_star.
  - now apply s_int.
  - eapply s_abs.
    + eassumption.
    + intros x Hxl.
      apply H1.
      eassumption.
  - eapply s_pi; eauto.
  - now apply s_app with A.
  - now apply s_forall with L k.
  - apply s_forall_2 with L k.
    + assumption.
    + apply H3.
  - assumption.
  - apply s_forall_2 with L k; assumption.
  - eauto.
Qed.

Hint Resolve reflexivity_r : core.
Hint Resolve reflexivity_l : core.



Theorem ctx_narrowing : forall Γ1 Γ2 x A B C e1 e2 k,
  Γ1 , x : B ,, Γ2 ⊢ e1 <: e2 : C ->
  Γ1 ⊢ A <: B : e_kind k ->
  Γ1 , x : A ,, Γ2 ⊢ e1 <: e2 : C.
Proof.
  intros.
  remember (Γ1 , x : B ,, Γ2) as Γ.
  generalize HeqΓ. clear HeqΓ.
  generalize Γ2. clear Γ2.
  apply sub_mut with
    (P := fun Γ e1 e2 C (_ : Γ ⊢ e1 <: e2 : C) =>
        forall Γ2, Γ = Γ1 , x : B ,, Γ2 -> Γ1 , x : A ,, Γ2 ⊢ e1 <: e2 : C)
    (P0 := fun Γ (_ : ⊢ Γ) =>
        forall Γ2, Γ = Γ1 , x : B ,, Γ2 -> ⊢ Γ1 , x : A ,, Γ2); intros; subst.
  - assert ({x = x0} + {x <> x0}) as [E | NE] by apply eq_dec.
    + subst. apply weakening_app; auto.
      assert (A0 = B) by now apply binds_type_equal with Γ1 x0 Γ2. subst.
      apply s_sub with A k.
      * apply s_var; eauto.
      * apply weakening_cons; eauto.
    + apply s_var.
      * auto.
      * now apply binds_type_not_equal with B.
  - auto.
  - auto.
  - auto.
  - eauto.
  - apply s_pi with (add x L) k1; auto.
  - eauto.
  - eauto.
  - apply s_forall_l with L e k0; eauto 3.
  - apply s_forall_r with (add x L) k0; auto.
  - eauto.
  - eauto.

  (* ⊢ Γ1 , x : B ,, Γ2 → Γ1 ⊢ A <: B : * → ⊢ Γ1 , x : A ,, Γ2 *)
  - destruct Γ2; inversion H1.
  - destruct Γ2; try destruct p; inversion H3; subst.
    + eapply wf_cons; eauto.
    + eapply wf_cons; auto.

  - assumption.
Qed.

Corollary ctx_narrowing_cons : forall Γ1 x A B C e1 e2 k,
    Γ1 , x : A ⊢ e1 <: e2 : C ->
    Γ1 ⊢ B <: A : e_kind k ->
    Γ1, x : B ⊢ e1 <: e2 : C.
Proof.
  intros.
  replace (Γ1 , x : B) with (Γ1 ,, x ~ B ,, nil) by reflexivity.
  apply ctx_narrowing with A k; auto.
Qed.

Require Import Declarative.BasicProperties.
Require Import Declarative.KindReasoning.
Require Import Declarative.OccurenceReasoning.

Require Import Program.Tactics.

Lemma binds_subst : forall Γ1 Γ2 x x' A B e,
    ⊢ Γ1, x' : B,, Γ2 ->
    x : A ∈ Γ1, x' : B,, Γ2 -> x <> x' -> x : [e / x'] A ∈ Γ1 ,, [e // x'] Γ2.
Proof.
  induction Γ2; simpl; intros.
  - destruct H0.
    + inversion H0. subst. contradiction.
    + inversion H. subst.
      assert (x' # A) by (eapply notin_dom_bind_fresh; eauto).
      rewrite fresh_subst_eq; auto.
  - destruct a. destruct H0.
    + inversion H0. subst. auto.
    + right. inversion H. apply IHΓ2 with B; auto.
Qed.

Lemma subst_ctx_distr_cons : forall Γ x A y e,
    [e // y] Γ , x : [e / y] A = [e // y] (Γ , x : A).
Proof.
  intros. reflexivity.
Qed.

Lemma dom_subst_equal : forall Γ x v,
    dom ([v // x] Γ) = dom Γ.
Proof.
  induction Γ; intros.
  + reflexivity.
  + destruct a. simpl. now rewrite (IHΓ x v).
Qed.

Import AtomSetProperties.

Lemma dom_insert_subset : forall Γ2 Γ1 a (A : expr),
    union (dom Γ2) (dom Γ1) [<=] dom (Γ1 , a : A ,, Γ2).
Proof.
  induction Γ2; simpl; intros.
  - apply subset_add_2. intro. intros.
    now apply empty_union_1 in H.
  - destruct a. intro. intros.
    apply union_add in H.
    assert (add a (union (dom Γ2) (dom Γ1)) [<=] add a (dom (Γ1 , a0 : A ,, Γ2))).
    + apply subset_add_3. auto.
      apply subset_add_2. apply IHΓ2.
    + now apply H0.
Qed.

Theorem substitution : forall Γ1 Γ2 x A B e1 e2 e3,
  Γ1 , x : B ,, Γ2 ⊢ e1 <: e2 : A ->
  Γ1 ⊢ e3 : B -> mono_type e3 ->
  Γ1 ,, [e3 // x] Γ2 ⊢ [e3 / x] e1 <: [e3 / x] e2 : [e3 / x] A.
Proof.
  intros until e3. intros Hsub Hsub3 Mono.
  remember (Γ1 , x : B ,, Γ2) as Γ.
  generalize dependent HeqΓ.
  generalize x Γ2. clear x Γ2.
  apply sub_mut with
      (P := fun Γ e1 e2 A => fun (_ : Γ ⊢ e1 <: e2 : A) =>
         forall x Γ2, Γ = Γ1, x : B,, Γ2 ->
         Γ1 ,, [e3 // x] Γ2 ⊢ [e3 / x] e1 <: [e3 / x] e2 : [e3 / x] A)
      (P0 := fun Γ => fun (_ : ⊢ Γ) =>
         forall x Γ2, Γ = Γ1 , x : B,, Γ2 -> ⊢ Γ1 ,, [e3 // x] Γ2);
      simpl; intros; subst.
  - destruct (x == x0).
    + subst. assert (A0 = B) by (eapply binds_type_equal; eauto). subst.
      rewrite fresh_subst_eq. apply weakening_app; auto.
      apply prefix_wf in w. inversion w. subst.
      eapply fresh_ctx_fresh_expr; eauto.
    + apply s_var. auto.
      apply binds_subst with B; auto.
  - auto.
  - auto.
  - auto.
  - apply s_abs with (add x L) k.
    + auto.
    + intros. distribute_ctx. rewrite subst_ctx_distr_cons.
      repeat rewrite subst_open_var_assoc; auto 2.
  - apply s_pi with (add x L) k1.
    + auto.
    + auto.
    + auto.
    + intros. distribute_ctx. rewrite subst_ctx_distr_cons.
      repeat rewrite subst_open_var_assoc; auto 2.
    + intros. distribute_ctx. rewrite subst_ctx_distr_cons.
      repeat rewrite subst_open_var_assoc; auto 2.
  - rewrite subst_open_distr; auto.
    apply s_app with ([e3 / x] A0); auto.
  - apply s_forall with (add x L) k.
    + auto.
    + intros. distribute_ctx. rewrite subst_ctx_distr_cons.
      repeat rewrite subst_open_var_assoc; auto 2.
  - apply s_forall_l with (add x L) ([e3 / x] e) k.
    + now apply subst_mono; auto.
    + auto.
    + auto.
    + rewrite <- subst_open_distr; auto.
    + intros. distribute_ctx. rewrite subst_ctx_distr_cons.
      repeat rewrite subst_open_var_assoc; auto 2.
  - apply s_forall_r with (add x L) k.
    + auto.
    + auto.
    + intros. distribute_ctx. rewrite subst_ctx_distr_cons.
      repeat rewrite subst_open_var_assoc; auto 2.
  - apply s_forall_2 with (add x L) k.
    + auto.
    + intros. distribute_ctx. rewrite subst_ctx_distr_cons.
      repeat rewrite subst_open_var_assoc; auto 2.
  - eauto.

  - destruct Γ2; inversion H.
  - destruct Γ2; inversion H1; subst; simpl in *.
    + auto.
    + apply wf_cons with k; auto.
      rewrite dom_app. rewrite dom_subst_equal.
      intro. apply in_subset with (s2 := dom (Γ1 , x0 : B ,, Γ2)) in H2.
      contradiction.
      apply dom_insert_subset.
  - assumption.
Qed.

Theorem transitivity : forall e2 Γ e1 e3 A B,
  Γ ⊢ e1 <: e2 : A -> Γ ⊢ e2 <: e3 : B -> Γ ⊢ e1 <: e3 : A.
Proof.
Admitted.

Theorem type_consistency : forall Γ e1 e2 A B,
  Γ ⊢ e1 : A -> Γ ⊢ e1 <: e2 : B -> Γ ⊢ e1 <: e2 : A.
Proof.
Admitted.

Theorem type_correct : forall Γ A B C, Γ ⊢ A <: B : C -> Γ ⊢ C : *.
Proof.
Admitted.

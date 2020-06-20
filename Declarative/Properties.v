Require Import Declarative.BasicProperties.
Require Import Declarative.KindReasoning.
Require Import Declarative.OccurenceReasoning.
Require Import Declarative.FSetReasoning.
Require Import Extraction.

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

Lemma ctx_app_cons_assoc : forall (Γ1 Γ2 : context) x A,
    Γ1 ,, Γ2 , x : A = Γ1 ,, (Γ2 , x : A).
Proof.
  reflexivity.
Qed.

Hint Rewrite ctx_app_cons_assoc : reassoc.
Hint Rewrite subst_ctx_distr_cons : reassoc.
Hint Rewrite subst_open_var_assoc : reassoc.
Hint Rewrite subst_extract : reassoc.

Lemma dom_subst_equal : forall Γ x v,
    dom ([v // x] Γ) = dom Γ.
Proof.
  induction Γ; intros.
  + reflexivity.
  + destruct a. simpl. now rewrite (IHΓ x v).
Qed.

Local Ltac solve_substitution :=
  try solve
      [ auto
      | intros; autorewrite with reassoc;
        (auto 2 || eauto using fv_subst_inclusion)
      ].

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
  - pick fresh x' and apply s_abs; solve_substitution.
  - pick fresh x' and apply s_pi ; solve_substitution.
  - rewrite subst_open_distr; auto.
    apply s_app with ([e3 / x] A0); auto using subst_mono.
  - apply s_forall with (add x L `union` fv_eexpr (extract e3)) k;
      solve_substitution.
  - apply s_forall_l with (add x L) ([e3 / x] e) k;
      solve_substitution.
    + now apply subst_mono; auto.
    + rewrite <- subst_open_distr; auto.
  - pick fresh x' and apply s_forall_r; solve_substitution.
  - pick fresh x' and apply s_forall_2; solve_substitution.
  - eauto.

  - destruct Γ2; inversion H.
  - destruct Γ2; inversion H1; subst; simpl in *.
    + auto.
    + apply wf_cons with k; auto.
      rewrite dom_app. rewrite dom_subst_equal.
      eauto using dom_insert_subset.
  - assumption.
Qed.

Corollary substitution_cons : forall Γ x A B e1 e2 e3,
    Γ, x : B ⊢ e1 <: e2 : A ->
    Γ ⊢ e3 : B -> mono_type e3 ->
    Γ ⊢ [e3 / x] e1 <: [e3 / x] e2 : [e3 / x] A.
Proof.
  intros *.
  replace (Γ , x : B) with (Γ ,, one (pair x B) ,, nil) by reflexivity.
  intros.
  replace Γ with (Γ ,, [e3 // x] nil) by reflexivity.
  eapply substitution; simpl in *; eauto.
Qed.

Lemma ctx_type_correct : forall Γ x A,
    ⊢ Γ -> x : A ∈ Γ -> exists k, Γ ⊢ A : e_kind k.
Proof.
  intros * Wf.
  induction Wf; simpl; intros.
  - inversion H.
  - destruct H1.
    + inversion H1. subst.
      eauto.
    + destruct (IHWf H1) as [k0 IH].
      eauto.
Qed.

Theorem type_correctness : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> A = BOX \/ exists k, Γ ⊢ A : e_kind k.
Proof.
  intros * Sub.
  induction Sub; eauto 4.
  - eauto 3 using ctx_type_correct.
  - pick fresh x.
    destruct (H2 x Fr) as [H' | [k H']].
    + auto.
    + apply kind_sub_inversion_l in H' as (E1 & E2 & E3). subst. eauto.
  - destruct IHSub2 as [H0 | [k H0]]. inversion H0.
    dependent induction H0.
    + clear IHusub1 IHusub2 IHusub3 H0 H2.
      pick fresh x for (L `union` fv_expr B).
      assert (Fr2 : x `notin` L) by auto.
      specialize (H1 x Fr2).
      right. exists k.
      rewrite open_subst_eq with (x := x); auto.
      replace (e_kind k) with ([e / x] e_kind k) by reflexivity.
      eapply substitution_cons; eauto.
    + apply IHusub1 with A k; auto.
      apply kind_sub_inversion_l in H0_0 as (E1 & E2 & E3). now subst.
Qed.

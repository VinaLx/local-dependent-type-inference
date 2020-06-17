Require Export Declarative.Language.
Require Export List.
Require Export Program.Equality.

Export ListNotations.

Require Export Metalib.Metatheory.

Notation "G ⊢ e : A" := (usub G e e A)
    (at level 65, e at next level, no associativity) : type_scope.
Notation "G ⊢ e1 <: e2 : A" := (usub G e1 e2 A)
    (at level 65, e1 at next level, e2 at next level, no associativity) : type_scope.

Notation "e1 ⟶ e2"  := (reduce  e1 e2) (at level 60, no associativity) : type_scope.
Notation "e1 ⋆⟶ e2" := (ereduce e1 e2) (at level 60, no associativity) : type_scope.

Declare Scope ctx_scope.
Delimit Scope ctx_scope with ctx.
Bind Scope ctx_scope with context.

Declare Scope expr_scope.
Delimit Scope expr_scope with exp.
Bind Scope expr_scope with expr.

Declare Scope eexpr_scope.
Delimit Scope eexpr_scope with eexp.
Bind Scope eexpr_scope with eexpr.

Notation "*"  := (e_kind k_star) : expr_scope.
Notation "'BOX'" := (e_kind k_box) : expr_scope.

Notation "` x" := (e_var_f x)
    (at level 0, x at level 0, no associativity): expr_scope.

Notation "G , x : A" := ((x, A) :: G)
    (left associativity, at level 62, x at level 0) : ctx_scope.

Notation "G1 ,, G2" := (G2 ++ G1)
    (left associativity, at level 62) : ctx_scope.

Notation "⊢ G" := (wf_context G)
    (no associativity, at level 65) : type_scope.

Notation "x : A ∈ G" := (binds x A G)
    (no associativity, at level 65) : type_scope.

Notation "x # e" := (x `notin` fv_expr e)
    (no associativity, at level 65) : type_scope.

Notation "e < ^^ n > e' " := (open_expr_wrt_expr_rec n e' e)
    (at level 40, n at level 0, left associativity) : expr_scope.

Notation "e <^^> e'" :=
  (open_expr_wrt_expr e e')
    (at level 40, no associativity) : expr_scope.

Notation "e <^> x" := (open_expr_wrt_expr e (e_var_f x))
    (at level 40) : expr_scope.

Definition subst_ctx (e : expr) (x : exprvar) : context -> context :=
  map (subst_expr e x).

Notation "[ e1 / x ] e2" := (subst_expr e1 x e2)
    (at level 60, e1 at level 0,  x at level 0, right associativity) : expr_scope.
Notation "[ e // x ] ctx" := (subst_ctx e x ctx)
    (at level 60, e at level 0, x at level 0, right associativity) : ctx_scope.


Notation "e ⋆^^ e'" := (open_eexpr_wrt_eexpr e e') (at level 40, no associativity) : eexpr_scope.
Notation "e ⋆^ x" := (open_eexpr_wrt_eexpr e (ee_var_f x)) (at level 40) : eexpr_scope.
Notation "[ e1 ⋆/ x ] e2" := (subst_eexpr e1 x e2)
    (at level 60, e1 at level 0, x at level 0, right associativity) : eexpr_scope.
Notation "e ⋆ n ^^ e'" := (open_eexpr_wrt_eexpr_rec n e' e)
    (at level 40, n at level 0, no associativity) : eexpr_scope.

Open Scope eexpr_scope.
Open Scope ctx_scope.

Lemma binds__in_dom : forall t Γ x (A : t),
    x : A ∈ Γ -> x `in` dom Γ.
Proof.
  intros. induction Γ.
  - inversion H.
  - destruct a. destruct H.
    + inversion H. subst. simpl. auto.
    + simpl. auto.
Qed.

Lemma in_dom_insert : forall x Γ1 Γ2 (A : expr),
    x `in` dom (Γ1 , x : A ,, Γ2).
Proof.
  induction Γ2; intros.
  - simpl. auto.
  - destruct a. simpl. auto.
Qed.

Lemma binds_insert : forall Γ1 x (A : expr) Γ2,
   x : A ∈ Γ1 , x : A ,, Γ2.
Proof.
  induction Γ2; simpl.
  - auto.
  - destruct a. unfold binds. simpl. now right.
Qed.

Lemma binds_type_equal : forall Γ1 x A B Γ2,
    x : A ∈ Γ1 , x : B ,, Γ2 ->
    ⊢ Γ1 , x : B ,, Γ2 ->
    A = B.
Proof.
  unfold binds. intros. induction Γ2.
  - destruct H.
    + now inversion H.
    + inversion H0. subst.
      now apply binds__in_dom in H.
  - destruct a. destruct H.
    + inversion H. inversion H0. subst.
      now assert (x `in` dom (Γ1 , x : B ,, Γ2))
        by apply in_dom_insert.
    + inversion H0; auto.
Qed.

Lemma binds_type_not_equal : forall Γ1 x x' (A : expr) B C Γ2,
    x : A ∈ Γ1 , x' : B ,, Γ2 ->
    x' <> x ->
    x : A ∈ Γ1 , x' : C ,, Γ2.
Proof.
  intros.
  induction Γ2.
  - destruct H.
    + now inversion H.
    + auto.
  - destruct a. destruct H.
    + inversion H. subst. auto.
    + right. apply IHΓ2. assumption.
Qed.

Lemma binds_inversion : forall Γ x (A : expr),
    x : A ∈ Γ -> exists Γ1 Γ2, Γ = Γ1 , x : A ,, Γ2.
Proof.
  intros. induction Γ.
  - inversion H.
  - unfold binds in *. destruct a. destruct H.
    + inversion H. subst. exists Γ. exists []. reflexivity.
    + destruct IHΓ. assumption.
      destruct H0. subst.
      exists x0. exists (x1 , a : e). reflexivity.
Qed.

Theorem sub_ctx_wf : forall Γ e1 e2 A,
  Γ ⊢ e1 <: e2 : A -> ⊢ Γ.
Proof.
  intros. induction H; eauto.
Qed.

Ltac ctx_wf_auto :=
  match goal with
  | _ : ?G ⊢ _ <: _ : _ |- ⊢ ?G =>
    eapply sub_ctx_wf; eassumption
  end
.

Hint Extern 2 (⊢ _) => ctx_wf_auto : core.

Lemma prefix_wf : forall Γ1 Γ2, ⊢ Γ1 ,, Γ2 -> ⊢ Γ1.
Proof.
  intros. induction Γ2.
  - assumption.
  - inversion H. auto.
Qed.

Hint Resolve prefix_wf : core.

Lemma binds_consistent : forall Γ x A B,
    ⊢ Γ -> x : A ∈ Γ -> x : B ∈ Γ -> A = B.
Proof.
  intros.
  apply binds_inversion in H1 as [Γ1 [Γ2 E]]. subst.
  eapply binds_type_equal; eauto.
Qed.

Open Scope expr_scope.

Theorem wf_ctx_type_correct : forall Γ1 Γ2 x A,
  ⊢ Γ1 , x : A ,, Γ2 -> exists k, Γ1 ⊢ A : e_kind k.
Proof.
  induction Γ2; intros.
  - inversion H. now exists k.
  - inversion H. subst. now apply IHΓ2 with x.
Qed.

Lemma var_in_ctx_weakening : forall Γ2 Γ1 Γ3 x (A : expr),
    x : A ∈ Γ1 ,, Γ3 ->
    x : A ∈ Γ1 ,, Γ2 ,, Γ3.
Proof.
  intros. apply binds_app_1 in H as [H | H].
  - auto.
  - rewrite <- app_assoc in *.
    now apply binds_app_3.
Qed.

Theorem fresh_open_rec : forall x e1 e2 n,
  x # e1 -> x # e2 -> x # open_expr_wrt_expr_rec n e2 e1.
Proof.
  intros x e1.
  induction e1; simpl; intros e2 n' Hfresh1 Hfresh2; eauto.
  - now destruct (n' == n).
Qed.

Corollary fresh_open : forall x e1 e2,
  x # e1 -> x # e2 -> x # open_expr_wrt_expr e1 e2.
Proof.
  intros. now apply fresh_open_rec.
Qed.

Corollary fresh_open_var : forall x e y,
  x # e -> x <> y -> x # open_expr_wrt_expr e (e_var_f y).
Proof.
  intros. apply fresh_open.
  + auto.
  + simpl. apply notin_singleton_2. intro.
    symmetry in H1. contradiction.
Qed.

Theorem fresh_close_rec : forall e1 e2 x n,
    x # open_expr_wrt_expr_rec n e2 e1 -> x # e1.
Proof.
  induction e1; intros; simpl in *; eauto.
Qed.

Theorem fresh_close : forall e1 e2 x,
    x # e1 <^^> e2 -> x # e1.
Proof.
  intros until x. apply fresh_close_rec.
Qed.

Hint Resolve fresh_open_var : core.
Hint Resolve fresh_close : core.

Scheme sub_mut := Induction for usub       Sort Prop
  with  wf_mut := Induction for wf_context Sort Prop.

Fixpoint context_fresh (x : atom) (ctx : context) : Prop :=
  match ctx with
  | nil => True
  | ((pair y t) :: ctx') => x # t /\ context_fresh x ctx'
  end
.

Hint Unfold context_fresh : core.

Ltac distribute_ctx :=
  match goal with
  | |- (?g1 ,, ?g2 , ?x : ?A) ⊢ _ <: _ : _ =>
    replace (g1 ,, g2 , x : A) with
      (g1 ,, (g2 , x : A)) by auto
  end
.

Hint Extern 1 (_ ,, _ , _ : _ ⊢ _ <: _ : _) => distribute_ctx : core.

Lemma open_rec_eq_cancel : forall e e1 e2 m n,
    m <> n -> e <^^m> e1 <^^n> e2 = e <^^m> e1 ->
    e <^^n> e2 = e.
Proof.
  induction e; simpl; intros; auto;
    try solve
      [inversion H0; apply IHe1 in H2; auto; apply IHe2 in H3; auto; congruence].
  - destruct (m == n).
    + destruct (n0 == n); congruence.
    + simpl in H0. destruct (n0 == n); easy.
Qed.

Hint Resolve open_rec_eq_cancel : ln.

Lemma lc_open_eq : forall e,
    lc_expr e -> forall n e', e <^^n> e' = e.
Proof.
  intros e LC. induction LC; simpl; intros; auto;
    try solve
        [ pick fresh x; rewrite IHLC;
          erewrite open_rec_eq_cancel with (m := 0); eauto].
  - now (rewrite IHLC1; rewrite IHLC2).
Qed.

Lemma subst_open_rec_distr : forall e x v e' n,
    lc_expr v ->
    [v / x] e <^^n> e' = ([v / x] e) <^^n> ([v / x] e').
Proof.
  induction e; simpl; intros; auto;
    try solve [rewrite IHe1; auto; rewrite IHe2; auto].
  - destruct (n0 == n); auto.
  - destruct (x == x0). rewrite lc_open_eq; auto. auto.
Qed.

Lemma subst_open_distr : forall e x v e',
    lc_expr v ->
    [v / x] e <^^> e' = ([v / x] e) <^^> ([v / x] e').
Proof.
  intros. unfold open_expr_wrt_expr. now rewrite subst_open_rec_distr.
Qed.

Lemma subst_open_var_assoc : forall e x v y,
    y <> x -> lc_expr v ->
    ([v / x] e) <^> y = [v / x] e <^> y.
Proof.
  intros.
  assert ([v / x] e <^> y = ([v / x] e) <^^> ([v / x] `y))
    by now apply subst_open_distr.
  assert ([v / x] `y = `y) by (simpl; destruct (y == x); easy).
  now rewrite H2 in H1.
Qed.

Lemma fresh_subst_eq : forall e x e', x # e -> [e' / x] e = e.
Proof.
  induction e; simpl; intros;
    try solve [auto | rewrite IHe1; auto; rewrite IHe2; auto].
  - destruct (x == x0).
    + apply notin_singleton_1 in H. contradiction.
    + auto.
Qed.

Lemma open_subst_eq : forall e x v,
    x # e -> lc_expr v ->
    e <^^> v = [v / x] e <^> x.
Proof.
  intros.
  rewrite subst_open_distr. simpl.
  rewrite eq_dec_refl.
  rewrite fresh_subst_eq.
  all: easy.
Qed.


Lemma lc_subst : forall e v x,
    lc_expr e -> lc_expr v -> lc_expr ([v / x] e).
Proof.
  intros. induction H; simpl; auto.
  - destruct (x0 == x); auto.

  Ltac solve_inductive_case_with C :=
    let L := gather_atoms in
    apply C with L; auto; intros; rewrite subst_open_var_assoc; auto.

  - solve_inductive_case_with lc_e_abs.
  - solve_inductive_case_with lc_e_pi.
  - solve_inductive_case_with lc_e_all.
  - solve_inductive_case_with lc_e_bind.
Qed.

Lemma lc_open_preserve : forall e e',
    (exists L, forall x, x `notin` L -> lc_expr (e <^> x)) ->
    lc_expr e' -> lc_expr (e <^^> e').
Proof.
  intros e e' [L H] H'.
  pick fresh x for (fv_expr e `union` L).
  assert (x # e) by auto.
  rewrite (open_subst_eq _ _ _ H0 H').
  apply lc_subst; auto.
Qed.


Fixpoint lc_ctx (c : context) : Prop :=
  match c with
  | nil => True
  | c', x : A => lc_expr A /\ lc_ctx c'
  end
.

Import Program.Tactics.

Ltac destruct_all_with x :=
  match goal with
  | H : forall x', x' `notin` ?L -> ?A /\ ?B |- _ =>
    let H1 := fresh in
    let H2 := fresh in
    destruct H with x' as [H1 H2]; try assumption; clear H; destruct_all_with x
  | _ => destruct_pairs
  end
.

Lemma usub_lc : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> lc_expr e1 /\ lc_expr e2 /\ lc_expr A.
Proof.
  intros.
  apply sub_mut with
      (P := fun c e1 e2 A (_ : c ⊢ e1 <: e2 : A) =>
        lc_expr e1 /\ lc_expr e2 /\ lc_expr A)
      (P0 := fun c (_ : ⊢ c) => lc_ctx c) (c := Γ); simpl; intros;
    destruct_pairs; repeat split; auto;
      try solve [econstructor; auto; intros; destruct_all_with x; auto].
  - induction G. inversion b.
    destruct a. destruct H0. inversion w. subst. destruct b.
    + inversion H2. now subst.
    + now apply IHG.
  - inversion H3; subst.
    apply lc_open_preserve; eauto.
Qed.

Lemma mono_lc : forall e,
    mono_type e -> lc_expr e.
Proof.
  intros. induction H; eauto.
Qed.

Ltac solve_basic_lc :=
  match goal with
  | H : _ ⊢ ?e <: _ : _ |- lc_expr ?e => apply usub_lc in H
  | H : _ ⊢ _ <: ?e : _ |- lc_expr ?e => apply usub_lc in H
  | H : _ ⊢ _ <: _ : ?e |- lc_expr ?e => apply usub_lc in H
  | H : mono_type ?e |- lc_expr ?e => now apply mono_lc
  end; destruct_pairs; assumption
.

Hint Extern 1 (lc_expr _) => solve_basic_lc : core.

Lemma lc_abs_param_l : forall Γ A b1 e T,
    Γ ⊢ e_abs A b1 <: e : T -> lc_expr A.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma lc_bind_param_l : forall Γ A b1 e T,
    Γ ⊢ e_bind A b1 <: e : T -> lc_expr A.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma lc_abs_param_r : forall Γ A b2 e T,
    Γ ⊢ e <: e_abs A b2 : T -> lc_expr A.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma lc_bind_param_r : forall Γ A b2 e T,
    Γ ⊢ e <: e_bind A b2 : T -> lc_expr A.
Proof.
  intros. dependent induction H; eauto.
Qed.

Ltac solve_more_lc :=
  match goal with
  | H : _ ⊢ e_abs ?A _ <: _ : _ |- lc_expr ?A => apply lc_abs_param_l in H
  | H : _ ⊢ _ <: e_abs ?A _ : _ |- lc_expr ?A => apply lc_abs_param_r in H
  | H : _ ⊢ e_bind ?A _ <: _ : _ |- lc_expr ?A => apply lc_bind_param_l in H
  | H : _ ⊢ _ <: e_bind ?A _ : _ |- lc_expr ?A => apply lc_bind_param_r in H
  end; assumption
.

Hint Extern 1 (lc_expr _) => solve_more_lc : core.

Lemma subst_mono : forall e x e',
    mono_type e -> mono_type e' -> mono_type ([e' / x] e).
Proof.
  intros.
  induction H; simpl; auto.
  (* var *)
  - destruct (x0 == x); auto.
  - apply mono_pi with (add x L).
    + assumption.
    + intros. rewrite subst_open_var_assoc.
      apply H2. all: auto.
  - apply mono_lambda with (add x L).
    + assumption.
    + intros. rewrite subst_open_var_assoc.
      apply H2. all: auto.
  - apply mono_bind with (add x L).
    + assumption.
    + intros. rewrite subst_open_var_assoc.
      apply H2. all: auto.
Qed.

Ltac instantiate_colimits :=
  match goal with
  | Fr : ?x `notin` ?L1 |- _ => repeat
    match goal with
    | H : forall x, x `notin` ?L2 -> _ |- _ =>
      let H2 := fresh "H" in
      assert (H2 : x `notin` L2) by eauto;
      specialize (H x H2);
      clear H2
    end
  end
.

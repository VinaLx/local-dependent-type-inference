Require Export Declarative.Language.
Require Export List.
Require Import Program.Equality.
Import ListNotations.

Require Export Metalib.Metatheory.

Notation "G ⊢ e : A" := (usub G e e A)
    (at level 65, e at next level, no associativity) : type_scope.
Notation "G ⊢ e1 <: e2 : A" := (usub G e1 e2 A)
    (at level 65, e1 at next level, e2 at next level, no associativity) : type_scope.

Declare Scope ctx_scope.
Delimit Scope ctx_scope with ctx.
Bind Scope ctx_scope with context.

Declare Scope expr_scope.
Delimit Scope expr_scope with exp.
Bind Scope expr_scope with expr.

Notation "*" := (e_star) : expr_scope.

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

Notation "e <^^> x" := (open_expr_wrt_expr e x)
    (at level 40) : expr_scope.
Notation "e <^> x" := (open_expr_wrt_expr e (e_var_f x))
    (at level 40) : expr_scope.

Definition subst_context (x : exprvar) (e : expr) : context -> context :=
  map (subst_expr e x).

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

Hint Extern 2 (⊢ _) => ctx_wf_auto.

Open Scope expr_scope.
Open Scope ctx_scope.

Theorem wf_ctx_type_correct : forall Γ1 Γ2 x A,
  ⊢ Γ1 , x : A ,, Γ2 -> Γ1 ⊢ A : *.
Proof.
  induction Γ2; intros.
  - inversion H. assumption.
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
  | [] => True
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

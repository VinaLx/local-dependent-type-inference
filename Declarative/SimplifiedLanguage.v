Require Import LanguageUtil.
Require Import BasicProperties.
Require Import Properties.

Notation "G ⊨ e : A" := (susub G e e A)
    (at level 65, e at next level, no associativity) : type_scope.
Notation "G ⊨ e1 <: e2 : A" := (susub G e1 e2 A)
    (at level 65, e1 at next level, e2 at next level, no associativity) : type_scope.

Notation "⊨ G" := (swf_context G)
    (no associativity, at level 65) : type_scope.


(*
Theorem soundness : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> Γ ⊨ e1 <: e2 : A
  with
    wf_soundness : forall Γ, ⊢ Γ -> ⊨ Γ.
Proof.
  - intros * Sub. destruct Sub;
    try solve [clear soundness; constructor; auto | econstructor; eauto 3 ].
  - intros * Wf. destruct Wf.
    + constructor.
    + econstructor; eauto.
Qed.


Ltac auto_instantiate_cofinite H :=
  match goal with
  | x : atom |- _ =>
    match goal with
    | Fr : x `notin` ?L |- _ => instantiate_cofinite x H
    end
  | _ =>
    let x := fresh "x" in
    pick fresh x; instantiate_cofinite x H
  end
.

Ltac conclude_typing_in_binding H :=
  match type of H with
  | forall x, x `notin` ?L -> ?G, x : ?A ⊨ _ <: _ : _ =>
    match goal with
    | _ : _ ⊢ A <: _ : _ |- _ => idtac
    | _ : _ ⊢ _ <: A : _ |- _ => idtac
    | _ =>
      let H1 := fresh "H" in
      pose proof H as H1;
      auto_instantiate_cofinite H1;
      let H2 := fresh "H" in
      let k := fresh "k" in
      assert (exists k, G ⊢ A : e_kind k) as [k H2] by eauto 4;
      clear H1
    end
  end
.

Ltac conclude_typing_in_bindings :=
  repeat
    match goal with
    | H : forall x, x `notin` ?L -> ?G , x : ?A ⊨ _ <: _ : _ |- _ =>
      progress conclude_typing_in_binding H
    end
.

Lemma wf_ctx_type_correct_cons : forall Γ x A,
    ⊢ Γ, x : A -> exists k, Γ ⊢ A : e_kind k.
Proof.
  intros. inversion H; subst; eauto.
Qed.

Hint Resolve wf_ctx_type_correct_cons : core.
Hint Resolve sub_ctx_wf : core.

Theorem completeness : forall Γ e1 e2 A,
    Γ ⊨ e1 <: e2 : A -> Γ ⊢ e1 <: e2 : A
  with
    wf_completeness : forall Γ, ⊨ Γ -> ⊢ Γ.
Proof.
  - intros * Sub. destruct Sub;
    try solve [ clear completeness; constructor; auto
              | conclude_typing_in_bindings; econstructor; eauto 3].
    + apply completeness in Sub.
      econstructor; eauto 3.
  - intros * Wf. destruct Wf.
    + constructor.
    + econstructor; eauto.
Qed.
*)

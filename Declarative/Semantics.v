Require Import LanguageUtil.
Require Import BasicProperties.
Require Import Properties.
Require Import Transitivity.
Require Import Extraction.
Require Import KindReasoning.
Require Import OccurenceReasoning.

Require Import Program.Tactics.

Definition Progressive (e : expr) : Prop := value e \/ exists e', e ⟶ e'.
Definition EProgressive (e : eexpr) := evalue e \/ exists e', e ⋆⟶ e'.

Hint Unfold Progressive : core.
Hint Unfold EProgressive : core.

Hint Rewrite extract_open_distr : reassoc.

Ltac find_impossible_reduction :=
  simpl in *;
  match goal with
  | _ : ee_app _ _ ⋆⟶ _ |- _ => fail
  | _ : e_app  _ _ ⟶  _ |- _ => fail
  | _ : e_app _ _ ⟹ _ |- _ => fail
  | H : _ ⋆⟶ _ |- _ => solve [inversion H]
  | H : _ ⟶  _ |- _ => solve [inversion H]
  | H : _ ⟹ _ |- _ => solve [inversion H]
  end
.

Ltac solve_impossible_reduction := try find_impossible_reduction.

Lemma head_kind_box_impossible : forall Γ e1 e2 A n,
    Γ ⊢ e1 <: e2 : A -> head_kind A k_box n -> A = BOX \/ False.
Proof.
  intros.
  apply type_correctness in H.
  destruct H as [E | (k & Sub)].
  + auto.
  + eauto using head_kind_box_never_welltype.
Qed.

Lemma pi_head_box_impossible : forall Γ e1 e2 A,
    not (Γ ⊢ e1 <: e2 : e_pi A BOX).
Proof.
  intros. intro. eapply head_kind_box_impossible in H.
  - destruct H. inversion H. auto.
  - constructor. apply h_kind. Unshelve. exact 0.
Qed.

Ltac solve_open_is_box :=
  repeat
    match goal with
    | H : _ ^^ _ = BOX |- _ => apply open_is_box in H as [|]; subst
    | H : _ ⊢ _ <: _ : e_pi _ BOX |- _ => contradict H; apply pi_head_box_impossible
    | _ => solve [box_welltype_contradiction]
    end
.

Lemma box_only_head_kind_star : forall Γ e,
    Γ ⊢ e : BOX -> exists n, head_kind e k_star n.
Proof.
  intros.
  dependent induction H; box_welltype_contradiction; instantiate_cofinites.
  (* star *)
  - exists 0. eauto.
  (* pi *)
  - instantiate_trivial_equals.
    destruct H1. apply head_kind_invert_subst_var in H1. eauto.
  (* app impossible *)
  - solve_open_is_box.
Qed.

Lemma box_never_reduce : forall Γ e,
    Γ ⊢ e : BOX -> forall e', not (e ⟹ e').
Proof.
  intros * Sub.
  dependent induction Sub; intros; intro;
    solve_impossible_reduction.
  - solve_open_is_box.
  - box_welltype_contradiction.
  - box_welltype_contradiction.
Qed.

Lemma app_inversion : forall Γ f a A,
    Γ ⊢ e_app f a : A ->
    exists B C k, Γ ⊢ f : e_pi B C /\ Γ ⊢ a : B /\ Γ ⊢ C ^^ a <: A : e_kind k.
Proof.
  intros.
  dependent induction H.
  - assert (G ⊢ e_app f a : B ^^ a) by eauto.
    apply type_correctness in H2 as [|[]].
    + solve_open_is_box.
    + exists A, B, x. auto.
  - edestruct IHusub1 as (B' & C' & k' & H1 & H2 & H3); eauto.
    exists B', C', k'. eauto using transitivity.
Qed.

Ltac conclude_type_refl H :=
  match type of H with
  | ?G ⊢ _ <: _ : ?A =>
    let k := fresh "k" in
    let H := fresh "H" in
    let EBox := fresh "Ebox" in
    assert (A = BOX \/ exists k, G ⊢ A : e_kind k) as [Ebox | [k H]]
        by (eapply type_correctness; eassumption);
    [inversion EBox; subst |]
  end
.

Ltac conclude_refls H :=
  match type of H with
  | ?G ⊢ ?e1 <: ?e2 : ?A =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    assert (H1 : G ⊢ e1 : A) by eauto;
    assert (H2 : G ⊢ e2 : A) by eauto;
    conclude_type_refl H
  end
.

Lemma abs_pi_principal : forall Γ A b1 b2 T,
    Γ ⊢ e_abs A b1 <: e_abs A b2 : T ->
    exists B k, Γ ⊢ e_abs A b1 <: e_abs A b2 : e_pi A B /\ Γ ⊢ e_pi A B <: T : e_kind k.
Proof.
  intros.
  dependent induction H.
  - assert (Sub : G ⊢ e_abs A b1 <: e_abs A b2 : e_pi A B) by eauto.
    conclude_type_refl Sub. eauto.
  - edestruct IHusub1 as (B' & k' & Sub & Subpi); eauto.
    exists B', k'. split.
    + assumption.
    + eapply transitivity; eauto.
Qed.


Lemma pi_sub_inversion : forall Γ A B C D k,
    Γ ⊢ e_pi A B <: e_pi C D : e_kind k ->
    exists k' L,
      Γ ⊢ C <: A : e_kind k' /\
      forall x, x `notin` L -> Γ, x : C ⊢ B ^` x <: D ^` x : e_kind k.
Proof.
  intros.
  dependent induction H.
  - exists k1, L. auto.
  - apply IHusub1; auto.
    apply kind_sub_inversion_l in H0. destruct_pairs. congruence.
Qed.

Lemma abs_inversion : forall Γ A b1 b2 T,
    Γ ⊢ e_abs A b1 <: e_abs A b2 : T ->
    forall B k,
    Γ ⊢ T <: e_pi A B : e_kind k ->
    exists L, forall x, x `notin` L -> Γ, x : A ⊢ b1 ^` x <: b2 ^` x : B ^` x.
Proof.
  intros * Sub.
  dependent induction Sub; intros.
  - apply pi_sub_inversion in H3 as (k' & L' & H').
    exists (L `union` L'). intros.
    destruct_pairs. instantiate_cofinites. eauto.
  - apply IHSub1 with k; eauto using transitivity.
Qed.

Lemma abs_principal_inversion : forall Γ A b1 b2 B,
    Γ ⊢ e_abs A b1 <: e_abs A b2 : e_pi A B ->
    exists L, forall x, x `notin` L -> Γ, x : A ⊢ b1 ^` x <: b2 ^` x : B ^` x.
Proof.
  intros.
  conclude_type_refl H.
  now apply abs_inversion with (e_pi A B) k.
Qed.

Lemma castdn_inversion : forall Γ e1 e2 A B,
    Γ ⊢ e_castdn A e1 <: e_castdn A e2 : B ->
    exists C k, Γ ⊢ e1 <: e2 : C /\ C ⟹ A /\ Γ ⊢ A <: B : e_kind k.
Proof.
  intros. dependent induction H.
  - eauto.
  - edestruct IHusub1 as (C & k1 & Sub1 & R & Sub2); eauto.
    exists C, k1. eauto using transitivity.
Qed.

Lemma castup_inversion : forall Γ e1 e2 A B,
    Γ ⊢ e_castup A e1 <: e_castup A e2 : B ->
    exists C k, Γ ⊢ e1 <: e2 : C /\ A ⟹ C /\ Γ ⊢ A <: B : e_kind k.
Proof.
  intros. dependent induction H.
  - eauto.
  - edestruct IHusub1 as (C & k1 & Sub1 & R & Sub2); eauto.
    exists C, k1; eauto using transitivity.
Qed.

Lemma castup_box_never_welltype : forall Γ A B,
    not (Γ ⊢ e_castup A BOX : B).
Proof.
  intros. intro.
  dependent induction H.
  - box_welltype_contradiction.
  - eauto.
Qed.

Lemma app_box_never_welltype : forall Γ f1 f2 A,
    not (Γ ⊢ e_app f1 BOX <: e_app f2 BOX : A).
Proof.
  intros. intro.
  dependent induction H.
  - box_welltype_contradiction.
  - eauto.
Qed.

Lemma lambda_box_never_welltype : forall Γ A B,
    not (Γ ⊢ e_abs A BOX : B).
Proof.
  intros. intro.
  dependent induction H.
  - instantiate_cofinites. unfold open_expr_wrt_expr in *. simpl in *.
    box_welltype_contradiction.
  - eauto.
Qed.

Lemma app_of_box_impossible : forall Γ e1 e2 e,
    not (Γ ⊢ e_app e1 e <: e_app e2 e : BOX).
Proof.
  intros. intro.
  inversion H; subst.
  - solve_open_is_box.
  - box_welltype_contradiction.
Qed.

Lemma castdn_of_box_impossible : forall Γ A e1 e2,
    not (Γ ⊢ e_castdn A e1 <: e_castdn A e2 : BOX).
Proof.
  intros. intro.
  inversion H; box_welltype_contradiction.
Qed.

Ltac find_typing_refl_of e H1 :=
  match goal with
  | H : _ ⊢ e : _ |- _ => rename H into H1
  | H : _ ⊢ e <: _ : _ |- _ =>
    pose proof H as H1; apply reflexivity_l in H1
  | H : _ ⊢ _ <: e : _ |- _ =>
    pose proof H as H1; apply reflexivity_r in H1
  end
.

Ltac conclude_head_kind_of e H := repeat
  match goal with
  | _ : head_kind  e _ _ |- _ => fail 1
  | _ : head_kind' e _   |- _ => fail 1
  | _ =>
    match goal with
    | H1 : _ ⊢ e : BOX |- _ =>
      let n := fresh "n" in
      apply box_only_head_kind_star in H1 as [n H]
    | H1 : _ ⊢ e <: _ : BOX |- _ =>
      pose proof H1 as H; apply reflexivity_l in H
    | H1 : _ ⊢ _ <: e : BOX |- _ =>
      pose proof H1 as H; apply reflexivity_r in H
    end
  end
.


Ltac box_reasoning :=
  repeat
    progress match goal with
    (* base cases *)
    | _ =>
      solve [box_welltype_contradiction]
    | H : _ ⊢ _ <: _ : e_pi BOX _ |- _ =>
      apply pi_box_impossible in H; contradiction
    | H : _ ⊢ e_app ?e1 ?e <: e_app ?e2 ?e : BOX |- _ =>
      apply app_of_box_impossible in H; contradiction
    | H : _ ⊢ e_castup _ BOX : _ |- _ =>
      apply castup_box_never_welltype in H; contradiction
    | H : _ ⊢ e_app _ BOX <: e_app _ BOX : _ |- _ =>
      apply app_box_never_welltype in H; contradiction
    | H : _ ⊢ e_abs _ BOX : _ |- _ =>
      apply lambda_box_never_welltype in H; contradiction
    | H : _ ⊢ e_castdn ?A _ <: e_castdn ?A _ : BOX |- _ =>
      apply castdn_of_box_impossible in H;  contradiction
    (* reasoning *)
    | H1 : head_kind ?e k_star _ |- _ =>
      match goal with
      | _ : _ ⊢ e      : BOX |- _ => fail 1
      | _ : _ ⊢ e ^` _ : BOX |- _ => fail 1
      | _ : _ ⊢ e : ?A |- _ =>
        let E := fresh "E" in
        assert (E : A = BOX) by eauto using head_kind_star_of_box;
        discharge_equality E
      | H : _ ⊢ e <: _ : _ |- _ => apply reflexivity_l in H
      | H : _ ⊢ _ <: e : _ |- _ => apply reflexivity_r in H
      | _ : _ ⊢ e ^` ?x : _ |- _ => apply head_kind_subst_var with (x := x) in H1
      end
    | H1 : head_kind ?e k_box _ |- _ =>
      let H2 := fresh H1 in
      find_typing_refl_of e H2;
      eapply head_kind_box_never_welltype in H2; [easy | eauto]
    | H : head_kind (?e1 ^^ ?e2) _ _ |- _ =>
      apply head_kind_invert_subst in H as [H | H]; try solve [inversion H]
    | E : ?e ^` _ = BOX |- _ =>
      apply open_var_is_box in E; discharge_equality E
    | E : ?e1 ^^ ?e2 = BOX |- _ =>
      apply open_is_box in E as [E | E]; discharge_equality E
    | H : _ ⊢ ?e : BOX |- _ => conclude_head_kind_of e H
    | H : _ ⊢ ?e1 <: ?e2 : BOX |- _ =>
      match goal with
      | _ =>
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        conclude_head_kind_of e1 H1; conclude_head_kind_of e2 H2
      end
    end
.

Lemma box_never_be_reduced : forall e' e,
    e' ⟹ e -> forall Γ A, Γ ⊢ e : BOX -> forall Γ', Γ' ⊢ e' : A -> False.
Proof.
  intros * R.
  induction R; intros.
  - box_reasoning.
  - apply app_inversion in H3 as (B & C & k & Sub1 & Sub2 & Sub3).
    box_reasoning.
    + apply abs_pi_principal in Sub1 as (B' & k1 & Sub1 & Sub5).
      eapply abs_inversion in Sub1 as (L & Sub4); eauto.
      apply pi_sub_inversion in Sub5 as (k2 & L' & Sub6 & Sub7).
      instantiate_cofinites.
      box_reasoning.
  - box_reasoning.
  - apply castdn_inversion in H3 as (C & k1 & Sub1 & R1 & Sub2).
    apply castup_inversion in Sub1 as (D & k2 & Sub3 & R2 & Sub4).
    box_reasoning.
    apply reflexivity_l in Sub4.
    inversion R2; subst.
    + box_reasoning.
      apply app_inversion in Sub4 as (B' & C' & k & Sub5 & _).
      now apply lambda_box_never_welltype in Sub5.
    + apply castdn_inversion in Sub4 as (C' & k3 & Sub5 & _ & _).
      now apply castup_box_never_welltype in Sub5.
Qed.

Lemma castdn_not_of_star : forall Γ A e,
    Γ ⊢ e_castdn A e : * -> False.
Proof.
  intros.
  dependent induction H.
  - assert (e_kind k = BOX) by (eapply star_type_inversion; eauto). inversion H2; subst.
    conclude_type_refl H1.
    + inversion H0.
    + eauto using box_never_be_reduced.
  - apply star_sub_inversion_l in H0. subst.
    eapply IHusub1; eauto.
Qed.

Lemma castup_not_of_star : forall Γ A e,
    Γ ⊢ e_castup A e : * -> False.
Proof.
  intros.
  dependent induction H.
  - inversion H0.
  - apply star_sub_inversion_l in H0. subst.
    eapply IHusub1; eauto.
Qed.

Lemma abs_le : forall Γ A b e T,
    Γ ⊢ e_abs A b <: e : T ->
    exists c, e = e_abs A c.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - now apply abs_not_of_star in H0.
  - now eapply IHusub1.
Qed.

Lemma abs_ge : forall Γ A b e T,
    Γ ⊢ e <: e_abs A b : T ->
    exists c, e = e_abs A c.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - apply reflexivity_r in H2.
    now apply abs_not_of_star in H2.
  - now eapply IHusub1.
Qed.

Lemma bind_le : forall Γ A b e T,
    Γ ⊢ e_bind A b <: e : T ->
    exists c, e = e_bind A c.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - now apply bind_not_of_star in H0.
  - now eapply IHusub1.
Qed.

Lemma bind_ge : forall Γ A b e T,
    Γ ⊢ e <: e_bind A b : T ->
    exists c, e = e_bind A c.
Proof.
  intros. dependent induction H.
  - eauto.
  - apply reflexivity_r in H2. now apply bind_not_of_star in H2.
  - now eapply IHusub1.
Qed.

Lemma castup_le : forall Γ A b e T,
    Γ ⊢ e_castup A b <: e : T ->
    exists c, e = e_castup A c.
Proof.
  intros. dependent induction H.
  - eauto.
  - now apply castup_not_of_star in H0.
  - now eapply IHusub1.
Qed.

Lemma castup_ge : forall Γ A b e T,
    Γ ⊢ e <: e_castup A b : T ->
    exists c, e = e_castup A c.
Proof.
  intros. dependent induction H.
  - eauto.
  - apply reflexivity_r in H2. now apply castup_not_of_star in H2.
  - now eapply IHusub1.
Qed.

Lemma castdn_le : forall Γ A b e T,
    Γ ⊢ e_castdn A b <: e : T ->
    exists c, e = e_castdn A c.
Proof.
  intros. dependent induction H.
  - eauto.
  - now apply castdn_not_of_star in H0.
  - now eapply IHusub1.
Qed.

Lemma castdn_ge : forall Γ A b e T,
    Γ ⊢ e <: e_castdn A b : T ->
    exists c, e = e_castdn A c.
Proof.
  intros. dependent induction H.
  - eauto.
  - apply reflexivity_r in H2. now apply castdn_not_of_star in H2.
  - now eapply IHusub1.
Qed.


Ltac invert_sub_hyp :=
  let b := fresh "b" in
  let E := fresh "E" in
  let H' := fresh "H" in
  match goal with
  | _ : _ ⊢ e_abs    ?A _ <: e_abs    ?A _ : _ |- _ => idtac
  | _ : _ ⊢ e_bind   ?A _ <: e_bind   ?A _ : _ |- _ => idtac
  | _ : _ ⊢ e_castdn ?A _ <: e_castdn ?A _ : _ |- _ => idtac
  | _ : _ ⊢ e_castup ?A _ <: e_castup ?A _ : _ |- _ => idtac
  | H : _ ⊢ e_abs _ _ <: _ : _ |- _ =>
    pose (H' := H); apply abs_le in H' as (b & E)
  | H : _ ⊢ _ <: e_abs _ _ : _ |- _ =>
    pose (H' := H); apply abs_ge in H' as (b & E)
  | H : _ ⊢ e_bind _ _ <: _ : _ |- _ =>
    pose (H' := H); apply bind_le in H' as (b & E)
  | H : _ ⊢ _ <: e_bind _ _ : _ |- _ =>
    pose (H' := H); apply bind_ge in H' as (b & E)
  | H : _ ⊢ e_castup _ _ <: _ : _ |- _ =>
    pose (H' := H); apply castup_le in H' as (b & E)
  | H : _ ⊢ _ <: e_castup _ _ : _ |- _ =>
    pose (H' := H); apply castup_ge in H' as (b & E)
  | H : _ ⊢ e_castdn _ _ <: _ : _ |- _ =>
    pose (H' := H); apply castdn_le in H' as (b & E)
  | H : _ ⊢ _ <: e_castdn _ _ : _ |- _ =>
    pose (H' := H); apply castdn_ge in H' as (b & E)
  end; inversion E; subst; simpl in *
.

Lemma type_preservation' : forall Γ e1 e2 A,
    Γ ⊢ e1 <: e2 : A -> forall k n e1' e2', head_kind A k n -> e1 ⟹ e1' -> e2 ⟹ e2' -> Γ ⊢ e1' <: e2' : A.
Proof.
  intros * Sub.
  induction Sub; intros k' n' e1' e2' K R1 R2;
    try solve [inversion K | inversion R1 | inversion R2].
  - inversion R1; inversion R2; subst.
    + box_reasoning.
      * destruct k'; box_reasoning.
      * conclude_type_refl Sub2.
        apply s_app with A; auto.
        eapply IHSub2; eauto.
    + invert_sub_hyp. solve_impossible_reduction.
    + invert_sub_hyp. solve_impossible_reduction.
    + invert_sub_hyp.
      box_reasoning.
      * destruct k'; box_reasoning.
      * apply abs_pi_principal in Sub2 as (B' & k2 & Sub2 & Sub3).
        apply pi_sub_inversion in Sub3 as (k3 & L2 & Sub3 & Sub4).
        apply abs_principal_inversion in Sub2 as (L3 & Sub2).
        pick fresh x for (L3 `union` L2 `union` fv_expr b `union` fv_expr e0 `union` fv_expr B).
        instantiate_cofinites.
        rewrite (open_subst_eq b x e), (open_subst_eq e0 x e), (open_subst_eq B x e); auto.
        eauto 4 using substitution_cons, ctx_narrowing_cons.
  - conclude_type_refl Sub2. inversion H.
    destruct k'; box_reasoning.
    eapply box_never_be_reduced in H; [contradiction | eauto ..].
  - assert (head_kind A k' n') by (eapply head_kind_sub_l; eauto).
    eauto.
Qed.

Corollary type_preservation : forall Γ e1 e2 e1' e2' k,
    Γ ⊢ e1 <: e2 : e_kind k -> e1 ⟹ e1' -> e2 ⟹ e2' -> Γ ⊢ e1' <: e2' : e_kind k.
Proof.
  intros.
  eapply type_preservation'; eauto.
  Unshelve. exact 0.
Qed.

Hint Extern 1 (lc_expr _) => instantiate_cofinites : inst.

Ltac cleanup_hyps := instantiate_trivial_equals; destruct_pairs; clear_dups.
Ltac solve_progress_value := auto || left; eauto with inst.

Lemma pi_ge_inversion : forall Γ e A B k,
    Γ ⊢ e <: e_pi A B : k -> (exists A' B', e = e_pi A' B') \/ (exists C' D', e = e_all C' D').
Proof.
  intros.
  dependent induction H.
  - eauto.
  - eauto.
  - now apply IHusub1 with A B.
Qed.

Lemma normal_form_forall_pi : forall Γ e A,
    Γ ⊢ e : A -> value e ->
    forall C D, A = e_all C D \/ A = e_pi C D ->
    forall E F k, Γ ⊢ A <: e_pi E F : k ->
    (exists A' b, e = e_abs A' b) \/ (exists A' b, e = e_bind A' b).
Proof.
  intros * H V.
  dependent induction H.
    all: try solve [inversion V]. (* solving cases where `e` is not value *)
    all: intros C' D' [E | E]; inversion E; (* solving invalid cases *)
      subst; intros; solve_impossible_reduction; eauto. (* solving trivial base cases *)
  - assert (G ⊢ A <: e_pi E F : (e_kind k)).
    now apply transitivity with (e_all C' D') k0.
    apply pi_ge_inversion in H3. destruct H3; destruct_exists; subst.
    eapply IHusub1; eauto.
    eapply IHusub1; auto.
    apply transitivity with (e_all C' D') k0; eauto.
  - assert (G ⊢ A <: e_pi E F : (e_kind k)).
    now apply transitivity with (e_pi C' D') k0.
    apply pi_ge_inversion in H3. destruct H3; destruct_exists; subst.
    eapply IHusub1; eauto.
    eapply IHusub1; auto.
    apply transitivity with (e_pi C' D') k0; eauto.
Qed.

Lemma normal_form_pi : forall Γ e A B,
    Γ ⊢ e : e_pi A B -> value e ->
    (exists A' b, e = e_abs A' b) \/ (exists A' b, e = e_bind A' b).
Proof.
  intros. conclude_type_refl H.
  eapply normal_form_forall_pi; eauto.
Qed.


Ltac invert_to_normal_forms H :=
  match type of H with
  | _ ⊢ _ <: _ : e_pi ?A ?B => apply normal_form_pi in H; eauto; destruct H
  end; destruct_exists; subst
.

Ltac invert_operator_to_nf :=
  match goal with
  | H : _ ⊢ ?e : e_pi _ _ |- ?g =>
    match g with
    | context [e] => invert_to_normal_forms H
    | _ => fail
    end
  end
.

Ltac destruct_progressive_for_app :=
  let destruct_with_new_name H := (
      let V := fresh "V" in
      let e' := fresh "e'" in
      destruct H as [V | [e' H]])
  in
  match goal with
  | H : Progressive ?e |- exists e', e_app ?e _ ⟶ e' =>
    destruct_with_new_name H
  | H : EProgressive ?e |- exists e', ee_app ?e _ ⋆⟶ e' =>
    destruct_with_new_name H
  end
.

Definition is_castup (e : expr) : Prop :=
  match e with
  | e_castup _ _ => True
  | _ => False
  end
.

Lemma is_castup_dec : forall e,
    is_castup e \/ not (is_castup e).
Proof.
  destruct e; simpl; eauto.
Qed.

Lemma is_castup_eq : forall e,
    is_castup e -> exists A b, e = e_castup A b.
Proof.
  intros. destruct e; solve [inversion H | eauto].
Qed.

Definition is_bind (e : expr) : Prop :=
  match e with
  | e_bind _ _ => True
  | _ => False
  end
.

Lemma is_bind_dec : forall e,
    is_bind e \/ not (is_bind e).
Proof.
  destruct e; simpl; auto.
Qed.

Lemma is_bind_eq : forall e,
    is_bind e -> exists A b, e = e_bind A b.
Proof.
  intros. destruct e; solve [inversion H | eauto].
Qed.

Lemma num_type_inversion : forall Γ n A,
    Γ ⊢ e_num n : A -> Γ ⊢ e_int <: A : *.
Proof.
  intros.
  dependent induction H; eauto 3 using transitivity.
Qed.

Lemma int_le_inversion : forall Γ A B,
    Γ ⊢ e_int <: A : B -> A = e_int \/ exists B c, A = e_all B c.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma pi_le_inversion : forall Γ A B C k,
    Γ ⊢ e_pi A B <: C : k -> (exists D E, C = e_pi D E) \/ (exists D E, C = e_all D E).
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Lemma kind_le_inversion : forall Γ kl ek k,
    Γ ⊢ e_kind kl <: ek : k -> ek = * /\ kl = k_star /\ k = BOX.
Proof.
  intros.
  dependent induction H.
  - auto.
  - edestruct IHusub2; eauto. destruct H4. discriminate.
  - edestruct IHusub1 as (E1 & E2 & E3); auto; subst.
    apply reflexivity_l in H0. now apply box_never_welltype in H0.
Qed.

Lemma pi_of_kind : forall Γ A B C D E,
    Γ ⊢ e_pi A B <: e_pi C D : E -> exists k, E = e_kind k.
Proof.
  intros.
  dependent induction H; eauto.
  - edestruct IHusub1; eauto. subst.
    apply kind_le_inversion in H0.
    destruct_conjs; subst; eauto.
Qed.

Lemma forall_of_star : forall Γ A B C D E,
    Γ ⊢ e_all A B <: e_all C D : E -> E = *.
Proof.
  intros.
  dependent induction H; eauto.
  - erewrite IHusub1 in H0; eauto.
    apply kind_le_inversion in H0. now destruct_conjs.
Qed.


Lemma irreducible_value : forall Γ e A B,
    Γ ⊢ e : A -> A ⟹ B -> not (is_castup e) -> not (is_bind e) -> value e -> False.
Proof.
  intros * Sub R H1 H2 V.
  inversion V; subst.
  - apply kind_sub_inversion_l in Sub.
    destruct_conjs. subst. inversion R.
  - apply num_type_inversion, int_le_inversion in Sub.
    destruct Sub; destruct_conjs; subst; inversion R.
  - apply int_of_star in Sub. subst. inversion R.
  - apply abs_pi_principal in Sub as (C & k & _ & Sub).
    apply pi_le_inversion in Sub as [|]; destruct_conjs; subst; inversion R.
  - contradict H2. simpl. auto.
  - apply pi_of_kind in Sub as (k & E); subst.
    inversion R.
  - apply forall_of_star in Sub. subst. inversion R.
  - contradict H1. simpl. auto.
Qed.

Theorem progress : forall e1 e2 A,
    nil ⊢ e1 <: e2 : A -> Progressive e1 /\ Progressive e2.
Proof.
  intros.
  dependent induction H; cleanup_hyps;
    try solve [split; solve_progress_value].
  (* var is not value *)
  - inversion H0.
  (* app *)
  - conclude_refls H1. split; right;
    destruct_progressive_for_app;
    eauto 3; (* solves r_app cases *)
    invert_operator_to_nf.
    + inversion V; subst. exists (H5 ^^ e). eauto.
    + inversion V. inversion H11. subst.
        pick fresh x. instantiate_cofinites.
        exists (e_app (H5 ^` x) e). eauto.
    + inversion V; subst. exists (H6 ^^ e). eauto.
    + inversion V; inversion H11. subst.
        pick fresh x. instantiate_cofinites.
        exists (e_app (H6 ^` x) e). eauto.
  - split.
    + destruct H2.
      * destruct (is_castup_dec e1), (is_bind_dec e1).
        -- apply is_castup_eq in H5; destruct_conjs; subst; eauto.
        -- apply is_castup_eq in H5; destruct_conjs; subst; eauto.
        -- apply is_bind_eq in H6; destruct_conjs; subst;
           eauto. Unshelve. exact 0.
        -- apply reflexivity_l in H1.
           eapply irreducible_value in H1; [easy | eauto..].
      * destruct H2. eauto.
    + destruct H3.
      * destruct (is_castup_dec e2), (is_bind_dec e2).
        -- apply is_castup_eq in H5; destruct_conjs; subst; eauto.
        -- apply is_castup_eq in H5; destruct_conjs; subst; eauto.
        -- apply is_bind_eq in H6; destruct_conjs; subst; eauto.
           Unshelve. exact 0.
        -- apply reflexivity_r in H1.
           eapply irreducible_value in H1; [easy | eauto..].
      * destruct H3. eauto.
Qed.

Ltac solve_progress_evalue := auto || left; solve_evalue.

Lemma extract_abs : forall A b,
    ee_abs (extract b) = extract (e_abs A b).
Proof.
  easy.
Qed.


Theorem extracted_progress : forall e1 e2 A,
    nil ⊢ e1 <: e2 : A -> forall e1' e2', extract e1 = e1' -> extract e2 = e2' ->
    EProgressive e1' /\ EProgressive e2'.
Proof.
  intros * H.
  dependent induction H; simpl; intros e1' e2' E1 E2; subst; auto;
    try solve [split; solve_progress_evalue].
  (* var is not value *)
  - inversion H0.
  (* app *)
  - instantiate_trivial_equals.
    destruct IHusub2 with (extract e1) (extract e2); auto.
    conclude_refls H1;
    split; right; destruct_progressive_for_app; eauto; (* solve r_app cases *)
      apply evalue_value in V; auto;
        invert_operator_to_nf; simpl.
    + exists ((extract H4) ⋆^^ (extract e)). constructor.
      replace (ee_abs (extract H4)) with (extract (e_abs H2 H4)) by reflexivity.
      all: eauto using lc_extract_lc.
    + pick fresh x. exists (ee_app (extract H4 ⋆^` x) (extract e)).
      eapply er_elim; eauto 3.
      replace (ee_bind (extract H4)) with (extract (e_bind H2 H4)) by reflexivity.
      eauto using lc_extract_lc.
    + exists ((extract H5) ⋆^^ (extract e)). constructor.
      replace (ee_abs (extract H5)) with (extract (e_abs H3 H5)) by reflexivity.
      all: eauto using lc_extract_lc.
    + pick fresh x. exists (ee_app (extract H5 ⋆^` x) (extract e)).
      eapply er_elim; eauto 3.
      replace (ee_bind (extract H5)) with (extract (e_bind H3 H5)) by reflexivity.
      eauto using lc_extract_lc.
  (* castdn *)
  - instantiate_trivial_equals.
    destruct IHusub2 with (extract e1) (extract e2); auto.
    split.
    + destruct H2.
      * apply evalue_value in H2; auto.
        destruct (is_castup_dec e1), (is_bind_dec e1).
        -- apply is_castup_eq in H4 as (C & e1' & E). subst.
           simpl. right. exists (extract e1'). eauto.
        -- apply is_castup_eq in H4 as (C & e1' & E). subst.
           simpl. right. exists (extract e1'). eauto.
        -- apply is_bind_eq in H5 as (C & e1' & E). subst.
           simpl. right. pick fresh x. exists (ee_castdn (extract e1' ⋆^` x)).
           apply er_cast_inst with empty.
           replace (ee_bind (extract e1')) with (extract (e_bind C e1')) by reflexivity.
           eauto using lc_extract_lc. auto.
        -- apply reflexivity_l in H1.
           eapply irreducible_value in H1; [easy | eauto..].
      * destruct H2; eauto.
    + destruct H3.
      * apply evalue_value in H3; auto.
        destruct (is_castup_dec e2), (is_bind_dec e2).
        -- apply is_castup_eq in H4 as (C & e2' & E). subst.
           simpl. right. exists (extract e2'). eauto.
        -- apply is_castup_eq in H4 as (C & e2' & E). subst.
           simpl. right. exists (extract e2'). eauto.
        -- apply is_bind_eq in H5 as (C & e1' & E). subst.
           simpl. right. pick fresh x. exists (ee_castdn (extract e1' ⋆^` x)).
           apply er_cast_inst with empty.
           replace (ee_bind (extract e1')) with (extract (e_bind C e1')) by reflexivity.
           eauto using lc_extract_lc. auto.
        -- apply reflexivity_r in H1.
           eapply irreducible_value in H1; [easy | eauto..].
      * destruct H3; eauto.
  (* forall_l *)
  - split.
    + solve_progress_evalue.
    + instantiate_trivial_equals.
      now destruct IHusub3 with (extract (B ^^ e)) (extract C).
  (* forall_r *)
  - split.
    + instantiate_trivial_equals.
      now destruct IHusub2 with (extract A) (extract A).
    + solve_progress_evalue.
Qed.

Lemma bind_extraction_inversion : forall e ee,
    ee_bind ee = extract e ->
    exists A e', e = e_bind A e' /\ ee = extract e'.
Proof.
  induction e; simpl; intros; inversion H; eauto.
Qed.

Lemma abs_extraction_inversion : forall e ee,
    ee_abs ee = extract e ->
    exists A e', e = e_abs A e' /\ ee = extract e'.
Proof.
  induction e; simpl; intros; inversion H; eauto.
Qed.

Lemma castdn_extraction_inversion : forall e ee,
    ee_castdn ee = extract e ->
    exists A e', e = e_castdn A e' /\ ee = extract e'.
Proof.
  induction e; simpl; intros; inversion H; eauto.
Qed.

Lemma castup_extraction_inversion : forall e ee,
    ee_castup ee = extract e ->
    exists A e', e = e_castup A e' /\ ee = extract e'.
Proof.
  induction e; simpl; intros; inversion H; eauto.
Qed.

Ltac invert_extraction :=
  let A := fresh "A" in
  let e2 := fresh "e" in
  let E1 := fresh "E" in
  let E2 := fresh "E" in
  match goal with
  | H : ee_bind _ = extract _ |- _ =>
    apply bind_extraction_inversion in H as (A & e2 & E1 & E2)
  | H : ee_abs  _ = extract _ |- _ =>
    apply abs_extraction_inversion in H as (A & e2 & E1 & E2)
  | H : ee_castdn _ = extract _ |- _ =>
    apply castdn_extraction_inversion in H as (A & e2 & E1 & E2)
  | H : ee_castup _ = extract _ |- _ =>
    apply castup_extraction_inversion in H as (A & e2 & E1 & E2)
  end; subst; simpl in *
.

Ltac invert_extractions := repeat invert_extraction.


Lemma bind_inversion : forall Γ A b1 b2 T,
    Γ ⊢ e_bind A b1 <: e_bind A b2 : T ->
    exists B L, Γ ⊢ e_bind A b1 <: e_bind A b2 : e_all A B
         /\ Γ ⊢ e_all A B <: T : *
         /\ (forall x, x `notin` L -> Γ , x : A ⊢ b1 ^` x <: b2 ^` x : B ^` x)
         /\ (forall x, x `notin` L -> x `notin` fv_eexpr (extract (b1 ^` x)))
         /\ (forall x, x `notin` L -> x `notin` fv_eexpr (extract (b2 ^` x))).
Proof.
  intros. dependent induction H.
  - exists B. exists L. repeat split; eauto 2.
  - specialize (IHusub1 A b1 b2). instantiate_trivial_equals.
    destruct IHusub1 as (B' & L & IH). destruct_pairs.
    exists B', L. repeat split; eauto 3 using transitivity.
Qed.

Definition is_forall (e : expr) : Prop :=
  match e with
  | e_all _ _ => True
  | _ => False
  end
.

Lemma forall_l_sub_inversion : forall Γ A B C,
    Γ ⊢ e_all A B <: C : * ->
    not (is_forall C) ->
    exists e, mono_type e /\ Γ ⊢ e : A /\ Γ ⊢ B ^^ e <: C : *.
Proof.
  intros * Sub.
  dependent induction Sub; simpl; intros.
  + eauto.
  + contradiction.
  + contradiction.
  + eapply IHSub1; eauto.
    apply kind_sub_inversion_l in Sub2. destruct_pairs. congruence.
Qed.

Ltac split_all := repeat split.

Ltac rewrite_open_with_subst_impl G :=
  match G with
  | context [?e ^^ ?v] =>
    progress
      match v with
      | e_var_f _ => idtac
      | _ => erewrite (open_subst_eq e); eauto
      end
  end
.

Ltac rewrite_open_with_subst :=
  repeat
    match goal with
    | |- ?g => rewrite_open_with_subst_impl g
    end
.

Ltac rewrite_extract_invariant G e :=
  match G with
  | context [e ⋆^^ _] =>
    erewrite (notin_open_var_notin_open e); eauto
  end
.

Ltac find_extract_invariants :=
  repeat
    match goal with
    | H : ?x `notin` fv_eexpr (extract _) |- _  => autorewrite with reassoc in H; simpl in H
    | H : ?x `notin` fv_eexpr (?e ⋆^` ?x) |- ?G => rewrite_extract_invariant G e
    | _ => progress autorewrite with reassoc
    end
.

Lemma is_forall_eq : forall e,
    is_forall e -> exists A b, e = e_all A b.
Proof.
  intros. destruct e; simpl in *; inversion H; eauto.
Qed.


Theorem preservation : forall e1 e2 A,
    nil ⊢ e1 <: e2 : A ->
    forall e1'' e2'', extract e1 ⋆⟶ e1'' -> extract e2 ⋆⟶ e2''  ->
    exists e1' e2', extract e1' = e1''
             /\ extract e2' = e2''
             /\ e1 ⟶ e1'
             /\ e2 ⟶ e2'
             /\ nil ⊢ e1' <: e2' : A.
Proof.
  intros * Sub.
  dependent induction Sub; simpl; intros;
    solve_impossible_reduction;
    instantiate_trivial_equals.
  - inversion H0; subst.
    + inversion H1; subst.
      (* main case for r_app *)
      * destruct IHSub2 with ee2 ee0 as (e1' & e2' & IH); eauto.
        destruct_conjs. subst.
        exists (e_app e1' e), (e_app e2' e). repeat split; eauto 3.
      * invert_extractions. invert_sub_hyp. solve_impossible_reduction.
      * invert_extractions. invert_sub_hyp. solve_impossible_reduction.
    + invert_extractions. invert_sub_hyp.
      inversion H1; subst; solve_impossible_reduction.
      (* main case for r_beta *)
      exists (e0 ^^ e), (b ^^ e).
      autorewrite with reassoc.
      split_all; eauto.
      pose (B' := Sub2). apply abs_pi_principal in B'. destruct_conjs.
      apply pi_sub_inversion in H8 as (k' & L & Sub3).
      apply abs_principal_inversion in H5 as (L' & Sub4).
      pick fresh x for
           (L `union` L' `union` fv_expr e0 `union` fv_expr b `union` fv_expr B).
      instantiate_cofinites. destruct_pairs.
      rewrite_open_with_subst.
      eapply ctx_narrowing_cons in Sub4; eauto 4 using substitution_cons.
    + invert_extractions. invert_sub_hyp.
      inversion H1; subst; solve_impossible_reduction.
      (* main case for r_inst *)
      apply bind_inversion in Sub2 as (F & L1 & Hb). destruct_pairs.
      apply forall_l_sub_inversion in H6 as (m & M & Subm & Sub_inst); auto.
      exists (e_app (e0 ^^ m) e), (e_app (b ^^ m) e). split_all; simpl.
      * pick fresh x'. instantiate_cofinites. find_extract_invariants.
      * pick fresh x'. instantiate_cofinites. find_extract_invariants.
      * eauto.
      * eauto.
      * eapply s_app; eauto. apply s_sub with (F ^^ m) k_star; auto.
        pick fresh x' for
             (L `union` L0 `union` L1 `union`
                fv_expr e0 `union` fv_expr b `union` fv_expr F).
        rewrite_open_with_subst.
        eauto 3 using substitution_cons.
  - inversion H0; subst.
    + inversion H1; subst.
      (* main case for r_castdn *)
      * destruct IHSub2 with ee2 ee0 as (e1' & e2' & IH); eauto.
        destruct_conjs. subst.
        exists (e_castdn B e1'), (e_castdn B e2'). repeat split; eauto 3.
      * invert_extractions. invert_sub_hyp. inversion H3.
      * invert_extractions. invert_sub_hyp. inversion H3.
    + invert_extractions. invert_sub_hyp. inversion H1; subst; solve_impossible_reduction.
    (* main case for r_cast_inst *)
      apply bind_inversion in Sub2 as (F & L1 & Hb). destruct_pairs.
      apply forall_l_sub_inversion in H8 as (m & M & Subm & Sub_inst); auto.
      exists (e_castdn B (e ^^ m)), (e_castdn B (b ^^ m)). split_all; simpl.
      * pick fresh x'. instantiate_cofinites. find_extract_invariants.
      * pick fresh x'. instantiate_cofinites. find_extract_invariants.
      * eauto.
      * eauto.
      * eapply s_castdn; eauto.
        eapply s_sub with (F ^^ m) k_star; auto.
        pick fresh x' for (L `union` L0 `union` L1 `union` fv_expr e `union` fv_expr b `union` fv_expr F). rewrite_open_with_subst.
        eauto 3 using substitution_cons.
      * intro. apply is_forall_eq in H12. destruct_exists. subst. inversion H.
    + invert_extractions. invert_sub_hyp. inversion H1; subst; solve_impossible_reduction.
      (* main case for r_cast_elim *)
      * exists e, b. repeat split; eauto.
        apply castup_inversion in Sub2 as (C & k' & Sub & R & Sub').
        apply s_sub with C k'. auto.
        eapply type_preservation; eauto.
  - edestruct IHSub1 as (e1' & e2' & H1); eauto.
    destruct_pairs.
    exists e1', e2'. repeat split; eauto.
Qed.

Require Import LanguageUtil.
Require Import BasicProperties.
Require Import Properties.
Require Import Transitivity.
Require Import Extraction.
Require Import KindReasoning.

Require Import Program.Tactics.

Definition Progressive (e : expr) : Prop := value e \/ exists e', e ⟶ e'.
Definition EProgressive (e : eexpr) := evalue e \/ exists e', e ⋆⟶ e'.

Hint Unfold Progressive : core.
Hint Unfold EProgressive : core.

Ltac instantiate_trivial_equals := repeat
  match goal with
  | H : ?a ~= ?a -> _ |- _ => specialize (H JMeq_refl)
  | H : ?a  = ?a -> _ |- _ => specialize (H eq_refl)
  end
.

Hint Extern 1 (lc_expr _) => instantiate_colimits : inst.

Ltac cleanup_hyps := instantiate_trivial_equals; destruct_pairs; clear_dups.
Ltac solve_progress_value := auto || left; eauto with inst.

Lemma pi_sub_l : forall Γ e A B k,
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
      subst; intros; eauto. (* solving trivial base cases *)
  - assert (G ⊢ A <: e_pi E F : (e_kind k)).
    now apply transitivity with (e_all C' D') k0.
    apply pi_sub_l in H3. destruct H3; destruct_exists; subst.
    eapply IHusub1; eauto.
    eapply IHusub1; auto.
    apply transitivity with (e_all C' D') k0; eauto.
  - assert (G ⊢ A <: e_pi E F : (e_kind k)).
    now apply transitivity with (e_pi C' D') k0.
    apply pi_sub_l in H3. destruct H3; destruct_exists; subst.
    eapply IHusub1; eauto.
    eapply IHusub1; auto.
    apply transitivity with (e_pi C' D') k0; eauto.
Qed.


Ltac conclude_type_refl H :=
  match type of H with
  | ?G ⊢ _ <: _ : ?A =>
    let k := fresh "k" in
    let H := fresh "H" in
    let contra := fresh "contra" in
    assert (A = BOX \/ exists k, G ⊢ A : e_kind k) as [contra | [k H]]
        by (eapply type_correctness; eassumption);
    try solve [inversion contra]
  end
.

Lemma normal_form_pi : forall Γ e A B,
    Γ ⊢ e : e_pi A B -> value e ->
    (exists A' b, e = e_abs A' b) \/ (exists A' b, e = e_bind A' b).
Proof.
  intros. conclude_type_refl H.
  eapply normal_form_forall_pi; eauto.
Qed.


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
    + inversion V; subst. exists (H5 <^^> e). eauto.
    + inversion V. inversion H11. subst.
        pick fresh x. instantiate_colimits.
        exists (e_app (H5 <^> x) e). eauto.
    + inversion V; subst. exists (H6 <^^> e). eauto.
    + inversion V; inversion H11. subst.
        pick fresh x. instantiate_colimits.
        exists (e_app (H6 <^> x) e). eauto.
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
    + pick fresh x. exists (ee_app (extract H4 ⋆^ x) (extract e)).
      eapply er_elim; eauto 3.
      replace (ee_bind (extract H4)) with (extract (e_bind H2 H4)) by reflexivity.
      eauto using lc_extract_lc.
    + exists ((extract H5) ⋆^^ (extract e)). constructor.
      replace (ee_abs (extract H5)) with (extract (e_abs H3 H5)) by reflexivity.
      all: eauto using lc_extract_lc.
    + pick fresh x. exists (ee_app (extract H5 ⋆^ x) (extract e)).
      eapply er_elim; eauto 3.
      replace (ee_bind (extract H5)) with (extract (e_bind H3 H5)) by reflexivity.
      eauto using lc_extract_lc.
  (* forall_l *)
  - split.
    + solve_progress_evalue.
    + instantiate_trivial_equals.
      now destruct IHusub3 with (extract (B <^^> e)) (extract C).
  (* forall_r *)
  - split.
    + instantiate_trivial_equals.
      now destruct IHusub2 with (extract A) (extract A).
    + solve_progress_evalue.
Qed.

Ltac find_impossible_reduction :=
  simpl in *;
  match goal with
  | H : ee_app _ _ ⋆⟶ _ |- _ => fail
  | H : _ ⋆⟶ _ |- _  => solve [inversion H]
  end
.

Ltac solve_impossible_reduction := try find_impossible_reduction.

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

Ltac invert_extraction :=
  let A := fresh "A" in
  let e2 := fresh "e" in
  let E1 := fresh "E" in
  let E2 := fresh "E" in
  match goal with
  | H : ee_bind ?ee = extract ?e |- _ =>
    apply bind_extraction_inversion in H as (A & e2 & E1 & E2)
  | H : ee_abs ?ee = extract ?e |- _ =>
    apply abs_extraction_inversion in H as (A & e2 & E1 & E2)
  end; subst; simpl in *
.

Ltac invert_extractions := repeat invert_extraction.

Lemma abs_not_star : forall Γ A b,
    not ( Γ ⊢ e_abs A b : * ).
Proof.
  intros. intro.
  dependent induction H.
  - eapply IHusub1; eauto using star_sub_inversion_l.
Qed.

Lemma bind_not_star : forall Γ A b,
    not ( Γ ⊢ e_bind A b : * ).
Proof.
  intros. intro.
  dependent induction H.
  - eapply IHusub1; eauto using star_sub_inversion_l.
Qed.

Lemma abs_sub_r : forall Γ A b e T,
    Γ ⊢ e_abs A b <: e : T ->
    exists c, e = e_abs A c.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - now apply abs_not_star in H0.
  - now eapply IHusub1.
Qed.

Lemma abs_sub_l : forall Γ A b e T,
    Γ ⊢ e <: e_abs A b : T ->
    exists c, e = e_abs A c.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - apply reflexivity_r in H2.
    now apply abs_not_star in H2.
  - now eapply IHusub1.
Qed.

Lemma bind_sub_r : forall Γ A b e T,
    Γ ⊢ e_bind A b <: e : T ->
    exists c, e = e_bind A c.
Proof.
  intros.
  dependent induction H.
  - eauto.
  - now apply bind_not_star in H0.
  - now eapply IHusub1.
Qed.

Lemma bind_sub_l : forall Γ A b e T,
    Γ ⊢ e <: e_bind A b : T ->
    exists c, e = e_bind A c.
Proof.
  intros. dependent induction H.
  - eauto.
  - apply reflexivity_r in H2. now apply bind_not_star in H2.
  - now eapply IHusub1.
Qed.

Ltac invert_sub_hyp :=
  let b := fresh "b" in
  let E := fresh "E" in
  let H' := fresh "H" in
  match goal with
  | _ : _ ⊢ e_abs _ _  <: e_abs _ _ : _ |- _ => idtac
  | _ : _ ⊢ e_bind _ _ <: e_bind _ _ : _ |- _ => idtac
  | H : _ ⊢ e_abs _ _ <: _ : _ |- _ =>
    pose (H' := H); apply abs_sub_r in H' as (b & E)
  | H : _ ⊢ _ <: e_abs _ _ : _ |- _ =>
    pose (H' := H); apply abs_sub_l in H' as (b & E)
  | H : _ ⊢ e_bind _ _ <: _ : _ |- _ =>
    pose (H' := H); apply bind_sub_r in H' as (b & E)
  | H : _ ⊢ _ <: e_bind _ _ : _ |- _ =>
    pose (H' := H); apply bind_sub_l in H' as (b & E)
  end; subst; simpl in *
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
    exists k' L, forall x, x `notin` L ->
      Γ ⊢ C <: A : e_kind k' /\ Γ, x : C ⊢ B <^> x <: D <^> x : e_kind k.
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
    exists L, forall x, x `notin` L -> Γ, x : A ⊢ b1 <^> x <: b2 <^> x : B <^> x.
Proof.
  intros * Sub.
  dependent induction Sub; intros.
  - apply pi_sub_inversion in H3 as (k' & L' & H').
    exists (L `union` L'). intros.
    instantiate_colimits. destruct_pairs. eauto.
  - apply IHSub1 with k; eauto using transitivity.
Qed.

Lemma abs_principal_inversion : forall Γ A b1 b2 B,
    Γ ⊢ e_abs A b1 <: e_abs A b2 : e_pi A B ->
    exists L, forall x, x `notin` L -> Γ, x : A ⊢ b1 <^> x <: b2 <^> x : B <^> x.
Proof.
  intros.
  conclude_type_refl H.
  now apply abs_inversion with (e_pi A B) k.
Qed.

Lemma bind_inversion : forall Γ A b1 b2 T,
    Γ ⊢ e_bind A b1 <: e_bind A b2 : T ->
    exists B L, Γ ⊢ e_bind A b1 <: e_bind A b2 : e_all A B
         /\ Γ ⊢ e_all A B <: T : *
         /\ (forall x, x `notin` L -> Γ , x : A ⊢ b1 <^> x <: b2 <^> x : B <^> x)
         /\ (forall x, x `notin` L -> x `notin` fv_eexpr (extract (b1 <^> x)))
         /\ (forall x, x `notin` L -> x `notin` fv_eexpr (extract (b2 <^> x))).
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
    exists e, mono_type e /\ Γ ⊢ e : A /\ Γ ⊢ B <^^> e <: C : *.
Proof.
  intros * Sub.
  dependent induction Sub; simpl; intros.
  + eauto.
  + contradiction.
  + contradiction.
  + eapply IHSub1; eauto.
    apply kind_sub_inversion_l in Sub2. destruct_pairs. congruence.
Qed.

Lemma notin_open_var_notin_open_rec : forall e x n,
    x `notin` fv_eexpr (e ⋆n^^ (ee_var_f x)) ->
    forall v, e ⋆n^^ v = e.
Proof.
  intros e x.
  induction e; unfold open_eexpr_wrt_eexpr in *; simpl; intros; auto;
    try solve [rewrite IHe; auto | rewrite IHe1; auto; rewrite IHe2; auto].
  - destruct (n0 == n).
    + contradict H. simpl. auto.
    + easy.
Qed.

Lemma notin_open_var_notin_open : forall e x v,
    x `notin` fv_eexpr (e ⋆^ x) ->
    e ⋆^^ v = e.
Proof.
  intros.
  eapply notin_open_var_notin_open_rec; auto.
Qed.

Hint Rewrite extract_open_distr : reassoc.

Ltac split_all := repeat split.

Ltac rewrite_open_with_subst_impl G :=
  match G with
  | context [?e <^^> ?v] =>
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
    | H : ?x `notin` fv_eexpr (?e ⋆^ ?x) |- ?G => rewrite_extract_invariant G e
    | _ => progress autorewrite with reassoc
    end
.

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
      exists (e0 <^^> e), (b <^^> e).
      autorewrite with reassoc.
      split_all; eauto.
      pose (B' := Sub2). apply abs_pi_principal in B'. destruct_conjs.
      apply pi_sub_inversion in H7 as (k' & L & Sub3).
      apply abs_principal_inversion in H3 as (L' & Sub4).
      pick fresh x for
           (L `union` L' `union` fv_expr e0 `union` fv_expr b `union` fv_expr B).
      instantiate_colimits. destruct_pairs.
      rewrite_open_with_subst.
      eauto 4 using substitution_cons, ctx_narrowing_cons.
    + invert_extractions. invert_sub_hyp.
      inversion H1; subst; solve_impossible_reduction.
      (* main case for r_inst *)
      apply bind_inversion in Sub2 as (F & L1 & Hb). destruct_pairs.
      apply forall_l_sub_inversion in H3 as (m & M & Subm & Sub_inst); auto.
      exists (e_app (e0 <^^> m) e), (e_app (b <^^> m) e). split_all; simpl.
      * pick fresh x'. instantiate_colimits. find_extract_invariants.
      * pick fresh x'. instantiate_colimits. find_extract_invariants.
      * eauto.
      * eauto.
      * eapply s_app; eauto. apply s_sub with (F <^^> m) k_star; auto.
        pick fresh x' for
             (L `union` L0 `union` L1 `union`
                fv_expr e0 `union` fv_expr b `union` fv_expr F).
        rewrite_open_with_subst.
        eauto 3 using substitution_cons.
  - edestruct IHSub1 as (e1' & e2' & H1); eauto.
    destruct_pairs.
    exists e1', e2'. repeat split; eauto.
Qed.

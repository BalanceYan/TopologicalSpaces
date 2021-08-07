(* Notation *)

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃ x .. y ']' , '/' P ']'") : type_scope.

Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.

Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.

Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.

Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'λ' x .. y ']' , '/' t ']'").

(* Logic *)
Axiom classic : ∀ P : Prop, P ∨ ¬P.

Proposition NNPP : ∀ P, (¬ (¬ P) ↔ P).
Proof. intros; destruct (classic P); tauto. Qed.

Proposition inp : ∀ P Q : Prop, (P ↔ Q) → (¬ P → ¬ Q).
Proof. intros; intro. elim H0. apply H; auto. Qed.

(* Ensemble *)
Parameter Class : Type.

Parameter In : Class → Class → Prop.
Notation "a ∈ A" := (In a A)(at level 70).
Notation "a ∉ A" := (¬ (a ∈ A))(at level 70).

Parameter Classifier : ∀ P : Class → Prop, Class.
Notation "\{ P \}" := (Classifier P)(at level 0).

Axiom ExtAx : ∀ A B : Class, A = B ↔ (∀ x, x ∈ A ↔ x ∈ B).
Ltac AppE := apply ExtAx; split; intros.

Axiom ClaAx : ∀ (x : Class) (P : Class → Prop),
  x ∈ \{ P \} ↔ (P x).
Ltac AppC H := apply -> ClaAx in H; simpl in H.

Parameter ClassifierP : ∀ P : Class → Class → Prop, Class.
Notation "\{\ P \}\" := (ClassifierP P)(at level 0).

Fact ClaI : ∀ x (P : Class → Prop), P x → x ∈ \{ P \}.
Proof. intros x P HP. apply ClaAx; auto. Qed.

Fact ClaE : ∀ x (P : Class → Prop), x ∈ \{ P \} → P x.
Proof. intros x P Hx. apply ClaAx; auto. Qed.

Definition NoEmpty A := ∃ x, x ∈ A.
Notation "⦿ A" := (NoEmpty A) (at level 45).

Definition Empty := \{ λ x, x ≠ x \}.
Notation " ∅ " := Empty.

Fact EmptyNI : ∀ x, x ∉ ∅.
Proof.
  intros x H. AppC H. apply H; auto.
Qed.
Ltac exfalso0 := exfalso; eapply EmptyNI; eauto.

Fact EmptyEq : ∀ x, x = ∅ ↔ ¬ (⦿ x).
Proof.
  split; intros. subst x. intro. destruct H. exfalso0.
  AppE. elim H. exists x0; auto. exfalso0.
Qed.

Fact EmptyNE : ∀ x, x ≠ ∅ ↔ ⦿ x.
Proof.
  intros. pose proof EmptyEq. split; intros.
  - apply inp with (Q := ¬ (⦿ x)) in H0; auto.
    apply -> NNPP in H0; auto.
  - intro. apply H in H1; auto.
Qed.

Definition Singleton x : Class := \{ λ z, z = x \}.
Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Fact SingI : ∀ x, x ∈ [x].
Proof. intros. apply ClaAx; auto. Qed.

Fact SingE : ∀ x y, x ∈ [y] → x = y.
Proof. intros. AppC H; auto. Qed.

Definition Included A B := ∀ x, x ∈ A → x ∈ B.
Notation "A ⊂ B" := (Included A B)(at level 70).

Fact ReSyTrP : ∀ A B C : Class,
  (A ⊂ A) ∧ (A ⊂ B ∧ B ⊂ A → A = B) ∧ (A ⊂ B ∧ B ⊂ C → A ⊂ C).
Proof.
  intros. split; try red; auto. split; intros.
  - AppE; apply H; auto.
  - destruct H. intros x Hx. apply H in Hx. auto.
Qed.

Definition PowerSet X : Class := \{ λ A, A ⊂ X \}.
Notation " cP( X )" := (PowerSet X)(at level 9, right associativity).

Definition Union A B := \{ λ x, x ∈ A ∨ x ∈ B \}.
Notation "A ⋃ B" := (Union A B)(at level 65, right associativity).

Definition Inter A B := \{ λ x, x ∈ A ∧ x ∈ B \}.
Notation "A ∩ B" := (Inter A B)(at level 60, right associativity).

Definition Setmin A B := \{ λ x, x ∈ A ∧ x ∉ B \}.
Notation "A - B" := (Setmin A B).

(* Basic properties (Union, Inter, Setmin, Sub) *)
Fact Idem : ∀ A, A ⋃ A = A.
Proof. intros. AppE. AppC H; tauto. apply ClaI; auto. Qed.

Fact Idem' : ∀ A, A ∩ A = A.
Proof. intros. AppE. AppC H; tauto. apply ClaI; auto. Qed.

Fact Commu : ∀ A B, A ⋃ B = B ⋃ A.
Proof. intros. AppE; AppC H; apply ClaI; tauto. Qed.

Fact Commu' : ∀ A B, A ∩ B = B ∩ A.
Proof. intros. AppE; AppC H; apply ClaI; tauto. Qed.

Fact Assoc : ∀ A B C, (A ⋃ B) ⋃ C =A ⋃ (B ⋃ C).
Proof.
  intros. AppE; apply ClaI; apply ClaE in H as [].
  - apply ClaE in H as []; auto. right; apply ClaI; auto.
  - right; apply ClaI; auto.
  - left; apply ClaI; auto.
  - apply ClaE in H as []; auto. left; apply ClaI; auto.
Qed.

Fact Distribu : ∀ A B C, (A ⋃ B) ∩ C = (A ∩ C) ⋃ (B ∩ C).
Proof.
  intros. AppE; apply ClaAx.
  - do 2 (AppC H; destruct H).
    + left; apply ClaI; auto. + right; apply ClaI; auto.
  - do 2 (AppC H; destruct H); split; try (apply ClaI; auto); auto.
Qed.

Fact Distribu' : ∀ A B C, A ∩ (B ⋃ C) = A ∩ B ⋃ A ∩ C.
Proof.
  intros. rewrite Commu', Distribu, Commu', (Commu' A C); auto.
Qed.

Fact TwDeMorgan : ∀ A B C, A - (B ∩ C) = (A - B) ⋃ (A - C).
Proof.
  intros. AppE; AppC H; apply ClaI.
  - destruct H, (classic (x ∈ C)).
    + left; apply ClaI. split; auto. intro; elim H0. apply ClaI; tauto.
    + right; apply ClaI. split; auto.
  - destruct H; apply ClaE in H as []; split; auto;
    intro; AppC H1; destruct H1; tauto.
Qed.

Fact UnionNI : ∀ x A B, x ∉ A ⋃ B → x ∉ A /\ x ∉ B.
Proof. intros. split; intro; elim H; apply ClaI; auto. Qed.

Fact InterEm : ∀ A, A ∩ ∅ = ∅.
Proof. intros. AppE. AppC H; tauto. exfalso0. Qed.

Fact SetminId : ∀ X, X - X = ∅.
Proof. intro. AppE. apply ClaE in H; tauto. exfalso0. Qed.

Fact SetminEm : ∀ X, X - ∅ = X.
Proof.
  intro. AppE. apply ClaE in H; tauto.
  apply ClaI. split; auto. intro. exfalso0.
Qed.

Fact SubUnion : ∀ A B, B ⊂ A → A ⋃ B = A.
Proof.
  intros. AppE. apply ClaE in H0 as []; auto. apply ClaI; auto.
Qed.

Fact SubSetmin : ∀ A X, A ⊂ X → X - A ⊂ X.
Proof. intros * Hsub x Hx. apply ClaE in Hx. tauto. Qed.

Fact SubSetmin1 : ∀ A X, A ⊂ X → X - (X - A) = A.
Proof.
  intros. AppE. apply ClaE in H0 as [Hx H0].
  destruct (classic (x ∈ A)); eauto. elim H0. apply ClaI; eauto.
  apply ClaI. split; eauto. intro. apply ClaE in H1; tauto.
Qed.

Fact SetBasicP : ∀ x U A, U ∩ A - [x] = ∅ → x ∉ A → U ∩ A = ∅.
Proof with eauto.
  intros. rewrite <- H. AppE; apply ClaE in H1 as [Hu Ha];
  apply ClaI; split... apply ClaI. split... intro.
  apply ClaE in H1. subst... apply ClaE in Ha. tauto.
Qed.

Fact SetBasicP1 : ∀ A B C,
  A ∈ [C] ⋃ [∅] → B ∈ [C] ⋃ [∅] → A ∩ B ∈ [C] ⋃ [∅].
Proof with eauto.
  intros. apply ClaE in H as []; apply ClaE in H0 as [];
    apply ClaE in H; apply ClaE in H0; subst; apply ClaI.
    rewrite Idem'; left; apply ClaI...
    rewrite InterEm; right; apply ClaI...
    right. rewrite Commu', InterEm. apply ClaI...
    right. rewrite InterEm. apply ClaI...
Qed.

Definition EleU cA := \{ λ z, ∃ y, z ∈ y ∧ y ∈ cA \}.
Notation "∪ cA" := (EleU cA)(at level 66).

Definition EleI cA := \{ λ z, ∀ y, y ∈ cA → z ∈ y \}.
Notation "⋂ cA" := (EleI cA)(at level 66).

Fact EmEleU : ∪∅ = ∅.
Proof. AppE; [| exfalso0]. apply ClaE in H as [y []]. exfalso0. Qed.

Fact SiEleU : ∀ X, ∪[X] = X.
Proof with eauto.
  intro. AppE. apply ClaE in H as [y [Hx Hy]]. apply ClaE in Hy.
  subst... apply ClaI. exists X. split... apply ClaI...
Qed.

Fact EleUP : ∀ a cT, cT ⊂ [a] ⋃ [∅] → ∪cT ∈ [a] ⋃ [∅].
Proof with eauto.
  intros. assert (cT ∈ cP([a] ⋃ [∅])); apply ClaI...
  assert (∀ c d, cP([c] ⋃ [d]) =
    \{ λ Z, Z = ∅ \/ Z = [c] \/ Z = [d] \/ Z = [c] ⋃ [d] \}).
  { intros. AppE.
    - apply ClaI. apply ClaE in H1. destruct (classic (c ∈ x)).
      + destruct (classic (d ∈ x)).
        * right; right; right. apply ReSyTrP... split...
          intros z Hz. subst. apply ClaE in Hz as [];
          apply ClaE in H4; subst...
        * right; left. AppE; [| apply ClaE in H4; subst; auto].
          apply ClaI. pose proof H4. apply H1 in H4. subst.
          apply ClaE in H4 as []; apply ClaE in H4; subst... tauto.
      + destruct (classic (d ∈ x)).
        * right; right; left. AppE; [| apply ClaE in H4; subst; auto].
          apply ClaI. pose proof H4. apply H1 in H4. subst.
          apply ClaE in H4 as []; apply ClaE in H4; subst... tauto.
        * left. AppE; [| exfalso0]. pose proof H4. apply H1 in H4.
          subst. apply ClaE in H4 as []; apply ClaE in H4; subst; tauto...
    - apply ClaE in H1. apply ClaI; intros z Hz.
      destruct H1 as [| [| [| ]]]; subst... exfalso0.
      apply ClaI... apply ClaI... } rewrite H1 in H0; clear H1.
  apply ClaE in H0 as [| [| [| ]]]; subst.
  + assert (∪∅ = ∅).
    { AppE; [| exfalso0]. apply ClaE in H0 as [y [_ Hy]]. exfalso0. }
    rewrite H0. right. apply ClaI...
  + left. rewrite SiEleU. apply ClaI...
  + right. rewrite SiEleU. apply ClaI...
  + assert (∪ [a] ⋃ [∅] = a).
    { AppE. apply ClaE in H0 as [y [Hx Hy]].
      apply ClaE in Hy as []; apply ClaE in H0; subst... exfalso0.
      apply ClaI. exists a. split... apply ClaI. left. apply ClaI... }
    rewrite H0. left; apply ClaI...
Qed.

Fact EleIP : ∀ A cA, A ∈ cA → ⋂cA ⊂ A.
Proof. intros * H x Hx. apply ClaE in Hx. apply Hx; auto. Qed.

(* De Morgan *)
Definition AAr A cA := \{λ z, ∃ Ar, Ar ∈ cA /\ z = A - Ar\}.

Fact AArP : ∀ A cA, cA ≠ ∅ → AAr A cA ≠ ∅.
Proof.
  intros. apply EmptyNE in H as [Ar H]. apply EmptyNE.
  exists (A - Ar). apply ClaI; eauto.
Qed.

Fact DeMorganUI : ∀ A cA, cA ≠ ∅ → (A - ∪cA) = ⋂(AAr A cA).
Proof with eauto.
  intros. AppE.
  - apply ClaE in H0 as [Hx HcA]. apply ClaI. intros.
    apply ClaE in H0 as [B [Hb Heq]]. subst. apply ClaI. split...
    intro. elim HcA. apply ClaI...
  - apply EmptyNE in H as [Ar H]. apply ClaE in H0. apply ClaI.
    assert (A - Ar ∈ AAr A cA). { apply ClaI... }
    apply H0 in H1. apply ClaE in H1 as [Hx H1]. split...
    intro. apply ClaE in H2 as [B [Hb H2]].
    assert (A - B ∈ AAr A cA). { apply ClaI... }
    apply H0 in H3. apply ClaE in H3; tauto.
Qed.

Definition Unorder x y := [x] ⋃ [y].
Notation "[ x | y ] " := (Unorder x y) (at level 0).

Definition Order x y := [ [x] | [x | y] ].
Notation "[ x , y , .. , z ]" :=
  (Order .. (Order x y ) .. z ) (z at level 69).

Axiom ClaAx' : ∀ (x y : Class)(P : Class → Class → Prop),
  [x, y] ∈ \{\ P \}\ ↔ (P x y).
Ltac AppC' H := apply -> ClaAx' in H; simpl in H.

Fact ClaI' : ∀ x y (P : Class → Class → Prop),
  P x y → [x, y] ∈ \{\ P \}\.
Proof. intros x y P HP. apply ClaAx'; auto. Qed.

Fact ClaE' : ∀ x y (P : Class → Class → Prop),
  [x, y] ∈ \{\ P \}\ → P x y.
Proof. intros x y P Hx. apply ClaAx'; auto. Qed.

Definition Cartesian X Y := \{\ λ x y, x ∈ X ∧ y ∈ Y \}\.
Notation " X × Y " := (Cartesian X Y)(at level 2, right associativity).

Definition Relation R X Y := R ⊂ X × Y.

Definition Mapping F X Y : Prop :=
  Relation F X Y ∧ (∀ x, x ∈ X → (∃ y, [x, y] ∈ F)) ∧
  (∀ x y1 y2, [x, y1] ∈ F ∧ [x, y2] ∈ F → y1 = y2 ).
Notation "F : X → Y" := (Mapping F X Y)(at level 10).

Definition Value F x := ⋂ \{λ y, [x, y] ∈ F \}.
Notation "F [ x ]" := (Value F x)(at level 5).

Fact PropertyValue : ∀ F X Y x,
  Mapping F X Y → x ∈ X → [x, F[x]] ∈ F.
Proof with eauto.
  intros. unfold Mapping, Relation in H; destruct H, H1.
  apply H1 in H0 as [y H0]. assert (y = F[x]).
  { AppE. apply ClaI; intros. AppC H4.
    assert (y0 = y). { eapply H2... } subst...
    AppC H3. apply H3. apply ClaI... } subst...
Qed.

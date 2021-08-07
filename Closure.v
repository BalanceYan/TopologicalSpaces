Require Export Neighborhood.

(* Closure *)
Definition Condensa x A X cT := Topology X cT ∧ A ⊂ X ∧ x ∈ X ∧
  ∀ U, TNeigh x U X cT → U ∩ (A - [x]) ≠ ∅.

Definition Derivaed A X cT := \{λ x, Condensa x A X cT \}.

Fact DerivaedP : ∀ A X cT, Derivaed A X cT ⊂ X.
Proof. intros * x Hx. apply ClaE in Hx. apply Hx. Qed.

Definition Closed A X cT :=
  Topology X cT ∧ A ⊂ X ∧ Derivaed A X cT ⊂ A.

Definition Closure A X cT := A ⋃ Derivaed A X cT.

Fact ClosureP : ∀ A X cT, A ⊂ X → Closure A X cT ⊂ X.
Proof with eauto.
  intros * Ha x Hx. apply ClaE in Hx as []...
  apply DerivaedP in H...
Qed.

(* Theorem4 *)
Lemma LeTh4 : ∀ x C X cT, Topology X cT → C ⊂ X → x ∈ X →
  x ∉ Derivaed C X cT → ∃ U, TNeigh x U X cT ∧ U ∩ (C - [x]) = ∅.
Proof with eauto.
  intros * Ht Hsub Hx Hp.
  destruct (classic (∃ U, TNeigh x U X cT ∧ U ∩ (C - [x]) = ∅))...
  elim Hp. apply ClaI. split... split... split...
Qed.

Theorem Theorem4a : ∀ X cT, Topology X cT → Derivaed ∅ X cT = ∅.
Proof with eauto.
  intros * Ht. AppE; [|exfalso0]. apply ClaE in H as [_ [_ [Hx Hp]]].
  eapply TNeighP in Ht... apply Hp in Ht. elim Ht. AppE; [|exfalso0].
  apply ClaE in H as [_ H]. apply ClaE in H; tauto. apply Ht.
Qed.

Theorem Theorem4b : ∀ A B X cT, Topology X cT → A ⊂ X → B ⊂ X →
  A ⊂ B → Derivaed A X cT ⊂ Derivaed B X cT.
Proof with eauto.
  intros * Ht Ha Hb Hsub. intros x Hx.
  apply ClaE in Hx as [_ [_ [Hx Hp]]]. apply ClaI. split... split...
  split... intros U Hu. apply Hp in Hu.
  assert (U ∩ A - [x] ⊂ U ∩ B - [x]).
  { intros z Hz. apply ClaE in Hz as [Hz Hza]. apply ClaE in Hza
      as [Hza Hneq]. apply ClaI. split... apply ClaI. split... }
  intro. rewrite H0 in H. assert (U ∩ A - [x] = ∅).
  { apply ReSyTrP... split... intros z Hz. exfalso0. } tauto.
Qed.

Theorem Theorem4c : ∀ A B X cT, Topology X cT → A ⊂ X → B ⊂ X →
  Derivaed (A ⋃ B) X cT = Derivaed A X cT ⋃ Derivaed B X cT.
Proof with eauto.
  intros * Ht Ha Hb. assert (A ⊂ A ⋃ B ∧ B ⊂ A ⋃ B).
  { split; intros x Hx; apply ClaI. left... right... }
  destruct H as [Hsa Hsb]. assert (A ⋃ B ⊂ X).
  { intros z Hz. apply ClaE in Hz as []... }
  eapply Theorem4b in Hsa... eapply Theorem4b in Hsb...
  AppE; revgoals. apply ClaE in H0 as []...
  destruct (classic (x ∈ Derivaed A X cT ⋃ Derivaed B X cT))...
  assert (Hab : x ∉ Derivaed A X cT ∧ x ∉ Derivaed B X cT).
  { split; intro; elim H1; apply ClaI... }
  clear H1; destruct Hab as [Hna Hnb]. assert (H0' := H0).
  apply ClaE in H0' as [_ [_ [Hx _]]].
  apply LeTh4 in Hna as [U [Hun Hue]]...
  apply LeTh4 in Hnb as [V [Hvn Hve]]...
  set (U ∩ V) as D. assert (Hd : D ∩ ((A ⋃ B) - [x]) = ∅).
  { assert (H1 : D ∩ ((A ⋃ B) - [x]) = D ∩ ((A - [x]) ⋃ (B - [x]))).
    { assert ((A ⋃ B) - [x] = A - [x] ⋃ B - [x]).
      { AppE. apply ClaE in H1 as [Hab H1]. apply ClaE in Hab as [];
        apply ClaI. left; apply ClaI... right; apply ClaI...
        apply ClaE in H1 as []; apply ClaE in H1 as [H1 He];
        apply ClaI; split; eauto; apply ClaI; eauto. } rewrite H1... }
    assert (H2 : D ∩ (A - [x] ⋃ B - [x]) =
      (D ∩ (A - [x])) ⋃ (D ∩ (B - [x]))).
    { apply Distribu'... }
    assert (H3 : (D ∩ (A - [x])) ⋃ (D ∩ (B - [x])) ⊂
      (U ∩ (A - [x])) ⋃ (V ∩ (B - [x]))).
    { intros z Hz. apply ClaE in Hz as []; apply ClaI;
      apply ClaE in H3 as [H3 Hz]; apply ClaE in H3 as [Hu Hv].
      left; apply ClaI... right; apply ClaI... }
    assert (H4 : (U ∩ (A - [x])) ⋃ (V ∩ (B - [x])) = ∅).
    { rewrite Hue, Hve. AppE.
      apply ClaE in H4 as []; exfalso0. exfalso0. }
    rewrite H1, H2. rewrite H4 in H3. apply ReSyTrP...
    split... intros z Hz; exfalso0. }
  assert (x ∉ Derivaed (A ⋃ B) X cT).
  { apply ClaE in H0 as [_ [_ [_ H0]]]. assert (D ∈ TNeighS x X cT).
    { apply Theorem2b; try (apply ClaI)... }
    apply ClaE in H1. apply H0 in H1; tauto. } tauto.
Qed.

Theorem Theorem4d : ∀ A X cT, Topology X cT → A ⊂ X →
  Derivaed (Derivaed A X cT) X cT ⊂ A ⋃ Derivaed A X cT.
Proof with eauto.
  intros * Ht Hsub x Hx. destruct (classic (x ∈ A ⋃ Derivaed A X cT))...
  apply UnionNI in H as [Hxa Hxd].
  assert (Hx' := Hx); apply ClaE in Hx as [_ [_ [Hx _]]].
  apply LeTh4 in Hxd as [U [Hun Hue]]...
  assert (U ∈ TNeighS x X cT) by (apply ClaI; auto).
  pose proof Theorem2d x X cT Ht Hx as Hu.
  apply Hu in H as [V [Htv [Hvu Hp]]]; clear Hu. assert (V ⊂ X).
  { destruct Hun as [_ [_ [Hun _]]]. eapply ReSyTrP... }
  pose proof Theorem1 _ _ _ Ht H.
  pose proof Hp as Hp'. apply H0 in Hp; clear H H0.
  assert (V ∩ A - [x] = ∅).
  { AppE; [| exfalso0]. assert (V ∩ A - [x] ⊂ U ∩ A - [x]).
    { intros z Hz. apply ClaE in Hz as []. apply ClaI. split... }
    apply H0 in H. rewrite Hue in H. exfalso0. }
  assert (V ∩ A = ∅). { eapply SetBasicP... }
  assert (∀ y, y ∈ V → y ∉ A).
  { intros * Hy0 Hn. assert (y ∈ V ∩ A). { apply ClaI... }
    rewrite H0 in H1... exfalso0. }
  assert (∀ y, y ∈ V → V ∩ A - [y] = ∅).
  { intros. AppE; [| exfalso0]. apply ClaE in H3 as [].
    apply ClaE in H4 as []. apply H1 in H3... tauto. }
  assert (∀ y, y ∈ V → y ∉ Derivaed A X cT).
  { intros. intro. apply ClaE in H4 as [_ [_ [_ H4]]].
    pose proof H3. apply H2 in H3. apply Hp' in H5.
    apply ClaE in H5. apply H4 in H5. tauto. }
  assert (V ∩ Derivaed A X cT - [x] = ∅).
  { AppE; [| exfalso0]. apply ClaE in H4 as [].
    apply H3 in H4. apply ClaE in H5 as []. tauto. }
  apply ClaE in Hx' as [_ [_ [_ Hx']]]. apply ClaE in Htv.
  apply Hx' in Htv. tauto.
Qed.

Lemma ClosedSet : ∀ A X cT, Topology X cT → A ⊂ X →
  Closed A X cT ↔ X - A ∈ cT.
Proof with eauto.
  intros * Ht Hsub. apply SubSetmin in Hsub as Hsub'. split; intros Hp.
  - destruct Hp as [_ [_ Hp]]. eapply Theorem1...
    intros * Hx. apply ClaE in Hx as [Hx Hn].
    assert (x ∉ Derivaed A X cT). { intro. apply Hp in H; tauto. }
    apply LeTh4 in H as
      [U [[_ [_ [Hus [V [Hvo [Hvx Hvu]]]]]] Hue]]...
    apply SetBasicP in Hue... assert (U ⊂ X - A).
    { intros z Hz. apply ClaI. split... intro. assert (z ∈ U ∩ A).
      { apply ClaI... } rewrite Hue in H0. exfalso0. }
    apply ClaI. split... split... split...
    exists V. split... split... eapply ReSyTrP. split...
  - assert (∀ x, x ∈ X - A → TNeigh x (X - A) X cT ∧
      x ∉ Derivaed A X cT).
    { intros x Hx. apply (Theorem1 (X-A) _ _) in Ht...
      eapply Ht in Hp... apply ClaE in Hp... split...
      intro. apply ClaE in H as [_ [_ [_ H0]]]. apply H0 in Hp.
      assert (X - A ∩ A - [x] = ∅). { AppE; [| exfalso0].
        apply ClaE in H as [Hn H]. apply ClaE in Hn.
        apply ClaE in H; tauto. } tauto. }
    split... split... intros x Hx. destruct (classic (x ∈ A))...
    assert (x ∈ X - A). { apply ClaE in Hx as [_ [_ [Hx _]]].
      apply ClaI... } apply H in H1 as [_ H1]; tauto.
Qed.

(* Theorem5 *)
Definition cF X cT := \{λ U, U ⊂ X ∧ X - U ∈ cT \}.

Theorem Theorem5a : ∀ X cT, Topology X cT →
  X ∈ cF X cT ∧ ∅ ∈ cF X cT.
Proof with eauto.
  intros * Ht. split.
  - apply ClaI. split. intros z Hz... rewrite SetminId. apply Ht.
  - apply ClaI. split. intros z Hz; exfalso0.
    rewrite SetminEm. apply Ht.
Qed.

Theorem Theorem5b : ∀ A B X cT, Topology X cT →
  A ∈ cF X cT → B ∈ cF X cT → A ⋃ B ∈ cF X cT.
Proof with eauto.
  intros * Ht Ha Hb. apply ClaE in Ha as [Ha Hac].
  apply ClaE in Hb as [Hb Hbc]. assert (X - A ∩ X - B ∈ cT).
  { apply Ht... } apply SubSetmin1 in Ha.
  apply SubSetmin1 in Hb. rewrite <- Ha, <- Hb. 
  assert (X - (X - A) ⋃ X - (X - B) = X - (X - A ∩ X - B)).
  { AppE. rewrite TwDeMorgan; apply ClaI;
    apply ClaE in H0 as []... rewrite TwDeMorgan in H0;
    apply ClaI; apply ClaE in H0 as []... } rewrite H0.
  apply ClaI. split. intros z Hz. apply ClaE in Hz; tauto.
  rewrite SubSetmin1... intros z Hz. apply ClaE in Hz as [_ Hz].
  apply ClaE in Hz; tauto.
Qed.

Theorem Theorem5c : ∀ cF1 X cT, Topology X cT → cF1 ≠ ∅ →
  cF1 ⊂ cF X cT → ⋂cF1 ∈ cF X cT.
Proof with eauto.
  intros cF1 * Ht Hne Hsub. set \{λ A, A ⊂ X ∧ X - A ∈ cF1 \} as cT1.
  assert (HcT : cT1 ⊂ cT).
  { intros A Ha. apply ClaE in Ha as [Hsa Ha]. apply Hsub in Ha.
    apply ClaE in Ha as [Hc Ha]. rewrite SubSetmin1 in Ha... }
  apply Ht in HcT. assert (H4 : (X - ∪cT1) ∈ cF X cT).
  { apply ClaI. split. intros x Hx. apply ClaE in Hx; tauto.
    rewrite SubSetmin1... apply Ht in HcT. apply ClaE in HcT... }
  assert (H3 : (X - ∪(AAr X cF1)) = (X - ∪cT1)).
  { AppE; apply ClaE in H as [Hx Hn]; apply ClaI; split...
    - intro. elim Hn. apply ClaE in H as [B [Hb Hbt]].
      apply ClaE in Hbt as [Hbs Hb']. apply ClaI. exists (X - (X - B)).
      split. rewrite SubSetmin1... apply ClaI...
    - intro. elim Hn; clear Hn. apply ClaE in H as [B [Hb Hbt]].
      apply ClaE in Hbt as [T [Hbt Heq]]. apply ClaI. exists B.
      split... apply ClaI. split; subst.
      + intros z Hz. apply ClaE in Hz; tauto.
      + rewrite SubSetmin1... apply Hsub in Hbt.
        apply ClaE in Hbt; tauto. }
  rewrite DeMorganUI in H3; try apply AArP...
  assert (⋂ cF1 = ⋂ AAr X (AAr X cF1)).
  { AppE; apply ClaE in H; apply ClaI; intros.
    - apply ClaE in H0 as [B [Hb Heq]]. apply ClaE in Hb as
        [C [Hc Heq1]]. apply H. subst. rewrite SubSetmin1...
      apply Hsub in Hc. apply ClaE in Hc; tauto.
    - assert (y ⊂ X). { apply Hsub in H0. apply ClaE in H0; tauto. }
      apply H. apply ClaI. exists (X - y). split. apply ClaI...
      rewrite SubSetmin1... } rewrite H, H3...
Qed.

Lemma ClosedClosure : ∀ A X cT, Topology X cT → A ⊂ X →
  Closed A X cT ↔ A = Closure A X cT.
Proof with eauto.
  intros * Ht Hsub. split.
  - intros [_ [_ Hp]]. AppE. apply ClaI... apply ClaE in H as []...
  - intros Hp. split... split... intros z Hz.
    rewrite Hp. apply ClaI...
Qed.

(* Theorem6 *)
Theorem Theorem6a : ∀ X cT, Topology X cT → ∅ = Closure ∅ X cT.
Proof with eauto.
  intros. assert (∅ ⊂ X) by (intros z Hz; exfalso0)...
  apply ClosedClosure... apply ClosedSet...
  rewrite SetminEm. apply H.
Qed.

Theorem Theorem6b : ∀ A X cT, Topology X cT → A ⊂ X →
  A ⊂ Closure A X cT.
Proof. intros * Ht Hsub x Hx. apply ClaI; auto. Qed.

Theorem Theorem6c : ∀ A B X cT, Topology X cT → A ⊂ X → B ⊂ X →
  Closure (A ⋃ B) X cT = Closure A X cT ⋃ Closure B X cT.
Proof with eauto.
  intros * Ht Ha Hb. unfold Closure.
  rewrite Assoc, Theorem4c, <- Assoc, <- Assoc, <- Assoc...
  assert ((A ⋃ B) ⋃ Derivaed A X cT = (A ⋃ Derivaed A X cT) ⋃ B).
  { rewrite Assoc, Assoc, (Commu B _)... }
  rewrite H...
Qed.

Theorem Theorem6d : ∀ A X cT, Topology X cT → A ⊂ X →
  Closure (Closure A X cT) X cT = Closure A X cT.
Proof with eauto.
  intros * Ht Hsub. unfold Closure at 2.
  rewrite Theorem6c; try apply DerivaedP...
  unfold Closure. rewrite Assoc, <- (Assoc (Derivaed A X cT) _ _),
    Idem, <- Assoc, SubUnion... apply Theorem4d...
Qed.

Theorem ClosureClosed : ∀ A X cT, Topology X cT → A ⊂ X →
  Closed (Closure A X cT) X cT.
Proof with eauto.
  intros * Ht Hsub. apply ClosedClosure...
  intros z Hz. apply ClaE in Hz as []... apply ClaE in H. apply H.
  rewrite Theorem6d...
Qed.

(* Theorem2_4_7 *)
Lemma LeClosureEleI : ∀ A B X cT, Topology X cT → A ⊂ X → B ⊂ X →
  A ⊂ B → Closed B X cT → Closure A X cT ⊂ B.
Proof with eauto.
  intros. intros z Hz. apply ClaE in Hz as []...
  eapply Theorem4b in H2... apply H2 in H4. apply H3 in H4...
Qed.

Lemma ClosureEleI : ∀ A X cT, Topology X cT → A ⊂ X →
  Closure A X cT = ⋂\{λ B, B ∈ cF X cT /\ A ⊂ B \}.
Proof with eauto.
  intros * Ht Hsub. apply ReSyTrP... split.
  - assert (Ha : A ⊂ ⋂\{λ B, B ∈ cF X cT /\ A ⊂ B \}).
    { intros x Hx. apply ClaI; intros B Hb.
      apply ClaE in Hb as [_ Hb]... }
    assert (Hb : ⋂\{λ B, B ∈ cF X cT /\ A ⊂ B \} ∈ cF X cT).
    { apply Theorem5c... apply EmptyNE. exists X.
      apply ClaI; split... apply ClaI. split. intros z Hz...
      rewrite SetminId; apply Ht.
      intros z Hz. apply ClaE in Hz; tauto. }
    apply ClaE in Hb as [Hct Hb]. apply ClosedSet in Hb...
    apply LeClosureEleI...
  - intros z Hz. apply ClaE in Hz.
    assert (Closure A X cT ∈ \{λ B, B ∈ cF X cT /\ A ⊂ B \}).
    { apply ClaI. split. apply ClaI. assert (Closure A X cT ⊂ X).
      {intros x Hx. apply ClaE in Hx as []...
       apply ClaE in H as [_ [_ [H _]]]... }
      split... assert (Closed (Closure A X cT) X cT).
      { apply ClosureClosed... } apply ClosedSet...
      intros x Hx. apply ClaI... } apply Hz in H...
Qed.

Definition Kuratowski X c := Mapping c cP(X) cP(X) /\
  (c[∅] = ∅) /\ (∀ A, A ∈ cP(X) → A ⊂ c[A]) /\
  (∀ A B, A ∈ cP(X) → B ∈ cP(X) → c[A ⋃ B] = c[A] ⋃ c[B]) /\
  (∀ A, A ∈ cP(X) → c[c[A]] = c[A]).

(* Theorem7 *)
Theorem Theorem7 : ∀ X c, Kuratowski X c →
  exists! cT, Topology X cT ∧ (∀ A, A ⊂ X → c[A] = Closure A X cT).
Proof with eauto.
  intros * [Hm [H1 [H2 [H3 H4]]]].
  set (cT := \{λ U, U ⊂ X /\ c[X - U] = X - U\}). exists cT.
  assert (Ht : Topology X cT).
  { assert (He : ∅ ∈ cT).
    { apply ClaI. split. intros z Hz; exfalso0.
      rewrite SetminEm. apply ReSyTrP... split.
      + assert (X ∈ cP( X)). { apply ClaI. intros z Hz... }
        eapply PropertyValue in H... apply Hm in H.
        apply ClaE' in H as [_ H]. apply ClaE in H...
      + apply H2. apply ClaI. intros z Hz... } repeat split...
    - intros A Ha. apply ClaE in Ha. apply ClaI; tauto.
    - apply ClaI. split. intros z Hz... rewrite SetminId...
    - intros * Ha Hb. apply ClaE in Ha as [Ha' Ha].
      apply ClaE in Hb as [Hb' Hb]. apply ClaI. split.
      intros z Hz. apply ClaE in Hz as [Hz _]...
      rewrite TwDeMorgan, (H3 (X - A) (X - B)), Ha, Hb;
      try (apply ClaI; apply SubSetmin)...
    - assert (Hab : ∀ A B, A ⊂ X → B ⊂ X → A ⊂ B → c[A] ⊂ c[B]).
      { intros. assert (B = A ⋃ B - A).
        { AppE. apply ClaI. destruct (classic (x ∈ A))...
          right. apply ClaI... apply ClaE in H6 as []...
          apply ClaE in H6. tauto. } assert (B - A ⊂ X).
        { intros x Hx. apply ClaE in Hx as [Hx _]... }
        rewrite H6, H3; try (apply ClaI; tauto).
        intros x Hx. apply ClaI... }
      intros cT1 Hsub. apply ClaI. assert (Ht : ∪ cT1 ⊂ X).
      { intros x Hx. apply ClaE in Hx as [y [Hx Hy]].
        apply Hsub in Hy. apply ClaE in Hy as [Hy _]... } split...
      destruct (classic (cT1 = ∅)).
      { subst. rewrite EmEleU. apply ClaE in He; tauto. }
      apply ReSyTrP... split; revgoals.
      + apply H2. apply ClaI. intros z Hz. apply ClaE in Hz; tauto.
      + assert (∀ A1, A1 ∈ cT1 → X - (∪cT1) ⊂ X - A1).
        { intros. rewrite DeMorganUI... apply EleIP. apply ClaI... }
        assert (∀ A1, A1 ∈ cT1 → c[X - (∪ cT1)] ⊂ X - A1).
        { intros. pose proof H5. apply Hsub in H5.
          apply ClaE in H5 as []. rewrite <- H7.
          apply SubSetmin in Ht; apply SubSetmin in H5. apply Hab... }
        intros z Hz. rewrite DeMorganUI... apply ClaI. intros.
        apply ClaE in H6 as [A1 []]. apply H5 in H6. subst... }
  assert (Htp : ∀ A, A ⊂ X → c[A] = Closure A X cT).
  { intros. assert (A ∈ cP(X)) by (apply ClaI; auto). assert (c[A] ⊂ X).
    { eapply PropertyValue in H0... apply Hm in H0.
      apply ClaE' in H0 as []. apply ClaE in H5... }
    apply ReSyTrP... split.
    - assert (Closed (Closure A X cT) X cT). { apply ClosureClosed... }
      assert (Closure A X cT ⊂ X). { apply ClosureP... }
      apply ClosedSet in H6... apply ClaE in H6 as [].
      rewrite SubSetmin1 in H8... unfold Closure in *.
      rewrite <- H8, H3... intros z Hz. apply ClaI...
      apply ClaI. apply DerivaedP.
    - rewrite ClosureEleI... apply EleIP. apply ClaI.
      split; [| apply H2; auto]. apply ClaI. split... apply ClaI.
      split. apply SubSetmin... rewrite SubSetmin1... } split...
  intros cT1 [Ht1 Htp1]. apply ExtAx; intros A. split; intros Hp.
  - apply ClaE in Hp as []. apply SubSetmin in H as Hx'.
    assert (Closed (X - A) X cT1).
    { apply ClosedClosure... apply Htp1 in Hx'. rewrite H0 in Hx'... }
    pose proof ClosedSet _ _ _ Ht1 Hx'. apply H6 in H5.
    rewrite SubSetmin1 in H5...
  - apply Ht1 in Hp as Ha; apply ClaE in Ha. apply ClaI. split...
    apply SubSetmin in Ha as Ha'. apply SubSetmin1 in Ha.
    rewrite <- Ha in Hp.  apply ClosedSet in Hp...
    apply ClosedClosure in Hp... apply Htp1 in Ha'. rewrite Ha'...
Qed.

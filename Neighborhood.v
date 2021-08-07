Require Export Topology.

(* TNeigh *)
Definition TNeigh x U X cT := Topology X cT ∧ x ∈ X ∧ U ⊂ X ∧
  ∃ V, V ∈ cT ∧ x ∈ V ∧ V ⊂ U.

Definition TNeighS x X cT := \{λ U, TNeigh x U X cT \}.

Fact TNeighP : ∀ x U X cT,
  Topology X cT → x ∈ U → U ∈ cT → TNeigh x U X cT.
Proof with eauto.
  intros * Ht Hx Hu. split... assert (Hxx : U ⊂ X).
  { apply Ht in Hu. apply ClaE in Hu... } split... split...
  exists U. repeat split... intros z Hz...
Qed.

(* Theorem1 *)
Definition Ux x U cT := ∪\{λ V, x ∈ U ∧ V ∈ cT ∧ x ∈ V ∧ V ⊂ U \}.

Lemma LeTh1 : ∀ U, U = ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}).
Proof with eauto.
  intro. AppE. apply ClaI. exists [x]. split. apply SingI...
  apply ClaI. exists x. split... apply ClaE in H as [y [Hy Heq]].
  apply ClaE in Heq as [z [Hz Heq]]. subst. apply SingE in Hy. subst...
Qed.

Theorem Theorem1 : ∀ U X cT, Topology X cT → U ⊂ X →
  (U ∈ cT ↔ ∀ x, x ∈ U → U ∈ TNeighS x X cT).
Proof with eauto.
  intros * Ht Hsub. split; intros Hp.
  - intros * Hx. apply ClaI. apply TNeighP...
  - destruct (classic (U = ∅)). subst; apply Ht.
    assert (H1 : ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}) ⊂
       ∪(\{λ t, ∃ x, x ∈ U ∧ t = Ux x U cT\})).
    { intros z Hz. apply ClaE in Hz as [y [Hy Hz]]. apply ClaE
        in Hz as [x0 [Hx0 Hz]]. subst... apply ClaE in Hy. subst...
      assert (Hx0' := Hx0). apply Hp in Hx0. apply ClaE in Hx0.
      apply ClaI. exists (Ux x0 U cT). split. apply ClaI.
      assert (Hn := Hx0). destruct Hx0 as [_ [_ [_ [V [Hv [Hx0 Hvu]]]]]].
      exists V. split... apply ClaI... apply ClaI... }
    assert (H2 : ∪(\{λ t, ∃ x, x ∈ U ∧ t = Ux x U cT\}) ⊂ U).
    { intros z Hz. apply ClaE in Hz as [y [Hy Hz]].
      apply ClaE in Hz as [t [Htu Hz]]. subst...
      apply ClaE in Hy as [e [Hz Hy]]. apply ClaE in Hy. apply Hy... }
    assert (Hg : U = ∪(\{λ t, ∃ x, x ∈ U ∧ t = Ux x U cT\})).
    { apply ReSyTrP... split... rewrite <- LeTh1 in H1... }
    rewrite Hg. apply Ht. intros V Hv.
    apply ClaE in Hv as [x [Hx Heq]]. subst.
    apply Ht. intros z Hz. apply ClaE in Hz; tauto.
Qed.

(* Theorem2_3_2 *)
Theorem Theorem2a : ∀ x X cT, Topology X cT → x ∈ X →
  TNeighS x X cT ≠ ∅ ∧ (∀ U, U ∈ TNeighS x X cT → x ∈ U).
Proof with eauto.
  intros * Ht Hx. split.
  - assert (X ∈ TNeighS x X cT).
    { apply ClaI. split... split... split. intros z Hz...
      exists X. split. apply Ht. split... intros z Hz... }
    intro. rewrite H0 in H. exfalso0.
  - intros * Hu. apply ClaE in Hu as [_ [_ [_ [V [_ [Hv Hsub]]]]]]...
Qed.

Theorem Theorem2b : ∀ x X cT, Topology X cT → x ∈ X →
  (∀ U V, U ∈ TNeighS x X cT → V ∈ TNeighS x X cT →
  U ∩ V ∈ TNeighS x X cT).
Proof with eauto.
  intros * Ht Hx * Hu Hv.
  apply ClaE in Hu as [_ [_ [Hux [U0 [Ho1 [Hu0 Hsub1]]]]]].
  apply ClaE in Hv as [_ [_ [Hvx [V0 [Ho2 [Hv0 Hsub2]]]]]].
  assert (Huv : x ∈ U0 ∩ V0 ∧ U0 ∩ V0 ⊂ U ∩ V).
  { split. apply ClaI; tauto. intros z Hz.
    apply ClaE in Hz as [Hzu Hzv]. apply ClaI. split... }
  apply ClaI. split... split... split. intros z Hz.
  apply ClaE in Hz as [Hz1 _]... exists (U0 ∩ V0).
  split; try apply Ht...
Qed.

Theorem Theorem2c : ∀ x X cT, Topology X cT → x ∈ X →
  ∀ U V, U ∈ TNeighS x X cT → V ⊂ X → U ⊂ V → V ∈ TNeighS x X cT.
Proof with eauto.
  intros * Ht Hx * Hu Hv Hsub.
  apply ClaE in Hu as [_ [_ [Hux [U0 [Hou [Hu0 Hsub1]]]]]].
  apply ClaI. split... split... split...
  exists U0. repeat split... eapply ReSyTrP...
Qed.

Theorem Theorem2d : ∀ x X cT, Topology X cT → x ∈ X →
  ∀ U, U ∈ TNeighS x X cT → ∃ V, V ∈ TNeighS x X cT ∧ V ⊂ U ∧
  (∀ y, y ∈ V → V ∈ TNeighS y X cT).
Proof with eauto.
  intros * Ht Hx * Hu. assert (Hu' := Hu).
  apply ClaE in Hu as [_ [_ [Hux [V [Hvo [Hvx Hsub]]]]]].
  exists V. split. apply ClaI. split... split... split.
  eapply ReSyTrP... exists V. split... split... intros z HZ...
  split... apply Theorem1... eapply ReSyTrP...
Qed.

(* Theorem3 *)
Theorem Theorem3 : ∀ f X, Mapping f X cP(cP(X)) →
  (∀ x, x ∈ X → f[x] ⊂ cP(X) /\
  f[x] ≠ ∅ /\ (∀ U, U ∈ f[x] → x ∈ U) /\
  (∀ U V, U ∈ f[x] → V ∈ f[x] → U ∩ V ∈ f[x]) /\
  (∀ U V, U ∈ f[x] → V ⊂ X → U ⊂ V → V ∈ f[x]) /\
  (∀ U, U ∈ f[x] → ∃ V, V ∈ f[x] ∧ V ⊂ U ∧
  (∀ y, y ∈ V → V ∈ f[y]))) →
  exists! cT, (Topology X cT ∧ ∀ x, x ∈ X → f[x] = TNeighS x X cT).
Proof with eauto.
  intros * Hf Hp. set (cT :=
    \{λ U, U ⊂ X ∧ ∀ x, x ∈ U → U ∈ f[x] \}). exists cT.
  assert (Hs : cT ⊂ cP( X)).
  { intros A Ha. apply ClaE in Ha. apply ClaI. tauto. }
  assert (Ht : Topology X cT).
  { repeat split...
    - apply ClaI. split. intros z Hz... intros.
      apply Hp in H as [Hsub [H1 [_ [_ [H3 _]]]]]. 
      apply EmptyNE in H1 as [U H1]. pose proof H1.
      apply Hsub in H; apply ClaE in H.
      apply (H3 U X) in H1... intros z Hz...
    - apply ClaI. split; intros z Hz; exfalso0.
    - intros * Ha Hb. apply ClaE in Ha as [Hsuba Ha].
      apply ClaE in Hb as [Hsubb Hb]. apply ClaI. assert (A ∩ B ⊂ X).
      { intros x Hx. apply ClaE in Hx as []... } split...
      intros. apply H in H0 as H1. apply ClaE in H0 as [Hzl Hzr].
      apply Ha in Hzl; apply Hb in Hzr. apply Hp...
    - intros cT1 Hsubt. apply ClaI. assert (∪cT1 ⊂ X).
      { intros x Hx. apply ClaE in Hx as [y [Hx Hy]].
        apply Hsubt in Hy. apply ClaE in Hy as [Hy _]... } split...
      intros. apply ClaE in H0 as [U [Hx Hu]]. pose proof Hu.
      apply Hsubt in Hu. apply ClaE in Hu as [Hu Hup].
      apply Hu in Hx as Hx'. apply Hup in Hx.
      apply Hp in Hx' as [_ [_ [_ [_ [Hx' _]]]]].
      apply (Hx' U (∪cT1))... intros t Ht. apply ClaI. exists U... }
  assert (Htp : ∀ x, x ∈ X → f[x] = TNeighS x X cT).
  { intros. pose proof H. apply Hp in H.
    destruct H as [Hsub [_ [H1' [_ [H3 H4]]]]].
    apply ExtAx; intros U; split; intros Hu.
    + pose proof Hu. apply Hsub in H. apply ClaE in H.
      apply H4 in Hu as [V [Hv [Huv HP]]]. assert (V ∈ cT).
      { apply ClaI. split... eapply ReSyTrP... }
      apply ClaI. split... split... split...
    + apply ClaE in Hu as [_ [_ [Hu [V [Hv [Hvx Huv]]]]]].
      apply ClaE in Hv as [_ Hv]. apply Hv in Hvx. apply (H3 V U)... }
  split... intros cT1 [Ht1 Htp1].
  apply ExtAx. intro W. split; intros.
  - apply ClaE in H as []. pose proof Theorem1 _ _ _ Ht1 H.
    apply H1. intros. apply H in H2 as Hx.
    apply H0 in H2. rewrite <- Htp1...
  - apply Ht1 in H as Hw; apply ClaE in Hw. apply ClaI. split...
    intros. pose proof Theorem1 _ _ _ Ht1 Hw.
    pose proof H0. apply H1 in H0... rewrite Htp1... 
Qed.
Require Export Ensemble.

(* Topology Spaces *)
Definition Topology X cT := cT ⊂ cP(X) ∧
  X ∈ cT ∧ ∅ ∈ cT ∧ (∀ A B, A ∈ cT → B ∈ cT → A ∩ B ∈ cT) ∧
  (∀ cT1, cT1 ⊂ cT → ∪cT1 ∈ cT).

Definition Indiscrete  X := [X] ⋃ [∅].
Example IndiscreteP : ∀ X, Topology X (Indiscrete  X).
Proof with eauto.
  intros. repeat split.
  - intros A Ha. apply ClaE in Ha as []; apply ClaE in H; apply ClaI;
    subst; intros z Hz... exfalso0.
  - apply ClaI. left; apply ClaI...
  - apply ClaI. right; apply ClaI...
  - unfold Indiscrete. intros. apply SetBasicP1...
  - intros. unfold Indiscrete. apply EleUP...
Qed.

Definition Discrete X := cP(X).
Example DiscreteP : ∀ X, Topology X (Discrete X).
Proof with eauto.
  intros. repeat split. intros A Ha... apply ClaI; intros A Ha...
  apply ClaI; intros A Ha; exfalso0.
  intros * Ha Hb. apply ClaE in Ha; apply ClaE in Hb. apply ClaI.
  intros z Hz. apply ClaE in Hz as [H _]...
  intros. apply ClaI. intros x Hx. apply ClaE in Hx as [A [Hx Ha]].
  apply H in Ha. apply ClaE in Ha...
Qed.
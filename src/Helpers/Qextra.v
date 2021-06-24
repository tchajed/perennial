Require Import Qcanon ssreflect.
From stdpp Require Import numbers.
Require Import Psatz.
Require Import QArith.
Local Open Scope Q_scope.

Lemma Qp_split_lt (q1 q2: Qp) :
  (q1<q2)%Qp ->
  ∃ q', (q1 + q' = q2)%Qp.
Proof.
  rewrite Qp_lt_sum.
  intros [r EQ]. exists r. done.
Qed.

Lemma Qp_split_1 (q: Qp) :
  (q<1)%Qp ->
  ∃ q', (q + q' = 1)%Qp.
Proof. intros. by eapply Qp_split_lt. Qed.

Theorem Qp_div_2_lt (q: Qp) : (q/2 < q)%Qp.
Proof.
  apply Qp_lt_sum. exists (q/2)%Qp.
  rewrite Qp_div_2. done.
Qed.

Require Import Lqa.
Require Import Lra.
Require Import QArith.
Require Import Reals.

Lemma rhelper1 (q : R) :
  (/ 2 < q)%R →
  (q < 1)%R →
  (1 < q + (1 - q + (q + / 2 - 1) / 2))%R.
Proof. lra. Qed.

Lemma rhelper2 (r : R) :
  (/ 2 < r)%R →
  (r < 1)%R →
  (0 < 1 + - r + (r + / 2 - 1) / 2)%R.
Proof. lra. Qed.

Lemma rhelper3 (r : R) :
  (/ 2 < r)%R →
  (r < 1)%R →
  (0 < / 2 + - (1 + - r + (r + / 2 - 1) / 2))%R.
Proof. lra. Qed.

Lemma R_plus_inv_2_gt_1_split q:
  ((/2  < q)%R → ∃ q1 q2, 0 < q1 ∧ 0 < q2 ∧ (q1 + q2)%R = /2 ∧ 1 < q + q1)%R.
Proof.
  intros Hlt.
  assert (q < 1 ∨ 1 <= q)%R as [Hle|Hgt].
  { lra. }
  - set (q1 := ((1 - q)%R + ((q + /2) - 1)/2)%R).
    set (q2 := (/2 - q1)%R).
    exists q1, q2. split_and!.
    * rewrite /q1. lra.
    * rewrite /q2/q1. lra.
    * assert (1 - q < /2)%R.
      { lra. }
      rewrite /q2/q1.
      lra.
    * rewrite /q1. clear q1 q2. apply rhelper1; auto.
  - exists (/4)%R, (/4)%R.
    split; lra.
Qed.

  Require Import Lqa.

Lemma Q_plus_inv_2_gt_1_split q:
  ((/2  < q)%Q → ∃ q1 q2, 0 < q1 ∧ 0 < q2 ∧ Qred (q1 + q2)%Q = Qred (/2) ∧ 1 < q + q1)%Q.
Proof.
  intros Hlt.
  assert (q < 1 ∨ 1 <= q)%Q as [Hle|Hgt].
  { lra. }
  - set (q1 := ((1 - q)%Q + ((q + /2) - 1)/2)%Q).
    set (q2 := (/2 - q1)%Q).
    exists q1, q2. split_and!.
    * rewrite /q1.
      apply Qreals.Rlt_Qlt.
      repeat (rewrite ?Qreals.Q2R_plus ?Qreals.Q2R_inv ?Qreals.Q2R_opp
              ?Qreals.Q2R_div ?Qreals.Q2R_minus);
        try (by inversion 1).
      rewrite RMicromega.Q2R_0.
      rewrite RMicromega.Q2R_1.
      assert (Q2R 2 = 2%R) as Heq2.
      { replace 2%Q with (1 + 1)%Q by auto.
        rewrite ?Qreals.Q2R_plus.
        rewrite RMicromega.Q2R_1; auto with *. }
      rewrite ?Heq2.
      apply rhelper2.
      { rewrite -Heq2. rewrite -Qreals.Q2R_inv; first by inversion 1.
        apply Qreals.Qlt_Rlt. auto. }
      { rewrite -RMicromega.Q2R_1.
        apply Qreals.Qlt_Rlt. auto. }
    * rewrite /q2/q1.
      apply Qreals.Rlt_Qlt.
      repeat (rewrite ?Qreals.Q2R_plus ?Qreals.Q2R_inv ?Qreals.Q2R_opp
              ?Qreals.Q2R_div ?Qreals.Q2R_minus);
        try (by inversion 1).
      rewrite RMicromega.Q2R_0.
      rewrite RMicromega.Q2R_1.
      assert (Q2R 2 = 2%R) as Heq2.
      { replace 2%Q with (1 + 1)%Q by auto.
        rewrite ?Qreals.Q2R_plus.
        rewrite RMicromega.Q2R_1; auto with *. }
      rewrite ?Heq2.
      apply rhelper3.
      { rewrite -Heq2. rewrite -Qreals.Q2R_inv; first by inversion 1.
        apply Qreals.Qlt_Rlt. auto. }
      { rewrite -RMicromega.Q2R_1.
        apply Qreals.Qlt_Rlt. auto. }
    * apply Qred_complete.
      apply Qreals.eqR_Qeq. rewrite /q2/q1.
      repeat (rewrite ?Qreals.Q2R_plus ?Qreals.Q2R_inv ?Qreals.Q2R_opp
              ?Qreals.Q2R_div ?Qreals.Q2R_minus);
        try (by inversion 1).
      rewrite RMicromega.Q2R_1.
      assert (Q2R 2 = 2%R) as ->.
      { replace 2%Q with (1 + 1)%Q by auto.
        rewrite ?Qreals.Q2R_plus.
        rewrite RMicromega.Q2R_1; auto with *. }
      generalize (Q2R q). clear.
      intros. field.
    * rewrite /q1.
      apply Qreals.Rlt_Qlt.
      repeat (rewrite ?Qreals.Q2R_plus ?Qreals.Q2R_inv ?Qreals.Q2R_opp
              ?Qreals.Q2R_div ?Qreals.Q2R_minus);
        try (by inversion 1).
      rewrite RMicromega.Q2R_1.
      assert (Q2R 2 = 2%R) as Heq2.
      { replace 2%Q with (1 + 1)%Q by auto.
        rewrite ?Qreals.Q2R_plus.
        rewrite RMicromega.Q2R_1; auto with *. }
      rewrite ?Heq2.
      apply rhelper1.
      { rewrite -Heq2. rewrite -Qreals.Q2R_inv; first by inversion 1.
        apply Qreals.Qlt_Rlt. auto. }
      { rewrite -RMicromega.Q2R_1.
        apply Qreals.Qlt_Rlt. auto. }
  - exists (/4)%Q, (/4)%Q.
    split_and!; try constructor.
    * apply (Qle_lt_trans _ (1 + 0)).
      { eauto with *. }
      rewrite Qplus_comm.
      rewrite (Qplus_comm q).
      apply Qplus_lt_le_compat; auto.
      constructor.
Qed.

Lemma Qp_plus_inv_2_gt_1_split q:
  ((/2  < q)%Qp → ∃ q1 q2, q1 + q2 = /2 ∧ 1 < q + q1)%Qp.
Proof.
  intros. destruct q as (q&Hpos). destruct q as (q&Hcanon).
  edestruct (Q_plus_inv_2_gt_1_split q) as (q1&q2&?&?&?&?).
  { eauto with *. }
  unshelve (eexists _).
  { unshelve (econstructor).
    - apply (Qcanon.Q2Qc q1).
    - apply Qred_lt; auto.
  }
  unshelve (eexists _).
  { unshelve (econstructor).
    - apply (Qcanon.Q2Qc q2).
    - apply Qred_lt; auto.
  }
  rewrite //=.
  split.
  - rewrite /Qp_add//=.
    apply Qp_to_Qc_inj_iff.
    rewrite /Qcanon.Qcplus//=.
    apply Qcanon.Q2Qc_eq_iff.
    transitivity (Qplus' q1 q2).
    { rewrite Qplus'_correct.
      apply Qplus_comp; apply Qred_correct. }
    { rewrite /Qplus'. rewrite H2. constructor. }
  - rewrite /Qcanon.Qclt => //=.
    rewrite ?Qred_correct; auto.
Qed.

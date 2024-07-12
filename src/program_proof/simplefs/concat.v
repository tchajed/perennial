From stdpp Require Import base list.
From Coq Require Import ssreflect.

From Perennial.Helpers Require Import NatDivMod Integers Tactics.

Local Open Scope Z.

#[local] Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Set SsrOldRewriteGoalsOrder.

Definition length_uniform {A: Type} (l: list (list A)) (n: nat) :=
  ∀ i x, l !! i = Some x → length x = n.

Lemma length_uniform_u64_le (l: list u64) : length_uniform (u64_le <$> l) 8%nat.
Proof.
  intros i x H.
  fmap_Some in H.
  rewrite u64_le_length //.
Qed.

Lemma length_uniform_u32_le (l: list u32) : length_uniform (u32_le <$> l) 4%nat.
Proof.
  intros i x H.
  fmap_Some in H.
  rewrite u32_le_length //.
Qed.

Hint Resolve length_uniform_u64_le length_uniform_u32_le : core.

Lemma length_uniform_app_inv {A} (a: list A) (l: list (list A)) n :
  length_uniform (a :: l) n →
  length a = n ∧ length_uniform l n.
Proof.
  rewrite /length_uniform.
  intros Hlen.
  pose proof (Hlen 0%nat a) as H; simpl in H.
  split; auto.
  intros.
  pose proof (Hlen (S i)). auto.
Qed.

Lemma length_concat_uniform {A: Type} (l: list (list A)) (n: nat) :
  length_uniform l n →
  length (concat l) = (length l * n)%nat.
Proof.
  intros Hlen.
  induction l; simpl; auto.
  apply length_uniform_app_inv in Hlen as [Ha Hlen].
  intuition.
  rewrite length_app.
  rewrite H //.
  lia.
Qed.

Lemma Nat_mod_add_modulus n k :
  ((n + k) `mod` k = n `mod` k)%nat.
Proof.
  rewrite (Nat.Div0.add_mod n k k).
  rewrite Nat.Div0.mod_same.
  rewrite Nat.add_0_r.
  rewrite Nat.Div0.mod_mod.
  reflexivity.
Qed.

Lemma lookup_concat_uniform {A: Type} (l: list (list A)) (n: nat) :
  length_uniform l n →
  n ≠ 0%nat →
  ∀ i, concat l !! i =
         (l !! (i `div` n)%nat) ≫= λ (ll: list A), ll !! (i `mod` n)%nat.
Proof.
  intros Hlen Hn.
  induction l.
  - simpl. intros. rewrite lookup_nil //.
  - apply length_uniform_app_inv in Hlen as [Ha Hlen].
    simpl. intros i.
    destruct (decide (i < n)%nat).
    + rewrite lookup_app_l; [ | lia ].
      rewrite Nat.div_small // /=.
      rewrite Nat.mod_small //.
    + rewrite lookup_app_r; [ | lia ].
      rewrite IHl //.
      rewrite Ha.
      replace i with (1*n + (i-n))%nat at 2 by lia.
      rewrite Nat.div_add_l; [ | lia ].
      simpl.
      f_equal.
      f_equal.
      rewrite -(Nat_mod_add_modulus (i-n) n).
      replace (i - n + n)%nat with i by lia; auto.
Qed.

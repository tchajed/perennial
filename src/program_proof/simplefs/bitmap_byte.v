From stdpp Require Import base numbers list_numbers.
From Coq Require Import ssreflect.
From Perennial.Helpers Require Import Integers.
From Perennial.Helpers Require Import bytes.

Import Coq.Init.Nat.

#[local] Open Scope Z.

(* This file contains two proofs that are done by exploding all cases (eg, all
256 values for a [w8]). These proofs are rather slow (roughly 20s), so they make
iterating on the main bitmap tedious. *)

Lemma split_div_mod_8 (i: nat) :
  ∃ (i1 i2: nat),
    (i `div` 8 = i1 ∧
    i `mod` 8 = i2 ∧
    i = 8 * i1 + i2 ∧
    8 * i1 ≤ i ∧
    0 ≤ i2 < 8)%nat.
Proof.
  eexists _, _; split_and!; [ eauto | eauto | .. ].
  - rewrite {1}(Nat.div_mod i 8) //.
  - apply Nat.Div0.mul_div_le; lia.
  - apply Nat.mod_bound_pos; lia.
  - apply Nat.mod_bound_pos; lia.
Qed.

Lemma Some_inv {A} (a b: A) : Some a = Some b → a = b.
Proof. inversion 1; auto. Qed.

Lemma Some_eq_iff {A} (a b: A) : Some a = Some b ↔ a = b.
Proof. split; [ apply Some_inv | congruence ]. Qed.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Transparent w8_instance.w8.
Lemma set_bit_get (b: w8) (i: u64) bit :
  byte_to_bits (word.or b (word.slu (W8 1) (W8 (uint.Z i `mod` 8))))
  !! Z.to_nat (uint.Z i `mod` 8) = Some bit → true = bit.
Proof.
    byte_cases b; bit_off_cases (uint.Z i `mod` 8);
      intros H%Some_inv; exact H.
Qed.
Opaque w8_instance.w8.

Opaque Nat.div Nat.modulo.

Lemma testbit_set_bit (b: w8) (i: Z) (i': nat) :
  0 ≤ i < 8 →
  (i' < 8)%nat →
  Z.testbit (uint.Z (word.or b (word.slu (W8 1) (W8 i)))) (Z.of_nat i') =
  if decide (i = Z.of_nat i') then true else Z.testbit (uint.Z b) (Z.of_nat i').
Proof.
  intros Hbound Hbound'.
  (* this order is slightly faster than doing all the destructs first (it
  computes the decide first) *)
  bit_off_cases i; bit_off_cases i';
    simpl;
    byte_cases b;
    vm_compute;
    try reflexivity.
Qed.

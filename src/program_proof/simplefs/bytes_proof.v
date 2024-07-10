From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.Helpers Require Import NatDivMod bytes.
Import Nat.

From Goose.github_com Require Import tchajed.simplefs.bitmap.

From Perennial.program_proof.simplefs Require Import bitmap_byte.

Set Default Proof Using "Type".

#[local] Unset Printing Projections.
#[local] Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section proof.
Context `{!heapGS Σ}.

Lemma inj_lit_byte (b1 b2: w8) :
  #b1 = #b2 ↔ b1 = b2.
Proof.
  split; [ | congruence ].
  inversion 1; auto.
Qed.

Lemma bool_decide_byte_val_eq (b1 b2: w8) :
  bool_decide (#b1 = #b2) = bool_decide (b1 = b2).
Proof.
  apply bool_decide_ext.
  rewrite inj_lit_byte //.
Qed.

Lemma bool_decide_byte_val_neq (b1 b2: w8) :
  bool_decide (#b1 ≠ #b2) = bool_decide (b1 ≠ b2).
Proof.
  apply bool_decide_ext.
  rewrite inj_lit_byte.
  split; try congruence.
Qed.

Lemma getBit_pure (b: w8) (i: w64) :
  uint.Z i < 8 →
  byte_to_bits b !! uint.nat i =
  Some (bool_decide (word.and b (word.slu (W8 1) (W8 (uint.Z i))) ≠ W8 0)).
Proof.
  intros.
  bit_off_cases (uint.Z i); byte_cases b; vm_compute; reflexivity.
Qed.

Theorem wp_getBit (b : w8) (i : u64) :
  {{{ ⌜uint.Z i < 8⌝ }}}
    getBit #b #i
  {{{ (bit:bool), RET #bit; ⌜byte_to_bits b !! (uint.nat i) = Some bit⌝ }}}.
Proof.
  (*@ func getBit(b byte, i uint64) bool {                                    @*)
  (*@     return b&(1<<i) != 0                                                @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "%".
  wp_call. iModIntro.
  iApply "HΦ".
  iPureIntro.
  rewrite -bool_decide_not bool_decide_byte_val_neq.
  rewrite getBit_pure //.
Qed.

Lemma setBit_pure (b: w8) (i: Z) :
  0 ≤ i < 8 →
  byte_to_bits (word.or b (word.slu (W8 1) (W8 i))) =
  <[Z.to_nat i:=true]> (byte_to_bits b).
Proof.
  intros.
  bit_off_cases i; byte_cases b; reflexivity.
Qed.

Theorem wp_setBit (b : w8) (i : u64) :
  {{{ ⌜uint.Z i < 8⌝ }}}
    setBit #b #i
  {{{ (b': w8), RET #b'; ⌜byte_to_bits b' = <[ uint.nat i := true ]> (byte_to_bits b)⌝ }}}.
Proof.
  (*@ func setBit(b byte, i uint64) byte {                                    @*)
  (*@     return b | 1<<i                                                     @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "%".
  wp_call. iModIntro.
  iApply "HΦ".
  iPureIntro.
  rewrite setBit_pure //. word.
Qed.

Lemma clearBit_pure (b: w8) (i: Z) :
  0 ≤ i < 8 →
  byte_to_bits (word.and b (word.not (word.slu (W8 1) (W8 i)))) =
  <[Z.to_nat i:=false]> (byte_to_bits b).
Proof.
  intros.
  bit_off_cases i; byte_cases b; reflexivity.
Qed.

Theorem wp_clearBit (b : w8) (i : u64) :
  {{{ ⌜uint.Z i < 8⌝ }}}
    clearBit #b #i
  {{{ (b': w8), RET #b'; ⌜byte_to_bits b' = <[ uint.nat i := false ]> (byte_to_bits b)⌝ }}}.
Proof.
  (*@ func clearBit(b byte, i uint64) byte {                                  @*)
  (*@     return b & ^(1 << i)                                                @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "%".
  wp_call. iModIntro.
  iApply "HΦ".
  iPureIntro.
  rewrite clearBit_pure //. word.
Qed.

End proof.

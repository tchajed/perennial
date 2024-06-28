From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import bytes.
Import Nat.

From Goose.github_com Require Import tchajed.simplefs.

#[local] Unset Printing Projections.

Definition bytes_to_bits (data: list u8): list bool :=
  concat (byte_to_bits <$> data).

Definition length_uniform {A: Type} (l: list (list A)) (n: nat) :=
  ∀ i x, l !! i = Some x → length x = n.

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
  autorewrite with len.
  rewrite H //.
  lia.
Qed.

Lemma Nat_mod_add_modulus n k :
  ((n + k) `mod` k = n `mod` k)%nat.
Proof.
  rewrite (Div0.add_mod n k k).
  rewrite Div0.mod_same.
  rewrite Nat.add_0_r.
  rewrite Div0.mod_mod.
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

Lemma bytes_to_bits_uniform block :
  length_uniform (byte_to_bits <$> block) 8%nat.
Proof.
  intros i x H.
  fmap_Some in H as b.
  len.
Qed.

Hint Resolve bytes_to_bits_uniform : core.

Lemma bytes_to_bits_length data :
  length (bytes_to_bits data) = (length data * 8)%nat.
Proof.
  rewrite /bytes_to_bits.
  rewrite (length_concat_uniform _ 8%nat).
  { len. }
  apply bytes_to_bits_uniform.
Qed.

Hint Rewrite bytes_to_bits_length : len.

Lemma bytes_to_bits_lookup_Some (bytes: list u8) (i: nat) (bit: bool) :
  bytes_to_bits bytes !! i = Some bit →
  ∃ (b: u8), bytes !! (i `div` 8)%nat = Some b ∧
             byte_to_bits b !! (i `mod` 8)%nat = Some bit.
Proof.
  rewrite /bytes_to_bits => Hlookup.
  erewrite lookup_concat_uniform in Hlookup; eauto.
  apply bind_Some in Hlookup as [bits [Hlookup' Hlookup_bit]].
  fmap_Some in Hlookup' as b. exists b.
  eauto.
Qed.

Section proof.
Context `{!heapGS Σ}.

Definition own_bitmap (bb: val) (bits: list bool): iProp Σ :=
  ∃ (s: Slice.t) data,
    "%Hval" ∷ ⌜bb = (slice_val s, #())%V⌝ ∗
    "Hs" ∷ own_slice_small s byteT (DfracOwn 1) data ∗
    "%Hoverflow" ∷ ⌜Z.of_nat (length data) < 2^56⌝ ∗
    "%Hbits" ∷ ⌜bits = bytes_to_bits data⌝.

Lemma wp_newBitmap (s: Slice.t) (bits: list bool) :
  {{{ ∃ data, own_slice_small s byteT (DfracOwn 1) data ∗
              ⌜bytes_to_bits data = bits⌝ }}}
    newBitmap (slice_val s)
  {{{ v, RET v; own_bitmap v bits }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as (data) "(Hs & %)". subst.
  wp_rec.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len.
  wp_apply wp_Assume.
  rewrite bool_decide_eq_true.
  iIntros (Hoverflow).
  wp_pures.
  iApply "HΦ". iModIntro.
  rewrite /own_bitmap. iExists _, _; iFrame.
  iPureIntro.
  split; auto.
  split; auto.
  revert Hoverflow.
  change (uint.Z (word.slu (W64 1) (W64 56))) with (2^56).
  word.
Qed.

Lemma symex_wp_bitmap__Set s (bytes: list u8) (i : u64) :
  {{{ own_slice_small s byteT (DfracOwn 1) bytes ∗
        ⌜Z.of_nat (length bytes) < 2^56⌝ ∗
        ⌜uint.Z i < Z.of_nat (length bytes) * 8⌝ }}}
    bitmap__Set (s, #())%V #i
  {{{ (b: w8), RET #();
      ⌜bytes !! (uint.nat i `div` 8)%nat = Some b⌝ ∗
      own_slice_small s byteT (DfracOwn 1)
                 (<[(uint.nat i `div` 8)%nat:=
                      word.or b
                        (word.slu (W8 1) (W8 (uint.Z i `mod` 8)))]>
               bytes) }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "(Hbb & %Hoverflow & %Hbound)".
  wp_rec. wp_pures.
  wp_apply wp_slice_len. wp_pures.
  iDestruct (own_slice_small_sz with "Hbb") as %Hsz.
  rewrite bool_decide_eq_false_2.
  2: {
    rewrite word.unsigned_mul_nowrap; try word.
  }
  wp_pures.
  assert (exists b:u8, bytes !! (uint.nat i / 8)%nat = Some b) as [b Hlookup].
  { apply list_lookup_lt. apply Nat.Div0.div_lt_upper_bound. len. }
  word_cleanup.
  wp_apply (wp_SliceGet with "[$Hbb]").
  { word_cleanup.
    rewrite Z2Nat.inj_div //. word. }
  iIntros "Hbb".
  wp_pures.
  wp_apply (wp_SliceSet with "[$Hbb]").
  { iPureIntro. apply lookup_lt_is_Some.
    word_cleanup. rewrite -> Z2Nat.inj_div by word.
    apply Nat.Div0.div_lt_upper_bound. len. }
  iIntros "Hbb".
  word_cleanup.
  rewrite -> Z2Nat.inj_div by word. change (Z.to_nat 8) with 8%nat.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iSplit.
  { iPureIntro. eauto. }
  iFrame.
Qed.

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

Lemma byte_to_bits_lookup (b: u8) (i: nat) :
  byte_to_bits b !! (i `mod` 8)%nat =
    Some (Z.testbit (uint.Z b) (i `mod` 8)%nat ).
Proof.
  rewrite /byte_to_bits.
  rewrite list_lookup_fmap.
  assert (seqZ 0 8 !! (i `mod` 8)%nat = Some (i `mod` 8)).
  { apply lookup_seqZ.
    rewrite Nat2Z.inj_mod.
    split; lia. }
  rewrite !Nat2Z.inj_mod.
  rewrite H.
  reflexivity.
Qed.

Opaque Nat.div Nat.modulo.

Lemma testbit_set_bit (b: w8) (i: Z) (i': nat) :
  0 ≤ i < 8 →
  (i' < 8)%nat →
  Z.testbit (uint.Z (word.or b (word.slu (W8 1) (W8 i)))) i' =
  if decide (i = Z.of_nat i') then true else Z.testbit (uint.Z b) i'.
Proof.
  intros Hbound Hbound'.
  byte_cases b; bit_off_cases i; bit_off_cases i';
    try reflexivity.
Qed.

Lemma mod_8_bound (n: nat) :
  (n mod 8 < 8)%nat.
Proof.
  apply Nat.mod_bound_pos; lia.
Qed.

Hint Resolve mod_8_bound : core.
Hint Resolve mod_8_bound : word.

Lemma bytes_to_bits_set:
  ∀ (i : w64) (data : list w8),
  uint.Z i < length (bytes_to_bits data)
  → length data < 2 ^ 56
  → ∀ b : w8,
  data !! (uint.nat i `div` 8)%nat = Some b
  → <[uint.nat i:=true]> (bytes_to_bits data) =
      bytes_to_bits
        (<[(uint.nat i `div` 8)%nat:=word.or b
                                       (word.slu (W8 1) (W8 (uint.Z i `mod` 8)))]>
           data).
Proof.
  intros i data Hbound Hoverflow b Hget_b.
  eapply (list_eq_same_length _ _ (length data * 8)%nat); [ | | ].
  { len. }
  { len. }
  pose proof (lookup_lt_Some _ _ _ Hget_b) as Hbound'.
  intros i' bit1 bit2 Hi'_bound Hget1 Hget2.
  apply bytes_to_bits_lookup_Some in Hget2 as (b2 & Hget2 & Hb2).
  destruct (decide (uint.nat i `div` 8 = i' `div` 8)%nat).
  - (* same byte *)
    rewrite <- e in *.
    rewrite list_lookup_insert in Hget2; [ | len ].
    inv Hget2.

    destruct (decide (uint.nat i = i')); subst.
    + (* same bit *)
      rewrite list_lookup_insert in Hget1; [ | by len ].
      inv Hget1.
      replace (uint.nat i `mod` 8)%nat with (Z.to_nat (uint.Z i `mod` 8)) in *.
      2: { rewrite Z2Nat.inj_mod //; word. }
      eapply set_bit_get; eauto.
    + (* same byte but different bit *)
      rewrite list_lookup_insert_ne // in Hget1.
      apply bytes_to_bits_lookup_Some in Hget1 as [b'' [Hgetb'' Hb'']].
      assert (b = b'') by congruence; subst.
      inv Hgetb''.

      rewrite byte_to_bits_lookup in Hb2.
      rewrite byte_to_bits_lookup in Hb''.
      inv Hb2.
      rewrite testbit_set_bit; [ | word | auto ].
      rewrite decide_False //.
      intros H.
      contradiction n.
      pose proof (Nat.div_mod (uint.nat i) 8 ltac:(lia)).
      pose proof (Nat.div_mod i' 8 ltac:(lia)).
      rewrite H1 H2.
      rewrite e.
      f_equal.
      (* how did we get into this mess? *)
      rewrite Nat2Z.inj_mod in H.
      change 8%nat with (Z.to_nat 8).
      rewrite -(Z2Nat.inj_mod (uint.Z i)); [ | word .. ].
      rewrite H.
      rewrite Z2Nat.inj_mod; try word.
      change (Z.to_nat 8%nat) with 8%nat.
      change (Z.to_nat 8) with 8%nat.
      rewrite Nat2Z.id.
      auto.
  - assert (uint.nat i ≠ i') by congruence.
    rewrite list_lookup_insert_ne // in Hget1.
    rewrite list_lookup_insert_ne // in Hget2.
    apply bytes_to_bits_lookup_Some in Hget1 as [b'' [Hgetb'' Hb'']].
    congruence.
Qed.

Lemma wp_bitmap__Set v (bits: list bool) (i: u64) :
  {{{ own_bitmap v bits ∗ ⌜uint.Z i < Z.of_nat (length bits)⌝ }}}
    bitmap__Set v #i
  {{{ RET #(); own_bitmap v (<[uint.nat i := true]> bits) }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "[Hbm %Hbound]".
  iNamed "Hbm". subst.
  wp_apply (symex_wp_bitmap__Set with "[$Hs]").
  { iPureIntro. split; auto.
    move: Hbound; len. }
  iIntros (b) "[%Hget_b Hs]".
  iApply "HΦ".
  iFrame. iSplit; [ done | ].
  iSplit.
  { iPureIntro. len. }
  iPureIntro.
  apply bytes_to_bits_set; auto.
Qed.

Lemma wp_bitmap__Get v (bits: list bool) (i: u64) :
  {{{ own_bitmap v bits ∗ ⌜uint.Z i < Z.of_nat (length bits)⌝ }}}
    bitmap__Get v #i
  {{{ (bit: bool), RET #bit; own_bitmap v bits ∗ ⌜bits !! uint.nat i = Some bit⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "[Hbm %Hbound]".
  iNamed "Hbm". subst.
  autorewrite with len in Hbound.
  wp_rec.
  wp_pures.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len. wp_pures.
  rewrite bool_decide_eq_false_2.
  2: {
    rewrite word.unsigned_mul_nowrap; try word.
  }
  wp_pures.
Admitted.

Lemma wp_bitmap__Clear v (bits: list bool) (i: u64) :
  {{{ own_bitmap v bits ∗ ⌜uint.Z i < Z.of_nat (length bits)⌝ }}}
    bitmap__Clear v #i
  {{{ RET #(); own_bitmap v (<[uint.nat i := false]> bits) }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "[Hbm %Hbound]".
  iNamed "Hbm". subst.
  autorewrite with len in Hbound.
  wp_rec.
  wp_pures.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len. wp_pures.
  rewrite bool_decide_eq_false_2.
  2: {
    rewrite word.unsigned_mul_nowrap; try word.
  }
  wp_pures.
Admitted.

End proof.

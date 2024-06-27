From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import bytes.

From Goose.github_com Require Import tchajed.simplefs.

#[local] Unset Printing Projections.

Definition BlkBits: Z := (4096*8).

Section proof.
Context `{!heapGS Σ}.

Definition is_block_typed (s: Slice.t) (dq: dfrac) (block: Block) :=
  own_slice_small s byteT dq (vec_to_list block).

Lemma is_block_to_typed s dq block :
  is_block s dq block = is_block_typed s dq block.
Proof. reflexivity. Qed.

Definition block_has_bits (block: Block) (bits: list bool) :=
  Z.of_nat (length bits) = BlkBits ∧
  ∀ (i: nat) (bit: bool),
  bits !! i = Some bit →
  ∃ (b: u8), vec_to_list block !! (i `div` 8)%nat = Some b ∧
             Z.testbit (uint.Z b) (i `mod` 8)%nat = bit.

Definition block_to_bits (block: Block): list bool :=
  concat (byte_to_bits <$> vec_to_list block).

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
      admit. (* nonlinear arith goal (mod and minus) *)
Admitted.

Hint Unfold BlkBits : word.
Hint Unfold block_bytes : word.

Lemma byte_to_bits_uniform block :
  length_uniform (byte_to_bits <$> block) 8%nat.
Proof.
  intros i x H.
  fmap_Some in H as b.
  len.
Qed.

Hint Resolve byte_to_bits_uniform : core.

Lemma block_to_bits_length block :
  length (block_to_bits block) = Z.to_nat BlkBits.
Proof.
  rewrite /block_to_bits.
  rewrite (length_concat_uniform _ 8%nat).
  { len. }
  apply byte_to_bits_uniform.
Qed.

Hint Rewrite block_to_bits_length : len.

Lemma byte_to_bits_lookup_Some (bytes: list u8) (i: nat) (bit: bool) :
  concat (byte_to_bits <$> bytes) !! i = Some bit →
  ∃ (b: u8), bytes !! (i `div` 8)%nat = Some b ∧
             byte_to_bits b !! (i `mod` 8)%nat = Some bit.
Proof.
  intros Hlookup.
  erewrite lookup_concat_uniform in Hlookup; eauto.
  apply bind_Some in Hlookup as [bits [Hlookup' Hlookup_bit]].
  fmap_Some in Hlookup' as b. exists b.
  eauto.
Qed.

Lemma block_has_to_bits block:
  block_has_bits block (block_to_bits block).
Proof.
  split.
  + len.
  + intros ?? Hlookup.
    destruct (list_lookup_lt _ block (i `div` 8)) as [b Hlookup2].
    { apply lookup_lt_Some in Hlookup.
      autorewrite with len in Hlookup.
      apply Nat.Div0.div_lt_upper_bound.
      move: Hlookup; len. }
    exists b; split; [ by auto | ].
    apply byte_to_bits_lookup_Some in Hlookup as [b' [Hlookup' Hlookup_bit]].
    assert (b = b') by congruence; subst.
    rewrite /byte_to_bits in Hlookup_bit.
    fmap_Some in Hlookup_bit.
    apply lookup_seqZ in Hlookup_bit; intuition subst.
    f_equal; lia.
Qed.

Lemma block_to_bits_ok block :
  ∀ bits, block_has_bits block bits ↔ bits = block_to_bits block.
Proof.
  intros. split.
  - intros H.
    destruct H as [Hlen Hbits].
    eapply list_eq_same_length; auto.
    { len. }
    len. intros ??? Hi Hlookup1 Hlookup2.
    apply Hbits in Hlookup1 as [b [Hlookup1 Htestbit]].
    rewrite /block_to_bits in Hlookup2.
    (* this proof is harder than it's worth *)
    admit.
  - intros ->.
    apply block_has_to_bits.
Abort.

Definition own_bitmap (bb: val) (block: Block) (bits: list bool): iProp Σ :=
  ∃ (s: Slice.t), ⌜bb = (slice_val s, #())%V⌝ ∗
                   ⌜Z.of_nat (length bits) = BlkBits⌝ ∗
                   is_block s (DfracOwn 1) block ∗
                   ⌜bits = block_to_bits block⌝.

Lemma wp_newBitmap s block :
  {{{ is_block s (DfracOwn 1) block }}}
    newBitmap (slice_val s)
  {{{ v bits, RET v; own_bitmap v block bits }}}.
Proof.
  (*@ func newBlockBitmap(block disk.Block) bitmap {                     @*)
  (*@     return bitmap{block: block}                                    @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ".
  wp_rec.
  wp_pures.
  iApply ("HΦ" $! _ (block_to_bits block)).
  iModIntro.
  iFrame.
  iPureIntro.
  split; [ by eauto | ].
  split.
  - len.
  - (* apply block_has_to_bits. *) auto.
Qed.

Lemma symex_wp_bitmap__Set s (bytes: list u8) (i : u64) :
  {{{ own_slice_small s byteT (DfracOwn 1) bytes ∗ ⌜length bytes = 4096%nat⌝ ∗ ⌜uint.Z i < BlkBits⌝ }}}
    bitmap__Set (s, #())%V #i
  {{{ (b: w8), RET #();
      ⌜bytes !! (uint.nat i `div` 8)%nat = Some b⌝ ∗
      own_slice_small s byteT (DfracOwn 1)
                 (<[(uint.nat i `div` 8)%nat:=word.or b
                                                    (word.slu
                                                       (W8 1)
                                                       (W8 (uint.Z i `mod` 8)))]>
               bytes) }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "(Hbb & %Hbytelen & %Hbound)".
  wp_rec. wp_pures.
  wp_apply wp_slice_len. wp_pures.
  iDestruct (own_slice_small_sz with "Hbb") as %Hsz.
  assert (uint.Z (Slice.sz s) = 4096).
  { word. }
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

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma own_slice_small_to_block s dq (l: list u8) :
  length l = Z.to_nat 4096 →
  own_slice_small s byteT dq l = is_block s dq (list_to_block l).
Proof.
  intros Hlen.
  rewrite is_block_to_typed /is_block_typed.
  rewrite list_to_block_to_list //.
Qed.

Lemma Some_inv {A} (a b: A) : Some a = Some b → a = b.
Proof. inversion 1; auto. Qed.

Lemma Some_eq_iff {A} (a b: A) : Some a = Some b ↔ a = b.
Proof. split; [ apply Some_inv | congruence ]. Qed.

Transparent w8_instance.w8.
Lemma set_bit_get (b: w8) (i: u64) bit :
  byte_to_bits (word.or b (word.slu (W8 1) (W8 (uint.Z i `mod` 8))))
  !! Z.to_nat (uint.Z i `mod` 8) = Some bit → true = bit.
Proof.
    byte_cases b; bit_off_cases (uint.Z i `mod` 8); compute;
      intros H%Some_inv; exact H.
Qed.

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

Lemma set_get_bit_ne (i : w64) (b : w8) (i' : nat) (bit1 bit2 : bool) :
  (Z.to_nat (uint.Z i `mod` 8) ≠ i' `mod` 8)%nat →
  byte_to_bits (word.or b (word.slu (W8 1) (W8 (uint.Z i `mod` 8))))
    !! (i' `mod` 8)%nat = Some bit2
  → byte_to_bits b !! (i' `mod` 8)%nat = Some bit1 → bit1 = bit2.
Proof.
  clear Σ heapGS0.
  intros Hmodneq.
  rewrite byte_to_bits_lookup.
  rewrite byte_to_bits_lookup.
  rewrite !Some_eq_iff. intros <- <-.

  move: Hmodneq.
  assert (i' `mod` 8 < 8)%nat as Hbound.
  { pose proof (Nat.mod_bound_pos i' 8%nat). lia. }
  bit_off_cases (i' `mod` 8)%nat;
    bit_off_cases (uint.Z i `mod` 8);
    try (intros H; compute in H; exfalso; congruence);
    byte_cases b;
    compute;
    auto.
Qed.

Opaque w8_instance.w8.

Lemma byte_bit_update (data : list u8) (i : w64) (b : w8) :
  data !! (uint.nat i `div` 8)%nat = Some b
  → <[uint.nat i:=true]> (concat (byte_to_bits <$> data)) =
      concat
        (byte_to_bits <$>
          <[(uint.nat i `div` 8)%nat
            :=word.or b
                (word.slu (W8 1) (W8 (uint.Z i `mod` 8)))]>
            data).
Proof.
  intros Hbyte_lookup.
  eapply (list_eq_same_length _ _ (length data * 8)%nat); [ | | ].
  { erewrite -> !length_concat_uniform by eauto.
    len. }
  { autorewrite with len.
    erewrite -> !length_concat_uniform by eauto.
    len. }
  intros i' bit1 bit2 Hbound Hlookup1 Hlookup2.
  apply byte_to_bits_lookup_Some in Hlookup2 as [b' [Hlookupb' Hb']].

  destruct (decide (uint.nat i `div` 8 = i' `div` 8)%nat).
  - (* same byte *)
    rewrite -e in Hlookupb'.
    rewrite list_lookup_insert in Hlookupb'.
    2: {
      apply lookup_lt_Some in Hbyte_lookup.
      word.
    }

    destruct (decide (uint.nat i = i')); subst.
    + (* same bit *)
      rewrite list_lookup_insert in Hlookup1.
      2: {
        erewrite length_concat_uniform; [ | eauto ]. len.
      }
      inversion Hlookup1; subst.
      inversion Hlookupb'; subst; clear Hlookupb'.
      move: Hb'.
      replace (uint.nat i `mod` 8)%nat with (Z.to_nat (uint.Z i `mod` 8)).
      2: {
        rewrite Z2Nat.inj_mod //; word.
      }
      apply set_bit_get.
    + (* same byte but different bit *)
      rewrite list_lookup_insert_ne // in Hlookup1.
      apply byte_to_bits_lookup_Some in Hlookup1 as [b'' [Hlookupb'' Hb'']].
      assert (b = b'') by congruence; subst.
      inversion Hlookupb'; subst; clear Hlookupb'.

      eapply set_get_bit_ne; eauto.
      rewrite Z2Nat.inj_mod //; try word.
      change (Z.to_nat 8) with 8%nat.
      intros Heq.
      contradiction n.
      admit.

  - assert (uint.nat i ≠ i') by congruence.
    rewrite list_lookup_insert_ne // in Hlookup1.
    rewrite list_lookup_insert_ne // in Hlookupb'.
    apply byte_to_bits_lookup_Some in Hlookup1 as [b'' [Hlookupb'' Hb'']].
    congruence.

Admitted.

Lemma wp_bitmap__Set v block bits (i : u64) :
  {{{ own_bitmap v block bits ∗ ⌜uint.Z i < BlkBits⌝ }}}
    bitmap__Set v #i
  {{{ block', RET #(); own_bitmap v block' (<[uint.nat i := true]> bits) }}}.
Proof.
  (*@ func (b bitmap) Set(i uint64) {                                    @*)
  (*@     if i >= BLK_BITS {                                                  @*)
  (*@         panic("out of bounds")                                          @*)
  (*@     }                                                                   @*)
  (*@     byteIndex := i / 8                                                  @*)
  (*@     bitIndex := i % 8                                                   @*)
  (*@     b.block[byteIndex] |= 1 << bitIndex                                 @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "[Hbb %Hbound]".
  iDestruct "Hbb" as (s) "(-> & %Hlen & Hblock & %Hbits)".
  wp_apply (symex_wp_bitmap__Set with "[$Hblock]").
  { iPureIntro. len. }
  iIntros (b) "[%Hbyte_lookup Hbb]".
  rewrite own_slice_small_to_block; [ | len ].
  iApply "HΦ".
  iFrame "Hbb".

  iPureIntro.
  split; [ done | ].
  split; [ by len | ].

  rewrite /block_to_bits.
  rewrite list_to_block_to_list; [ | len ].
  rewrite -byte_bit_update //.
  subst. auto.
Qed.

End proof.

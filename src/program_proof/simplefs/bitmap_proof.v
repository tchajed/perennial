From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NatDivMod bytes.
Import Nat.

From Goose.github_com Require Import tchajed.simplefs.bitmap.

From Perennial.program_proof.simplefs Require Import bitmap_byte.

Set Default Proof Using "Type".

#[local] Unset Printing Projections.
#[local] Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

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

Lemma is_block_to_typed s dq (b: Block) :
  slice.own_slice_small s byteT dq (Block_to_vals b) =
  own_slice_small s byteT dq (vec_to_list b).
Proof. reflexivity. Qed.

Definition own_bitmap (bb: val) (bits: list bool): iProp Σ :=
  ∃ (s: Slice.t) data,
    "%Hval_eq" ∷ ⌜bb = (slice_val s, #())%V⌝ ∗
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

Lemma symex_wp_Bitmap__Set s (bytes: list u8) (i : u64) :
  {{{ own_slice_small s byteT (DfracOwn 1) bytes ∗
        ⌜Z.of_nat (length bytes) < 2^56⌝ ∗
        ⌜uint.Z i < Z.of_nat (length bytes) * 8⌝ }}}
    Bitmap__Set (s, #())%V #i
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
    word. }
  iIntros "Hbb".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iSplit.
  { eauto. }
  iExactEq "Hbb". f_equal.
  f_equal; word.
Qed.

Lemma byte_to_bits_lookup (b: u8) (i: nat) :
  byte_to_bits b !! (i `mod` 8)%nat =
    Some (Z.testbit (uint.Z b) (i `mod` 8)%nat).
Proof.
  rewrite /byte_to_bits.
  rewrite list_lookup_fmap.
  assert (seqZ 0 8 !! (i `mod` 8)%nat = Some (i `mod` 8)).
  { apply lookup_seqZ.
    lia. }
  rewrite H.
  rewrite !Nat2Z.inj_mod.
  reflexivity.
Qed.

Lemma mod_8_bound (n: nat) :
  (n mod 8 < 8)%nat.
Proof. lia. Qed.

Hint Resolve mod_8_bound : core.

Opaque Nat.div Nat.modulo.

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
      replace (uint.nat i `mod` 8)%nat with (Z.to_nat (uint.Z i `mod` 8)) in * by word.
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
      word.
  - assert (uint.nat i ≠ i') by congruence.
    rewrite list_lookup_insert_ne // in Hget1.
    rewrite list_lookup_insert_ne // in Hget2.
    apply bytes_to_bits_lookup_Some in Hget1 as [b'' [Hgetb'' Hb'']].
    congruence.
Qed.

Lemma wp_Bitmap__Set v (bits: list bool) (i: u64) :
  {{{ own_bitmap v bits ∗ ⌜uint.Z i < Z.of_nat (length bits)⌝ }}}
    Bitmap__Set v #i
  {{{ RET #(); own_bitmap v (<[uint.nat i := true]> bits) }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "[Hbm %Hbound]".
  iNamed "Hbm". subst.
  wp_apply (symex_wp_Bitmap__Set with "[$Hs]").
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

Lemma wp_Bitmap__Get v (bits: list bool) (i: u64) :
  {{{ own_bitmap v bits ∗ ⌜uint.Z i < Z.of_nat (length bits)⌝ }}}
    Bitmap__Get v #i
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

Lemma wp_Bitmap__Clear v (bits: list bool) (i: u64) :
  {{{ own_bitmap v bits ∗ ⌜uint.Z i < Z.of_nat (length bits)⌝ }}}
    Bitmap__Clear v #i
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

Definition blocks_to_bits (bs: list Block): list bool :=
  concat ((λ b, bytes_to_bits (vec_to_list b)) <$> bs).

Lemma concat_bytes_to_bits (bs : list Block) :
  bytes_to_bits (concat ((λ (b:Block), vec_to_list b) <$> bs)) =
  blocks_to_bits bs.
Proof.
  rewrite /blocks_to_bits.
  induction bs as [|b bs].
  - reflexivity.
  - rewrite /bytes_to_bits.
    rewrite !fmap_cons !concat_cons !fmap_app !concat_app.
    f_equal.
    rewrite -IHbs //.
Qed.

Theorem wp_NewBitmapFromBlocks (b_s : Slice.t) (off numBlocks: w64)
                               (bs: list Block) (bits: list bool) :
  {{{ "Hd" ∷ uint.Z off d↦∗ bs ∗
      "%Hbs_len" ∷ ⌜length bs = uint.nat numBlocks⌝ ∗
      "%Hno_overflow" ∷ ⌜uint.Z off + uint.Z numBlocks < 2^64⌝ }}}
    NewBitmapFromBlocks #() #off #numBlocks
  {{{ v, RET v; uint.Z off d↦∗ bs ∗
                  own_bitmap v (blocks_to_bits bs) }}}.
Proof.
  (*@ func NewBitmapFromBlocks(d disk.Disk, off uint64, numBlocks uint64) Bitmap { @*)
  (*@     var bitmapData = make([]byte, 0, numBlocks*disk.BlockSize)          @*)
  (*@     for i := uint64(0); i < numBlocks; i++ {                            @*)
  (*@         bitmapData = append(bitmapData, d.Read(off+i)...)               @*)
  (*@     }                                                                   @*)
  (*@     return newBitmap(bitmapData)                                        @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iNamed "Hpre".
  wp_rec. wp_pures.
  wp_apply wp_NewSliceWithCap.
  { word. }
  iIntros (ptr) "Hs".
  wp_apply wp_ref_to; first by auto.
  match goal with
  | |- context[Slice.mk ?ptr ?len ?cap] => generalize dependent (Slice.mk ptr len cap); intros s
  end.
  iIntros (data_l) "data".
  wp_pures.
  wp_apply wp_ref_to; first by auto. iIntros (i_l) "i".
  wp_pures.
  rewrite replicate_0.
  wp_apply (wp_forUpto
    (λ i, ∃ (s: Slice.t),
        "data" ∷ data_l ↦[slice.T byteT] s ∗
        "Hd" ∷ uint.Z off d↦∗ bs ∗
        "Hs" ∷ own_slice s byteT (DfracOwn 1)
          (concat ((λ b, vec_to_list b) <$> take (uint.nat i) bs))
    )%I with "[] [$i $Hd data Hs]").
  { word. }
  - iIntros (i).
    clear Φ.
    iIntros (Φ) "!> Hpre HΦ". iDestruct "Hpre" as "(I & i & %Hbound)".
    iNamed "I".
    wp_pures.
    wp_load.
    assert (∃ b, bs !! uint.nat i = Some b) as [bi Hget_bi].
    { apply list_lookup_lt. len. }
    iDestruct (disk_array_acc_read _ _ (uint.Z i) with "Hd") as "[Hi Hd']".
    { word. }
    { eauto. }
    wp_apply (wp_Read with "[Hi]").
    { iExactEq "Hi". f_equal. word. }
    iIntros (s') "[Hi [Hblock _]]".
    rewrite is_block_to_typed.
    wp_load.
    wp_apply (wp_SliceAppendSlice (V:=w8) with "[$Hs $Hblock]"); auto.
    iIntros (s'') "[Hs _Hblock]".
    wp_store.
    iModIntro. iApply "HΦ".
    iFrame.
    iDestruct ("Hd'" with "[Hi]") as "$".
    { iExactEq "Hi". f_equal. word. }
    iExactEq "Hs". rewrite /named. f_equal.
    word_cleanup.
    replace (Z.to_nat (uint.Z i + 1)) with (S (uint.nat i)) by word.
    erewrite take_S_r; eauto.
    rewrite fmap_app concat_app /=.
    rewrite app_nil_r //.
  - iFrame.
  - iIntros "[I _]". iNamed "I".
    rewrite -> firstn_all2 by word.
    wp_pures.
    wp_load.
    wp_apply (wp_newBitmap with "[Hs]").
    { rewrite own_slice_to_small.
      iFrame.
      eauto. }
    iIntros (v) "Hbm".
    iApply "HΦ".
    iFrame "Hd".
    iExactEq "Hbm".
    f_equal.
    rewrite concat_bytes_to_bits //.
Qed.

Definition blkBits: Z := 4096*8.

Theorem wp_Bitmap__Write v (off : u64) (bs0: list Block) bits :
  {{{ own_bitmap v bits ∗
      uint.Z off d↦∗ bs0 ∗
      ⌜(blkBits * (Z.of_nat $ length bs0))%Z = Z.of_nat $ length bits⌝}}}
    Bitmap__Write v #() #off
  {{{ bs', RET #(); uint.Z off d↦∗ bs' ∗
                    ⌜bits = blocks_to_bits bs'⌝ }}}.
Proof.
  (*@ func (b Bitmap) Write(d disk.Disk, off uint64) {                        @*)
  (*@     // assumes len(b.Data) is a multiple of block size                  @*)
  (*@     numBlocks := uint64(len(b.Data)) / disk.BlockSize                   @*)
  (*@     for i := uint64(0); i < numBlocks; i++ {                            @*)
  (*@         d.Write(off+i, b.Data[i*disk.BlockSize:(i+1)*disk.BlockSize])   @*)
  (*@     }                                                                   @*)
  (*@ }                                                                       @*)

  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "(Hb & Hd & %Hlen)".
  iNamed "Hb". subst.
  wp_rec. wp_pures.
  wp_apply wp_slice_len. wp_pures.
  wp_apply wp_ref_to; [ auto | ].
  iIntros (i_l) "i". wp_pures.
  wp_apply wp_forUpto.
  (* TODO: write down loop invariant *)
Admitted.

End proof.

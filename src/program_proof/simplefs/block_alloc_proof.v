From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.

From Goose.github_com Require Import tchajed.simplefs.alloc.

From Perennial.goose_lang.lib Require Import typed_slice.

From Perennial.program_proof.simplefs Require Import
  superblock_proof
  bitmap_proof.

From Perennial Require Import options.

Section proof.
Context `{!heapGS Σ}.
Context `{!superblockG Σ}.

Definition free_block γsb_var (a: w32): iProp _ :=
  ∃ sb,
  "#Hsb" ∷ is_sb γsb_var sb ∗
  "%Hbound" ∷ ⌜0 < uint.Z a < uint.Z sb.(data_blocks)⌝ ∗
  "Hdisk_ptsto" ∷ ∃ b, (uint.Z a + sb_data_start sb) d↦ b.

Lemma free_block_nonzero γ a :
  free_block γ a -∗ ⌜uint.Z a ≠ 0⌝.
Proof.
  iNamed 1.
  iPureIntro. word.
Qed.

Lemma free_block_conflict γ a :
  free_block γ a -∗ free_block γ a -∗ ⌜False⌝.
Proof.
  iIntros "H1 H2".
  iDestruct "H1" as (sb) "(#Hsb1 & _ & (%b1 & H1))".
  iDestruct "H2" as (sb') "(#Hsb2 & _ & (%b2 & H2))".
  rewrite /named.
  iDestruct (is_sb_agree with "Hsb1 Hsb2") as %<-.
  iDestruct (gen_heap.pointsto_ne with "H1 H2") as %Hne.
  congruence.
Qed.

Definition own_block_alloc γsb_var (l: loc): iProp _ :=
  ∃ (offset: w64) (bm_v: val) (free_s: Slice.t),
  "#offset" ∷ l ↦[BlockAllocator :: "offset"]□ #offset ∗
  "bitmap" ∷ l ↦[BlockAllocator :: "bitmap"] bm_v ∗
  "free" ∷ l ↦[BlockAllocator :: "free"] free_s ∗
  "#d" ∷ l ↦[BlockAllocator :: "d"]□ (ExtV tt) ∗
  ∃ (bits: list bool) (bit_data: list Block) (sb: superblockT) (free: list w32),
  "Hbitmap" ∷ own_bitmap bm_v bits ∗
  "%Hbits_len" ∷ ⌜Z.of_nat (length bits) = (uint.Z sb.(data_bitmap_blocks) * 32768)%Z⌝ ∗
  "#Hsb" ∷ is_sb γsb_var sb ∗
  "%Hoffset" ∷ ⌜uint.Z offset = sb_data_bitmap_start sb⌝ ∗
  (* this invariant will require that the on-disk bitmap reflects the
  in-memory one *)
  "Hdisk_bs" ∷ uint.Z offset d↦∗ bit_data ∗
  "%Hbit_data_len" ∷ ⌜blocks_to_bits bit_data = bits⌝ ∗
  "Hfree_list" ∷ own_slice free_s uint32T (DfracOwn 1) free ∗
  "Hfree_bs" ∷ [∗ list] a ∈ free,
    ⌜bits !! uint.nat a = Some false⌝ ∗
    free_block γsb_var a
  .

(* note we're only proving this theorem starting from a zero'd bitmap
region; a more complicated spec is needed to describe a correctly encoded
on-disk bitmap that we then load *)
Theorem wp_NewBlockAllocator γsb_var (sb_l : loc) sb :
  {{{ is_superblock γsb_var sb_l sb ∗
        (* zero'd bitmap *)
      sb_data_bitmap_start sb d↦∗ (replicate (uint.nat sb.(data_bitmap_blocks)) block0) ∗
        (* arbitrary data blocks *)
      (∃ data, sb_data_start sb d↦∗ data ∗ ⌜length data = uint.nat sb.(data_blocks)⌝)
  }}}
    NewBlockAllocator (ExtV tt) #sb_l
  {{{ (l : loc), RET #l; own_block_alloc γsb_var l }}}.
Proof.
  (*@ func NewBlockAllocator(d disk.Disk, sb *superblock.Superblock) *BlockAllocator { @*)
  (*@     offset := sb.DataBitmapStart()                                      @*)
  (*@     bm := bitmap.NewBitmapFromBlocks(d, sb.DataBitmapStart(), sb.DataBitmapBlocks) @*)
  (*@     var free = []uint32{}                                               @*)
  (*@     // skip 0 intentionally                                             @*)
  (*@     for i := uint32(1); i < uint32(sb.DataBlocks); i++ {                @*)
  (*@         if !bm.Get(uint64(i)) {                                         @*)
  (*@             free = append(free, i)                                      @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@     return &BlockAllocator{                                             @*)
  (*@         offset: offset,                                                 @*)
  (*@         bitmap: bm,                                                     @*)
  (*@         free:   free,                                                   @*)
  (*@         d:      d,                                                      @*)
  (*@     }                                                                   @*)
  (*@ }                                                                       @*)

  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "(#Hsb & Hbitmap & Hdata)".
  iNamed "Hsb".
  iDestruct (is_sb_to_wf with "Hsb") as %Hwf.
  wp_call. wp_apply (wp_Superblock__DataBitmapStart with "[$Hsb_mem]").
  iIntros (bm_start Hbm_start_val).
  wp_apply (wp_Superblock__DataBitmapBlocks with "[$Hsb_mem]").
  wp_apply (wp_NewBitmapFromBlocks with "[Hbitmap]").
  { rewrite Hbm_start_val. iFrame "Hbitmap".
    iPureIntro.
    split.
    - len.
    - destruct Hwf; word.
  }
  iIntros (bm_v) "(Hdisk & Hbm)".
  wp_apply wp_NewSlice_0; iIntros (free_s) "Hfree".
  wp_apply (wp_ref_to); [ val_ty | iIntros (free_l) "free" ].
  wp_pures.
  wp_apply (wp_Superblock__DataBlocks with "[$Hsb_mem]").
  wp_apply (wp_ref_to); [ val_ty | iIntros (i_l) "i" ].
  wp_pures.
  wp_apply (wp_forUpto' (λ i, ∃ (free_s: Slice.t) (free: list w32),
                "free" ∷ free_l ↦[slice.T uint32T] free_s ∗
                "Hfree" ∷ own_slice free_s uint32T (DfracOwn 1) free ∗
                "%free_eq" ∷ ⌜free = W32 <$> seqZ 1 (uint.Z i - 1)⌝ ∗
                "Hbm" ∷ own_bitmap bm_v
                          (blocks_to_bits (replicate (uint.nat sb.(data_bitmap_blocks)) block0))
              )%I with
           "[$i free Hfree Hbm]").
  - iSplit.
    + admit. (* TODO: superblock should guarantee sb.(data_blocks) > 0 *)
    + iExists _, _. iFrame "free Hfree Hbm". (* TODO: [iFrame] without names is much slower *)
      iPureIntro.
      change (uint.Z (W64 1) - 1) with 0.
      reflexivity.
  - clear Φ. iIntros "!>" (i Φ) "(HI & (i & %Hi_bound)) HΦ".
    iNamed "HI". subst.
    wp_pures.
    wp_load.
    wp_apply (wp_Bitmap__Get with "[$Hbm]").
    { rewrite length_blocks_to_bits. len.
      iPureIntro.
      destruct Hwf.
      rewrite /allocatable_data_blocks in wf_data_blocks_allocatable.
      change (BlkSize * 8) with (32768) in wf_data_blocks_allocatable.
      word. }
    iIntros (bit) "(Hbm & %Hbit_get)".
    (* TODO: prove bit is always false because we start with an all-zero bitmap *)
    assert (bit = false) by admit; subst.
    wp_pures.
    wp_load.
    wp_load.
    wp_apply (wp_SliceAppend with "[$Hfree]").
    iIntros (free_s') "Hs".
    wp_store.
    iModIntro.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    word_cleanup.
    replace (uint.Z i + 1 - 1) with (uint.Z i) by word.
    change [W32 (uint.Z i)] with (W32 <$> [uint.Z i]).
    rewrite -fmap_app.
    admit. (* some seqZ stuff *)
  - iIntros "(I & i)". iNamed "I". iDestruct "free" as "free_local".
    wp_load.
    iDestruct (own_bitmap_val_ty with "Hbm") as %Hbm_ty.
    iApply wp_fupd.
    wp_apply (wp_allocStruct); [ val_ty | ].
    iIntros (l) "Hba".
    iApply struct_fields_split in "Hba". iNamed "Hba".
    iMod (struct_field_pointsto_persist with "offset") as "offset".
    iMod (struct_field_pointsto_persist with "d") as "d".
    iModIntro.
    iApply "HΦ".
    iExists _, _, _; iFrame "offset bitmap free d".
    iExists _, _, _, _; iFrame "Hbm Hdisk Hfree Hsb".
    repeat iSplit; auto; try iPureIntro.
    + rewrite length_blocks_to_bits; len.
    + rewrite /named. subst free.
      rewrite /free_block.
      (* TODO: need to align each element of free (which are just the numbers
      1..data_blocks) with the disk points-to facts in Hdata, and prove that
      these bits are false using the earlier lemma that says all the bits are
      false *)
Admitted.

Theorem wp_BlockAllocator__Alloc γ (ba : loc) :
  {{{ own_block_alloc γ ba }}}
    BlockAllocator__Alloc #ba
  {{{ (a : u32) (ok : bool), RET (#a, #ok);
      own_block_alloc γ ba ∗
      (⌜ok = true⌝ -∗ free_block γ a)
  }}}.
Proof.
  (*@ func (ba *BlockAllocator) Alloc() (uint32, bool) {                      @*)
  (*@     if len(ba.free) == 0 {                                              @*)
  (*@         return 0, false                                                 @*)
  (*@     }                                                                   @*)
  (*@     i := ba.free[len(ba.free)-1]                                        @*)
  (*@     ba.free = ba.free[:len(ba.free)-1]                                  @*)
  (*@     ba.bitmap.Set(uint64(i))                                            @*)
  (*@     ba.bitmap.Write(ba.d, ba.offset)                                    @*)
  (*@     return i, true                                                      @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "Hba".
  wp_call.
  iNamed "Hba".
  wp_loadField.
  wp_apply wp_slice_len. wp_pures.
  wp_if_destruct; wp_pures.
  { iModIntro. iApply "HΦ".
    iFrame "∗#".
    iIntros "%"; congruence. }
  iNamed "Hba".
  iDestruct (own_slice_sz with "Hfree_list") as %Hfree_sz.
  wp_loadField. wp_apply wp_slice_len. wp_loadField.
  assert (uint.Z free_s.(Slice.sz) ≠ 0).
  { change 0 with (uint.Z (W64 0)).
    intros H%(inj uint.Z).
    congruence. }
  list_elem free (length free - 1)%nat as last_free.
  iDestruct (own_slice_split with "Hfree_list") as "[Hfree_list Hcap]".
  wp_apply (wp_SliceGet with "[$Hfree_list]").
  { iPureIntro.
    word_cleanup.
    replace (Z.to_nat (uint.Z free_s.(Slice.sz) - 1)) with (length free - 1)%nat by word.
    eauto.
  }
  iIntros "Hfree_list".
  repeat (wp_loadField || wp_apply wp_slice_len).
  iDestruct (own_slice_cap_wf with "Hcap") as %Hcap.
  wp_apply wp_SliceTake.
  { word. }
  wp_storeField.
  wp_loadField.
  (* need to split off last element of Hfree_bs to get that anything in free is
  in bounds in [bits] (with the value false), and also to get the [free_block]
  ownership *)
  wp_apply (wp_Bitmap__Set with "[$Hbitmap]").
  { iPureIntro. word_cleanup.
Admitted.

Theorem wp_BlockAllocator__Free γ (ba : loc) (a : u32) :
  {{{ own_block_alloc γ ba ∗
      free_block γ a
  }}}
    BlockAllocator__Free #ba #a
  {{{ RET #(); own_block_alloc γ ba }}}.
Proof.
  (*@ func (ba *BlockAllocator) Free(i uint32) {                              @*)
  (*@     if !ba.bitmap.Get(uint64(i)) {                                      @*)
  (*@         panic("freeing free block")                                     @*)
  (*@     }                                                                   @*)
  (*@     ba.bitmap.Clear(uint64(i))                                          @*)
  (*@     ba.bitmap.Write(ba.d, ba.offset)                                    @*)
  (*@     ba.free = append(ba.free, i)                                        @*)
  (*@ }                                                                       @*)
Admitted.

End proof.

#[global] Typeclasses Opaque own_block_alloc.
#[global] Opaque own_block_alloc.

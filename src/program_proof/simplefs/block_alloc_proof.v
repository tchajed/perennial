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
  "offset" ∷ l ↦[BlockAllocator :: "offset"] #offset ∗
  "bitmap" ∷ l ↦[BlockAllocator :: "bitmap"] bm_v ∗
  "free" ∷ l ↦[BlockAllocator :: "free"] free_s ∗
  "d" ∷ l ↦[BlockAllocator :: "d"] #() ∗
  ∃ (bits: list bool) (bit_data: list Block) (sb: superblockT) (free: list w32),
  "Hbitmap" ∷ own_bitmap bm_v bits ∗
  "%Hbit_len" ∷ ⌜length bits = uint.nat sb.(data_bitmap_blocks)⌝ ∗
  "#Hoffset" ∷ is_sb γsb_var sb ∗
               ⌜uint.Z offset = sb_data_bitmap_start sb⌝ ∗
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
    NewBlockAllocator #() #sb_l
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

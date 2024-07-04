From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.

From Goose.github_com Require Import tchajed.simplefs.alloc.

From Perennial.goose_lang.lib Require Import typed_slice.

From Perennial.program_proof.simplefs Require Import
  superblock_proof
  inode_proof.

Section proof.
Context `{!heapGS Σ}.
Context `{!inodeG Σ}.

Definition free_inode γ (inum: w64): iProp _ :=
  ∃ i, inode_ptsto γ inum i.

Definition own_inode_alloc γ (l: loc): iProp _ :=
  ∃ (sb_l: loc) (free_s: Slice.t),
  "sb" ∷ l ↦[InodeAllocator :: "sb"] #sb_l ∗
  "d" ∷ l ↦[InodeAllocator :: "d"] #() ∗
  "free" ∷ l ↦[InodeAllocator :: "free"] free_s ∗
  ∃ (sb: superblockT) (free: list w64),
    "#Hsb" ∷ is_superblock γ.(sb_var) sb_l sb ∗
    "Hfree" ∷ own_slice free_s uint64T (DfracOwn 1) free ∗
    "Hfree_inodes" ∷ [∗ list] inum ∈ free, free_inode γ inum
.

Theorem wp_NewInodeAllocator γ (sb_l: loc) sb :
  {{{ is_superblock γ.(sb_var) sb_l sb ∗
      [∗ list] inum ∈ seq 0 (uint.nat sb.(inode_blocks) * 32)%nat,
        inode_ptsto γ (W64 (Z.of_nat inum)) inode_rep.zero
  }}}
    NewInodeAllocator #() #sb_l
  {{{ (l: loc), RET #l; own_inode_alloc γ l }}}.
Proof.
  (*@ func NewInodeAllocator(d disk.Disk, sb *superblock.Superblock) *InodeAllocator { @*)
  (*@     var free = []simplefs.Inum{}                                        @*)
  (*@     inode_blocks := sb.InodeBlocks                                      @*)
  (*@     offset := sb.InodeStart()                                           @*)
  (*@     for blk_num := uint64(0); blk_num < inode_blocks; blk_num++ {       @*)
  (*@         blk := d.Read(offset + blk_num)                                 @*)
  (*@         for i := uint64(0); i < simplefs.INODES_PER_BLOCK; i++ {        @*)
  (*@             ino := inode.FromBytes(blk[i*simplefs.INODE_SIZE : (i+1)*simplefs.INODE_SIZE]) @*)
  (*@             if ino.GetType() == simplefs.Invalid {                      @*)
  (*@                 free = append(free, simplefs.Inum(blk_num*simplefs.INODES_PER_BLOCK+i)) @*)
  (*@             }                                                           @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@     return &InodeAllocator{                                             @*)
  (*@         sb: sb, d: d, free: free,                                       @*)
  (*@     }                                                                   @*)
  (*@ }                                                                       @*)
Admitted.


End proof.

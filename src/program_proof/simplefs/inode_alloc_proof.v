From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.

From Goose.github_com Require Import tchajed.simplefs.alloc.

From Perennial.goose_lang.lib Require Import typed_slice.

From Perennial.program_proof.simplefs Require Import
  superblock_proof
  inode_proof.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section proof.
Context `{!heapGS Σ}.
Context `{!inodeG Σ}.

Definition free_inode γ (inum: w64): iProp _ :=
  inode_ptsto γ inum inode_rep.zero.

(* TODO: inode allocator owns all free inodes, which means to find out if an
inode is valid or not requires both [own_inode_alloc] and [inode_ptsto] facts
for the rest of the disk. *)

(* [own_inode_alloc] exposes its free set to maintain the fact that every [inode_ptsto]
is either owned by the file system or the allocator, and none are lost *)
Definition own_inode_alloc γ (l: loc) (free: gset w64) : iProp _ :=
  ∃ (sb_l: loc) (free_s: Slice.t),
  "sb" ∷ l ↦[InodeAllocator :: "sb"] #sb_l ∗
  "d" ∷ l ↦[InodeAllocator :: "d"] #() ∗
  "free" ∷ l ↦[InodeAllocator :: "free"] free_s ∗
  ∃ (sb: superblockT) (free_list: list w64),
    ⌜list_to_set free_list = free⌝ ∗
    "#Hsb" ∷ is_superblock γ.(sb_var) sb_l sb ∗
    "Hfree" ∷ own_slice free_s uint64T (DfracOwn 1) free_list ∗
    "Hfree_inodes" ∷ [∗ list] inum ∈ free_list, free_inode γ inum
.

#[global] Instance own_inode_alloc_timeless : `(Timeless (own_inode_alloc γ l free)).
Proof. apply _. Qed.

Theorem wp_NewInodeAllocator γ (sb_l: loc) sb (inodes: gmap w64 inode_rep.t) :
  {{{ is_superblock γ.(sb_var) sb_l sb ∗
      inode_auth γ ∗
      ⌜∀ inum, sb_valid_inum sb inum → inum ∈ dom inodes⌝ ∗
      ([∗ map] inum↦ino ∈ inodes, inode_ptsto γ inum ino)
  }}}
    NewInodeAllocator #() #sb_l
  {{{ (l: loc), RET #l;
      (let free := filter (λ '(_, i), i.(inode_rep.typ) = inodeType.invalid) inodes in
      own_inode_alloc γ l (dom free)) ∗
      inode_auth γ ∗
      (* allocator owns all invalid inodes, but rest are returned to caller *)
      let valid_inodes := filter (λ '(_, i), i.(inode_rep.typ) ≠ inodeType.invalid) inodes in
      ([∗ map] inum↦ino ∈ valid_inodes, inode_ptsto γ inum ino)
  }}}.
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

Theorem wp_InodeAllocator__Alloc γ (ia : loc) free (tyI : w32) ty :
  inodeType.rep ty = tyI →
  {{{ own_inode_alloc γ ia free ∗ inode_auth γ }}}
    InodeAllocator__Alloc #ia #tyI
  {{{ (inum: w64) (ok: bool), RET (#inum, #ok);
      inode_auth γ ∗
      (⌜ok = true⌝ -∗
      ⌜inum ∈ free⌝ ∗
      own_inode_alloc γ ia (free ∖ {[inum]}) ∗
      (inode_ptsto γ inum (inode_rep.zero <| inode_rep.typ := ty |>))) ∗
      (⌜ok = false⌝ -∗
      own_inode_alloc γ ia free) }}}.
Proof.
  (*@ func (ia *InodeAllocator) Alloc(ty simplefs.InodeType) (simplefs.Inum, bool) { @*)
  (*@     // precondition                                                     @*)
  (*@     machine.Assert(ty != simplefs.Invalid)                              @*)
  (*@     if len(ia.free) == 0 {                                              @*)
  (*@         return 0, false                                                 @*)
  (*@     }                                                                   @*)
  (*@     i := ia.free[len(ia.free)-1]                                        @*)
  (*@     ia.free = ia.free[:len(ia.free)-1]                                  @*)
  (*@     ino := inode.ReadInode(ia.d, ia.sb, i)                              @*)
  (*@     ino.SetType(ty)                                                     @*)
  (*@     ino.Write(ia.d, ia.sb, i)                                           @*)
  (*@     return i, true                                                      @*)
  (*@ }                                                                       @*)
Admitted.

Theorem wp_InodeAllocator__Free γ (ia : loc) free (inum: w64) i :
  {{{ own_inode_alloc γ ia free ∗ inode_auth γ ∗
      inode_ptsto γ inum i ∗
        (* TODO: not sure when/if inode state should be reset; maybe allocator
        can return a non-deterministic value for everything *)
      ⌜i.(inode_rep.len) = W64 0 ∧
       i.(inode_rep.meta) = W32 0 ∧
       i.(inode_rep.block_ptrs) = vreplicate 28 (W32 0)⌝
  }}}
    InodeAllocator__Free #ia #inum
  {{{ RET #(); own_inode_alloc γ ia (free ∪ {[inum]}) ∗ inode_auth γ }}}.
Proof.
  (*@ func (ia *InodeAllocator) Free(i simplefs.Inum) {                       @*)
  (*@     ino := inode.ReadInode(ia.d, ia.sb, i)                              @*)
  (*@     ino.SetType(simplefs.Invalid)                                       @*)
  (*@     ino.Write(ia.d, ia.sb, i)                                           @*)
  (*@     ia.free = append(ia.free, i)                                        @*)
  (*@ }                                                                       @*)
Admitted.


End proof.

#[global] Typeclasses Opaque own_inode_alloc.
#[global] Opaque own_inode_alloc.

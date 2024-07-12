From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.

From Goose.github_com Require Import tchajed.simplefs.filesys.

From Perennial.goose_lang.lib Require Import typed_slice.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof.simplefs Require Import
  inode_proof
  block_alloc_proof
  inode_alloc_proof
  superblock_proof
.

From iris.base_logic.lib Require Import ghost_map.

#[local] Open Scope Z.
#[local] Unset Printing Projections.

Module block_file.
Record t :=
  mk {
      typ: inodeType.t;
      len: w64;
      meta: w32;
      data: vec Block 28;
    }.
End block_file.

Record blockfs_names :=
  { inode_var: inode_names;
    (* TODO: doesn't seem like this will be needed *)
    files_var: gname;
  }.

Definition sb_var (γ: blockfs_names) :=
  γ.(inode_var).(inode_proof.sb_var).

Class blockfsG Σ :=
  { fs_inodeG :: inodeG Σ;
    inode_mapG :: ghost_mapG Σ w64 block_file.t;
  }.

Section proof.
Context `{!heapGS Σ}.
Context `{!blockfsG Σ}.

Definition blockfs_auth (γ: blockfs_names): iProp Σ :=
  ∃ (inodes: gmap w64 block_file.t),
    ghost_map_auth γ.(files_var) 1 inodes.

Definition bfile_metadata (f: block_file.t) :=
  (f.(block_file.typ), f.(block_file.len), f.(block_file.meta)).

Definition inode_metadata (ino: inode_rep.t) :=
  (ino.(inode_rep.typ), ino.(inode_rep.len), ino.(inode_rep.meta)).

Definition own_bfile γ (i: w64) (ino: inode_rep.t) (f: block_file.t): iProp Σ :=
  ∃ sb, "Hsb2" ∷ is_sb (sb_var γ) sb ∗
    (* TODO: doesn't seem like this ghost state is needed since [own_bfile] can
    own all the relevant data *)
    (* ghost_map_elem γ.(files_var) inum (DfracOwn 1) f ∗ *)
    "Hino_ptsto" ∷ inode_ptsto γ.(inode_var) i ino ∗
    "%Hmetadata" ∷ ⌜inode_metadata ino = bfile_metadata f⌝ ∗
    "Hblocks" ∷ [∗ list] a; b ∈ ino.(inode_rep.block_ptrs); f.(block_file.data),
    ⌜uint.Z a = 0 → b = block0⌝ ∗
    (⌜uint.Z a ≠ 0⌝ → (sb_data_start sb + uint.Z a) d↦ b)
.

(* unclear if this is needed or if [own_bfile] is needed more often; if [ino] is
existentially quantified (and more fundamentally if [inodes_ptsto] is fully
owned by [own_bfile]) there's no way to talk about the inode state outside of
[own_bfile], which means we can't have a [inode_mem] fact known to have the
current inode data. *)
Definition bfile_ptsto γ i f: iProp _ :=
  ∃ ino, own_bfile γ i ino f.

(* partial ownership over block fs that does not assert completeness, doesn't
own [bfile_ptsto] facts, and exposes the [free] set *)
Definition own_blockFs_internal (γ: blockfs_names) (l: loc) sb free: iProp _ :=
  ∃ (sb_l ba_l ia_l: loc),
  "#sb_l" ∷ l ↦[blockFs :: "sb"]□ #sb_l ∗
  "#d" ∷ l ↦[blockFs :: "d"]□ #() ∗
  "#ba_l" ∷ l ↦[blockFs :: "ba"]□ #ba_l ∗
  "#ia_l" ∷ l ↦[blockFs :: "ia"]□ #ia_l ∗
  (* "Hauth" ∷ blockfs_auth γ ∗ *)
  "#sb" ∷ is_superblock (sb_var γ) sb_l sb ∗
  "Hba" ∷ own_block_alloc (sb_var γ) ba_l ∗
  "Hinodes" ∷ inode_auth γ.(inode_var) ∗
  "Hia" ∷ own_inode_alloc γ.(inode_var) ia_l free.

(* Note that [own_blockFs] exposes the exact logical state of the file system.
It owns the entire disk, including all inode points-to facts, which permits
looking up inodes without explicitly having ownership. *)
Definition own_blockFs (γ: blockfs_names) (l: loc) (bfiles: gmap w64 block_file.t) : iProp _ :=
  ∃ sb free,
  "Hbfs" ∷ own_blockFs_internal γ l sb free ∗
  "%Hinum_complete" ∷
    ⌜∀ inum, sb_valid_inum sb inum → inum ∈ free ∨ inum ∈ dom bfiles⌝ ∗
  "Hfiles" ∷ [∗ map] inum↦f ∈ bfiles, bfile_ptsto γ inum f
.

Definition sb_disk_ptsto sb : iProp _ :=
    0 d↦ list_to_block (sb_encode sb).
Definition sb_zero_data_bitmap sb : iProp _ :=
    sb_data_bitmap_start sb d↦∗ (replicate (uint.nat sb.(data_bitmap_blocks)) block0).
Definition sb_data_blocks sb: iProp _ :=
    ∃ bs, ⌜length bs = uint.nat sb.(data_blocks)⌝ ∗ sb_data_start sb d↦∗ bs.

Theorem wp_zeroDisk (sz : u64) bs :
  {{{ 0 d↦ bs ∗ ⌜length bs = uint.nat sz⌝ }}}
    zeroDisk #() #sz
  {{{ γsb (l : loc) sb, RET #l;
      is_superblock γsb l sb ∗
      sb_disk_ptsto sb ∗ sb_zero_data_bitmap sb ∗ sb_data_blocks sb ∗
      sb_inode_start sb d↦∗ (replicate (uint.nat sb.(inode_blocks)) block0)
  }}}.
Proof.
  (*@ func zeroDisk(d disk.Disk, sz uint64) *superblock.Superblock {          @*)
  (*@     sb := superblock.InitSuperblock(sz)                                 @*)
  (*@     d.Write(0, sb.Encode())                                             @*)
  (*@                                                                         @*)
  (*@     zero_blk := make(disk.Block, disk.BlockSize)                        @*)
  (*@     for i := uint64(0); i < sb.InodeBlocks; i++ {                       @*)
  (*@         d.Write(sb.InodeStart()+i, zero_blk)                            @*)
  (*@     }                                                                   @*)
  (*@     for i := uint64(0); i < sb.DataBitmapBlocks; i++ {                  @*)
  (*@         d.Write(sb.DataBitmapStart()+i, zero_blk)                       @*)
  (*@     }                                                                   @*)
  (*@     // data does not have to be zeroed                                  @*)
  (*@     return sb                                                           @*)
  (*@ }                                                                       @*)
Admitted.

Definition root_ino: inode_rep.t :=
  inode_rep.mk inodeType.dirType (W64 0) (W32 493) (vreplicate _ (W32 0)).

Definition init_inodes (sb: superblockT) :=
  <[W64 1 := root_ino]> (init_inode_map (uint.nat sb.(inode_blocks) * 32)%nat).

(* the on-disk facts for an initialized file system *)
Definition init_fs γ sb: iProp _ :=
    "sb_disk" ∷ sb_disk_ptsto sb ∗
    "data_bitmaps" ∷ sb_zero_data_bitmap sb ∗
    "inodes" ∷
      ([∗ map] inum↦ino ∈ init_inodes sb,
        inode_ptsto γ.(inode_var) inum ino) ∗
    "data_blocks" ∷ sb_data_blocks sb.

Theorem wp_mkBlockFs (sz : w64) (bs: list Block) :
  {{{ 0 d↦∗ bs ∗ ⌜length bs = uint.nat sz⌝ }}}
    mkBlockFs #() #sz
  {{{ γ sb, RET #(); init_fs γ sb
  }}}.
Proof.
  (*@ func mkBlockFs(d disk.Disk, sz uint64) {                                @*)
  (*@     sb := superblock.InitSuperblock(sz)                                 @*)
  (*@     d.Write(0, sb.Encode())                                             @*)
  (*@                                                                         @*)
  (*@     zero_blk := make(disk.Block, disk.BlockSize)                        @*)
  (*@     for i := uint64(0); i < sb.InodeBlocks; i++ {                       @*)
  (*@         d.Write(sb.InodeStart()+i, zero_blk)                            @*)
  (*@     }                                                                   @*)
  (*@     for i := uint64(0); i < sb.DataBitmapBlocks; i++ {                  @*)
  (*@         d.Write(sb.DataBitmapStart()+i, zero_blk)                       @*)
  (*@     }                                                                   @*)
  (*@     // data does not have to be zeroed                                  @*)
  (*@                                                                         @*)
  (*@     root_inode := inode.NewInode(simplefs.DirType)                      @*)
  (*@     root_inode.SetMeta(inode.Meta{Mode: 0o755})                         @*)
  (*@     root_inode.Write(d, sb, simplefs.ROOT_INUM)                         @*)
  (*@ }                                                                       @*)
Admitted.

Definition root_bfile: block_file.t :=
  block_file.mk inodeType.dirType (W64 0) (W32 493) (vreplicate _ block0).

(* only specified for a newly created file system *)
Theorem wp_loadBlockFs γ sb :
  {{{ init_fs γ sb }}}
    loadBlockFs #()
  {{{ (l : loc), RET #l;
      is_sb (sb_var γ) sb ∗
      own_blockFs γ l {[ W64 1 := root_bfile ]}
  }}}.
Proof.
  (*@ func loadBlockFs(d disk.Disk) *blockFs {                                @*)
  (*@     sb := superblock.LoadSuperblock(d)                                  @*)
  (*@     ba := alloc.NewBlockAllocator(d, sb)                                @*)
  (*@     ia := alloc.NewInodeAllocator(d, sb)                                @*)
  (*@     return &blockFs{sb: sb, d: d, ba: ba, ia: ia}                       @*)
  (*@ }                                                                       @*)
Admitted.

Theorem wp_blockFs__Superblock γ (l: loc) bfiles :
  {{{ own_blockFs γ l bfiles }}}
    blockFs__Superblock #l
  {{{ (sb_l : loc) sb, RET #sb_l;
      own_blockFs γ l bfiles ∗
      is_superblock (sb_var γ) sb_l sb }}}.
Proof.
  (*@ func (fs *blockFs) Superblock() *superblock.Superblock {                @*)
  (*@     return fs.sb                                                        @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "Hfs". iNamed "Hfs". iNamed "Hbfs".
  wp_call. wp_loadField. iApply "HΦ".
  iSplitL; [ | iFrame "#" ].
  iFrame "∗#%".
Qed.


End proof.

#[global] Typeclasses Opaque own_blockFs.
#[global] Opaque own_blockFs.

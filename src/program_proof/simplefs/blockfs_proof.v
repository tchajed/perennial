From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com Require Import tchajed.simplefs.filesys.

From Perennial.program_proof Require Import disk_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.

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

Definition own_blockFs (γ: blockfs_names) (l: loc) : iProp _ :=
  ∃ (sb_l ba_l ia_l: loc),
  "sb_l" ∷ l ↦[blockFs :: "sb"]□ #sb_l ∗
  "d" ∷ l ↦[blockFs :: "d"]□ #() ∗
  "ba_l" ∷ l ↦[blockFs :: "ba"]□ #ba_l ∗
  "ia_l" ∷ l ↦[blockFs :: "ia"]□ #ia_l ∗
  "Hauth" ∷ blockfs_auth γ ∗
  ∃ (sb: superblockT),
    "#sb" ∷ is_superblock (sb_var γ) sb_l sb ∗
    "Hba" ∷ own_block_alloc (sb_var γ) ba_l ∗
    "Hia" ∷ own_inode_alloc γ.(inode_var) ia_l ∗
    "Hinodes" ∷ inode_auth γ.(inode_var)
.

End proof.

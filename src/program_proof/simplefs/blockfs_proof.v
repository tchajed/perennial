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

(* TODO: should we create gmap ghost state for each inode's state and
permissions? or just have one big gmap and a separating conjunction over it to
express disjointness? (actually, this is the minimum needed - the ghost state is
just a small layer above this) *)

Section proof.
Context `{!heapGS Σ}.
Context `{!inodeG Σ}.

Definition own_blockFs γ (l: loc) : iProp _ :=
  ∃ (sb_l ba_l ia_l: loc),
  "sb_l" ∷ l ↦[blockFs :: "sb"]□ #sb_l ∗
  "d" ∷ l ↦[blockFs :: "d"]□ #() ∗
  "ba_l" ∷ l ↦[blockFs :: "ba"]□ #ba_l ∗
  "ia_l" ∷ l ↦[blockFs :: "ia"]□ #ia_l ∗
  ∃ (sb: superblockT),
    "#sb" ∷ is_superblock γ.(sb_var) sb_l sb ∗
    "Hba" ∷ own_block_alloc γ.(sb_var) ba_l ∗
    "Hia" ∷ own_inode_alloc γ ia_l ∗
    "Hinodes" ∷ inode_auth γ
.

End proof.

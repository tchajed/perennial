From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.

From Perennial.program_proof Require Import marshal_stateless_proof.

From Goose.github_com Require Import tchajed.simplefs.superblock.

Record superblockT := {
    log_blocks: u64;
    inode_blocks: u64;
    data_bitmap_blocks: u64;
    data_blocks: u64;
}.

Definition InodeSize: Z := 128.
Definition BlkSize: Z := 4096.

Implicit Types (sb: superblockT).

Definition num_inodes sb :=
  uint.Z sb.(inode_blocks) * (BlkSize / InodeSize).

Definition allocatable_data_blocks sb: Z :=
  uint.Z sb.(data_bitmap_blocks) * (BlkSize * 8).

Record superblock_wf sb : Prop :=
  {
    wf_data_bitmap_blocks_bound: uint.Z sb.(data_bitmap_blocks) <= 0x2000;
    wf_data_blocks_allocatable: allocatable_data_blocks sb >= uint.Z sb.(data_blocks);
    wf_data_blocks_bound: uint.Z sb.(data_blocks) < 0x100000000
  }.

Section proof.
Context `{!heapGS Σ}.

(*@ type Superblock struct {                                                @*)
(*@     LogBlocks        uint64                                             @*)
(*@     InodeBlocks      uint64                                             @*)
(*@     DataBitmapBlocks uint64                                             @*)
(*@     DataBlocks       uint64                                             @*)
(*@ }                                                                       @*)
Definition is_superblock (l : loc) (sb: superblockT) : iProp Σ :=
    "logBlocks" ∷ l ↦[Superblock :: "LogBlocks"]{DfracDiscarded} #(sb.(log_blocks)) ∗
    "inodeBlocks" ∷ l ↦[Superblock :: "InodeBlocks"]{DfracDiscarded} #(sb.(inode_blocks)) ∗
    "dataBitmapBlocks" ∷ l ↦[Superblock :: "DataBitmapBlocks"]{DfracDiscarded} #(sb.(data_bitmap_blocks)) ∗
    "dataBlocks" ∷ l ↦[Superblock :: "DataBlocks"]{DfracDiscarded} #(sb.(data_blocks)) ∗
    "%Hwf" ∷ ⌜superblock_wf sb⌝.

Global Instance is_superblock_persistent l sb : Persistent (is_superblock l sb) := _.

Lemma wp_Superblock__allocatableDataBlocks (l : loc) sb :
  {{{ is_superblock l sb }}}
    Superblock__allocatableDataBlocks #l
  {{{ (x:u64), RET #x; ⌜uint.Z x = allocatable_data_blocks sb⌝ }}}.
Proof.
  (*@ func (sb *Superblock) allocatableDataBlocks() uint64 {                  @*)
  (*@     return sb.DataBitmapBlocks * (disk.BlockSize * 8)                   @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iNamed "Hpre". destruct Hwf.
  wp_rec.
  wp_loadField.
  wp_pures.
  iApply "HΦ".
  iPureIntro.
  rewrite word.unsigned_mul_nowrap //.
  change (word.mul (W64 4096) (W64 8)) with (W64 32768).
  word.
Qed.

Lemma wp_Superblock__Wf (l : loc) sb :
  {{{ is_superblock l sb }}}
    Superblock__Wf #l
  {{{ RET #true; True }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iPoseProof "Hpre" as "#Hwf".
  iPoseProof "Hwf" as "Hwf2". iNamed "Hwf2".
  pose proof Hwf as Hwf'; destruct Hwf'.
  wp_rec.
  wp_loadField. wp_pures.
  rewrite bool_decide_eq_true_2; [ wp_pures | word ].
  wp_loadField.
  wp_apply (wp_Superblock__allocatableDataBlocks with "Hwf").
  iIntros (x). iIntros (Hx_val).
  wp_pures.
  rewrite bool_decide_eq_true_2; [ | word ].
  wp_loadField.
  wp_pures.
  iModIntro.
  rewrite bool_decide_eq_true_2; [ | word ].
  iApply "HΦ"; auto.
Qed.

End proof.

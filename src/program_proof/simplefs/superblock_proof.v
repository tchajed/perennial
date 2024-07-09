From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.

From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.algebra Require Import ghost_var.

From Goose.github_com Require Import tchajed.simplefs.superblock.

#[local] Open Scope Z.
#[local] Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
#[local] Unset Printing Projections.

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
Definition sb_inode_start (sb: superblockT): Z :=
  1 + uint.Z sb.(log_blocks).
Definition sb_data_bitmap_start sb: Z :=
  1 + uint.Z sb.(log_blocks) + uint.Z sb.(inode_blocks).
Definition sb_data_start sb: Z :=
  1 + uint.Z sb.(log_blocks) + uint.Z sb.(inode_blocks) + uint.Z sb.(data_bitmap_blocks).
Definition sb_used_blocks sb: Z :=
  sb_data_start sb + uint.Z sb.(data_blocks).

#[global] Hint Unfold num_inodes allocatable_data_blocks
  sb_inode_start sb_data_bitmap_start sb_data_start sb_used_blocks : word.

Definition sb_valid_inum sb (inum: w64) :=
  uint.Z inum < uint.Z sb.(inode_blocks) * 32.
#[global] Hint Unfold sb_valid_inum : word.

Record superblock_wf sb : Prop :=
  {
    (* no overflow anywhere *)
    wf_used_blocks_bound: 1 + uint.Z sb.(log_blocks) +
                            uint.Z sb.(inode_blocks) +
                            uint.Z sb.(data_bitmap_blocks) +
                            uint.Z sb.(data_blocks) < 0x1_0000_0000;
    wf_data_blocks_allocatable: allocatable_data_blocks sb >= uint.Z sb.(data_blocks);
    wf_data_blocks_bound: uint.Z sb.(data_blocks) < 0x1_0000_0000
  }.

Class superblockG Σ :=
  {
    has_agree_sb :: ghost_varG Σ superblockT;
  }.

Section proof.
Context `{!heapGS Σ}.
Context `{!superblockG Σ}.

(* the superblock is constant so we create a ghost variable that establishes
it *)
Definition is_sb γ (sb: superblockT): iProp Σ :=
  ghost_var γ DfracDiscarded sb ∗ ⌜superblock_wf sb⌝.

#[global] Instance is_sb_persistent γ sb : Persistent (is_sb γ sb) := _.

Lemma is_sb_agree γ sb1 sb2 :
  is_sb γ sb1 -∗ is_sb γ sb2 -∗ ⌜sb1 = sb2⌝.
Proof.
  rewrite /is_sb.
  iIntros "[H1 _] [H2 _]". iDestruct (ghost_var_agree with "H1 H2") as %?.
  auto.
Qed.

Lemma is_sb_to_wf γ sb :
  is_sb γ sb -∗ ⌜superblock_wf sb⌝.
Proof.
  iIntros "[_ $]".
Qed.

(*@ type Superblock struct {                                                @*)
(*@     LogBlocks        uint64                                             @*)
(*@     InodeBlocks      uint64                                             @*)
(*@     DataBitmapBlocks uint64                                             @*)
(*@     DataBlocks       uint64                                             @*)
(*@ }                                                                       @*)
Definition superblock_fields (l : loc) dq (sb: superblockT) : iProp Σ :=
    "logBlocks" ∷ l ↦[Superblock :: "LogBlocks"]{dq} #(sb.(log_blocks)) ∗
    "inodeBlocks" ∷ l ↦[Superblock :: "InodeBlocks"]{dq} #(sb.(inode_blocks)) ∗
    "dataBitmapBlocks" ∷ l ↦[Superblock :: "DataBitmapBlocks"]{dq} #(sb.(data_bitmap_blocks)) ∗
    "dataBlocks" ∷ l ↦[Superblock :: "DataBlocks"]{dq} #(sb.(data_blocks)).

Definition is_superblock_mem (l : loc) (sb: superblockT) : iProp Σ :=
    "logBlocks" ∷ l ↦[Superblock :: "LogBlocks"]{DfracDiscarded} #(sb.(log_blocks)) ∗
    "inodeBlocks" ∷ l ↦[Superblock :: "InodeBlocks"]{DfracDiscarded} #(sb.(inode_blocks)) ∗
    "dataBitmapBlocks" ∷ l ↦[Superblock :: "DataBitmapBlocks"]{DfracDiscarded} #(sb.(data_bitmap_blocks)) ∗
    "dataBlocks" ∷ l ↦[Superblock :: "DataBlocks"]{DfracDiscarded} #(sb.(data_blocks)) ∗
    "%Hwf" ∷ ⌜superblock_wf sb⌝.
Global Instance is_superblock_mem_persistent l sb : Persistent (is_superblock_mem l sb) := _.

Definition is_superblock γ l sb: iProp Σ :=
  "Hsb_mem" ∷ is_superblock_mem l sb ∗ "Hsb" ∷ is_sb γ sb.
Global Instance is_superblock_persistent γ l sb : Persistent (is_superblock γ l sb) := _.

Lemma is_superblock_get_is_sb γ l sb :
  is_superblock γ l sb -∗ is_sb γ sb.
Proof.
  rewrite /is_superblock. iIntros "[? ?]". iFrame.
Qed.

Lemma div_roundup_exact (i k: Z) :
  0 < k →
  (i + k - 1) / k = if decide (i `mod` k = 0) then i / k else i / k + 1.
Proof.
  intros H0.
  assert (k ≠ 0) by lia.
  destruct (decide _).
  - rewrite {1}(Z.div_mod i k) //.
    rewrite e.
    replace (k * i `div` k + 0 + k - 1) with (k - 1 + (i `div` k * k)) by lia.
    rewrite Z.div_add //.
    rewrite Z.div_small; [ | lia ].
    lia.
  - rewrite {1}(Z.div_mod i k) //.
    replace (k * i `div` k + i `mod` k + k - 1)
              with ((i `mod` k - 1) + (i `div` k + 1) * k) by lia.
    rewrite Z.div_add //.
    rewrite Z.div_small; [ | lia ].
    lia.
Qed.

Lemma div_roundup_characterize (i k: Z) :
  0 < k →
  i / k ≤ (i + k - 1) / k ≤ i / k + 1.
Proof.
  intros H.
  rewrite div_roundup_exact //.
  destruct (decide _); lia.
Qed.

Lemma wp_mkSuperblockNoWf (sz: w64) :
  {{{ True }}}
    mkSuperblockNoWf #sz
  {{{ (l: loc) sb, RET #l; superblock_fields l (DfracDiscarded) sb ∗ ⌜15 ≤ uint.Z sz < 0x1_0000_0000⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "%Hsz".
  wp_call.
  case_bool_decide as Hsz1; wp_pures.
  2: wp_apply wp_Assume_false.
  case_bool_decide as Hsz2; wp_pures.
  2: wp_apply wp_Assume_false.
  wp_apply wp_Assume; iIntros (_).
  wp_pures.
  wp_apply wp_allocStruct; [ val_ty | ].
  iIntros (l) "Hsb".
  wp_pures.
  iMod (struct_pointsto_persist with "Hsb") as "Hsb".
  iModIntro.
  iApply ("HΦ" $! l (Build_superblockT _ _ _ _)).
  iSplit.
  - iApply struct_fields_split in "Hsb". iDestruct "Hsb" as "#Hsb". iNamed "Hsb".
    iFrame "#".
  - iPureIntro. word.
Qed.

Lemma inv_litint (i1 i2: w64) :
  #i1 = #i2 → i1 = i2.
Proof.
  inversion 1; subst; auto.
Qed.

Lemma wp_InitSuperblock (sz: w64) :
  {{{ True }}}
    InitSuperblock #sz
  {{{ (l: loc) sb, RET #l; is_superblock_mem l sb ∗ ⌜sb_used_blocks sb = uint.Z sz⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "_".
  wp_call.
  wp_apply (wp_mkSuperblockNoWf).
  iIntros (l sb) "[Hfields %Hsz]".
  wp_pures.
  iNamed "Hfields".
  do 2 wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow); iIntros (Hadd1).
  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow); iIntros (Hadd2).
  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow); iIntros (Hadd3).
  wp_apply (std_proof.wp_SumAssumeNoOverflow); iIntros (Hadd4).
  rewrite -> Hadd1, Hadd2, Hadd3 in *.
  wp_pures.
  rewrite /Superblock__allocatableDataBlocks.
  repeat wp_loadField. wp_pures.
  change (word.mul (W64 4096) (W64 8)) with (W64 32768).
  wp_apply wp_Assume. rewrite bool_decide_eq_true.
  iIntros (Hdata_block_bound).
  wp_apply wp_Assume. rewrite bool_decide_eq_true.
  iIntros (Hused%inv_litint%(f_equal uint.Z)).
  rewrite -> Hadd4 in *.
  wp_pures.
  iModIntro. iApply "HΦ".
  iFrame.
  iSplit.
  - iPureIntro.
    constructor.
    + word.
    + rewrite /allocatable_data_blocks.
      change (BlkSize * 8) with 32768.
      move: Hdata_block_bound.
      rewrite word.unsigned_mul_nowrap; [ | word ].
      word.
    + word.
  - iPureIntro.
    word.
Qed.

Lemma wp_Superblock__allocatableDataBlocks (l : loc) sb :
  {{{ is_superblock_mem l sb }}}
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
  {{{ is_superblock_mem l sb }}}
    Superblock__Wf #l
  {{{ RET #true; True }}}.
Proof.
  (*@ func (sb *Superblock) Wf() bool {                                       @*)
  (*@     return (                                                            @*)
  (*@     // no overflow in total number of blocks, and reasonable maximum size @*)
  (*@     std.SumNoOverflow(1, sb.LogBlocks) &&                               @*)
  (*@         std.SumNoOverflow(1+sb.LogBlocks, sb.InodeBlocks) &&            @*)
  (*@         std.SumNoOverflow(1+sb.LogBlocks, sb.InodeBlocks) &&            @*)
  (*@         std.SumNoOverflow(1+sb.LogBlocks+sb.InodeBlocks, sb.DataBitmapBlocks) && @*)
  (*@         std.SumNoOverflow(1+sb.LogBlocks+sb.InodeBlocks+sb.DataBitmapBlocks, sb.DataBlocks) && @*)
  (*@         sb.UsedBlocks() < 0x1_0000_0000) &&                             @*)
  (*@         // should be able to allocate all the data blocks using the data bitmaps @*)
  (*@         (sb.allocatableDataBlocks() >= sb.DataBlocks) &&                @*)
  (*@         // block pointers are 32 bits, they should be able to address all blocks @*)
  (*@         (sb.DataBlocks < 0x1_0000_0000)                                 @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iPoseProof "Hpre" as "#Hwf".
  iPoseProof "Hwf" as "Hwf2". iNamed "Hwf2".
  pose proof Hwf as Hwf'; destruct Hwf'.
  wp_rec.

  repeat wp_loadField.
  wp_apply std_proof.wp_SumNoOverflow.
  rewrite bool_decide_eq_true_2 //; [ | word ]. wp_pures.

  repeat wp_loadField.
  wp_apply std_proof.wp_SumNoOverflow.
  rewrite bool_decide_eq_true_2 //; [ | word ]. wp_pures.

  repeat wp_loadField.
  wp_apply std_proof.wp_SumNoOverflow.
  rewrite bool_decide_eq_true_2 //; [ | word ]. wp_pures.

  repeat wp_loadField.
  wp_apply std_proof.wp_SumNoOverflow.
  rewrite bool_decide_eq_true_2 //; [ | word ]. wp_pures.

  repeat wp_loadField.
  wp_apply std_proof.wp_SumNoOverflow.
  rewrite bool_decide_eq_true_2 //; [ | word ]. wp_pures.

  repeat (wp_rec || wp_loadField || wp_pures).
  rewrite bool_decide_eq_true_2 //; [ | word ]. wp_pures.

  repeat wp_loadField.
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

Theorem wp_Superblock__InodeStart (l : loc) sb :
  {{{ is_superblock_mem l sb }}}
    Superblock__InodeStart #l
  {{{ (x: w64), RET #x; ⌜uint.Z x = sb_inode_start sb⌝ }}}.
Proof.
  (*@ func (sb *Superblock) InodeStart() uint64 {                             @*)
  (*@     return sb.LogStart() + sb.LogBlocks                                 @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "#Hsb".
  iNamed "Hsb".
  repeat (wp_rec || wp_loadField || wp_pures).
  iApply "HΦ".
  iPureIntro.
  destruct Hwf.
  word.
Qed.

Theorem wp_Superblock__DataBitmapStart (l : loc) sb :
  {{{ is_superblock_mem l sb }}}
    Superblock__DataBitmapStart #l
  {{{ (x: w64), RET #x; ⌜uint.Z x = sb_data_bitmap_start sb⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "#Hsb".
  iNamed "Hsb".
  repeat (wp_rec || wp_loadField || wp_pures).
  iApply "HΦ".
  iPureIntro.
  destruct Hwf.
  word.
Qed.

Theorem wp_Superblock__DataStart (l : loc) sb :
  {{{ is_superblock_mem l sb }}}
    Superblock__DataStart #l
  {{{ (x: w64), RET #x; ⌜uint.Z x = sb_data_start sb⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "#Hsb".
  iNamed "Hsb".
  repeat (wp_rec || wp_loadField || wp_pures).
  iApply "HΦ".
  iPureIntro.
  destruct Hwf.
  word.
Qed.

Definition magicConst_: Z := 0x94f6c920688f08a6.

Definition sb_encode sb : list u8 :=
  u64_le magicConst_ ++
  u64_le sb.(log_blocks) ++
  u64_le sb.(inode_blocks) ++
  u64_le sb.(data_bitmap_blocks) ++
  u64_le sb.(data_blocks) ++
  replicate 4056 (U8 0). (* 4096 - 8*5 *)

Lemma sb_encode_len sb : length (sb_encode sb) = Z.to_nat BlkSize.
Proof.
  rewrite /sb_encode /BlkSize. len.
Qed.

Lemma wp_Superblock__Encode (l : loc) sb :
  {{{ is_superblock_mem l sb }}}
    Superblock__Encode #l
  {{{ s, RET (slice_val s); own_slice s u8T (DfracOwn 1) (sb_encode sb) }}}.
Proof.
  (*@ func (sb *Superblock) Encode() disk.Block {                             @*)
  (*@     var buf []byte                                                      @*)
  (*@     buf = marshal.WriteInt(buf, magicConst)                             @*)
  (*@     buf = marshal.WriteInt(buf, sb.LogBlocks)                           @*)
  (*@     buf = marshal.WriteInt(buf, sb.InodeBlocks)                         @*)
  (*@     buf = marshal.WriteInt(buf, sb.DataBitmapBlocks)                    @*)
  (*@     buf = marshal.WriteInt(buf, sb.DataBlocks)                          @*)
  (*@     padding := make([]byte, disk.BlockSize-uint64(len(buf)))            @*)
  (*@     buf = append(buf, padding...)                                       @*)
  (*@     return buf                                                          @*)
  (*@ }                                                                       @*)

  iIntros (Φ) "Hpre HΦ". iNamed "Hpre".
  wp_rec.
  wp_apply wp_ref_of_zero; [ auto | ]. iIntros (buf) "buf".
  wp_pures.
  wp_load.
  rewrite zero_slice_val.
  wp_apply wp_WriteInt.
  { iApply own_slice_zero. }
  iIntros (s1) "Hs".
  wp_store. wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "Hs").
  iIntros (s2) "Hs".
  wp_store. wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "Hs").
  iIntros (s3) "Hs".
  wp_store. wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "Hs").
  iIntros (s4) "Hs".
  wp_store. wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "Hs").
  iIntros (s5) "Hs".
  iDestruct (own_slice_sz with "Hs") as %Hsz5.
  assert (uint.Z s5.(Slice.sz) = 40) as Hlen_prefix.
  { move: Hsz5; len. }
  wp_store. wp_load. wp_apply wp_slice_len.
  wp_pures. wp_apply wp_NewSlice.
  iIntros (s_pad) "Hpadding".
  wp_load. wp_apply (wp_SliceAppendSlice with "[Hs Hpadding]"); first by auto.
  { iFrame. rewrite own_slice_to_small. iFrame. }
  iIntros (s6) "[Hs _]".
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_store. wp_load.
  iModIntro. iApply "HΦ".
  iExactEq "Hs".
  f_equal.
  autorewrite with len in Hsz.
  rewrite -!app_assoc app_nil_l.
  change (IntoVal_def w8) with (U8 0).
  rewrite /sb_encode.
  repeat f_equal.
  word.
Qed.

Theorem wp_Decode_mem buf_s dq data sb :
  {{{ own_slice_small buf_s byteT dq data ∗ ⌜data = sb_encode sb⌝ ∗ ⌜superblock_wf sb⌝ }}}
    Decode (slice_val buf_s)
  {{{ (l: loc), RET #l; is_superblock_mem l sb }}}.
Proof.
  (*@ func Decode(b disk.Block) Superblock {                                  @*)
  (*@     magic, b2 := marshal.ReadInt(b)                                     @*)
  (*@     if magic != magicConst {                                            @*)
  (*@         panic("invalid magic number")                                   @*)
  (*@     }                                                                   @*)
  (*@     logBlocks, b3 := marshal.ReadInt(b2)                                @*)
  (*@     inodeBlocks, b4 := marshal.ReadInt(b3)                              @*)
  (*@     dataBitmapBlocks, b5 := marshal.ReadInt(b4)                         @*)
  (*@     dataBlocks, _ := marshal.ReadInt(b5)                                @*)
  (*@     return Superblock{                                                  @*)
  (*@         LogBlocks:        logBlocks,                                    @*)
  (*@         InodeBlocks:      inodeBlocks,                                  @*)
  (*@         DataBitmapBlocks: dataBitmapBlocks,                             @*)
  (*@         DataBlocks:       dataBlocks,                                   @*)
  (*@     }                                                                   @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "(Hs & -> & %Hwf)".
  wp_rec.
  wp_apply (wp_ReadInt with "Hs").
  iIntros (s1) "Hs". wp_pures.
  wp_apply (wp_ReadInt with "Hs").
  iIntros (s2) "Hs". wp_pures.
  wp_apply (wp_ReadInt with "Hs").
  iIntros (s3) "Hs". wp_pures.
  wp_apply (wp_ReadInt with "Hs").
  iIntros (s4) "Hs". wp_pures.
  wp_apply (wp_ReadInt with "Hs").
  iIntros (s5) "Hs". wp_pures.
  (* we need to have a fupd to create the readonly facts *)
  rewrite -wp_ncfupd.
  wp_apply (wp_allocStruct).
  { val_ty. }
  iIntros (l) "Hsb".
  iDestruct (struct_fields_split with "Hsb") as "Hfields"; iNamed "Hfields".
  iMod (struct_field_pointsto_persist with "LogBlocks") as "#?".
  iMod (struct_field_pointsto_persist with "InodeBlocks") as "#?".
  iMod (struct_field_pointsto_persist with "DataBitmapBlocks") as "#?".
  iMod (struct_field_pointsto_persist with "DataBlocks") as "#?".
  iModIntro.
  iApply "HΦ".
  rewrite /is_superblock.
  (* TODO: iFrame is noticeably slow here, seems like it's processing ["Hs" : replicate
  4056 (W8 0)]? *)
  iClear "Hs".
  iFrame "#".
  auto.
Qed.

Lemma is_sb_init l sb :
  is_superblock_mem l sb ==∗ ∃ γ, is_superblock γ l sb.
Proof.
  rewrite /is_superblock /named.
  iIntros "Hmem".
  iAssert (⌜superblock_wf sb⌝)%I as %Hwf.
  { iNamed "Hmem". auto. }
  iFrame.
  rewrite /is_sb.
  iMod (ghost_var_alloc sb) as (γ) "Hvar".
  iMod (ghost_var_persist with "Hvar") as "$".
  auto.
Qed.

End proof.

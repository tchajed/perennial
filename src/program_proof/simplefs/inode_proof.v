From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com Require Import tchajed.simplefs.
From Goose.github_com Require Import tchajed.simplefs.inode.

From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.goose_lang.lib Require Import typed_slice.

From Perennial.program_proof.simplefs Require Import concat.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Set Default Proof Using "Type".
#[local] Unset Printing Projections.

Module inodeType.
Inductive t :=
| invalid
| dirType
| fileType.

Definition rep (x: t) : w32 :=
  W32 (match x with
  | invalid => 0
  | dirType => 1
  | fileType => 2
  end).

Definition is_valid (v: w32) :=
  0 < uint.Z v < 3.

End inodeType.

Section proof.
Context `{!heapGS Σ}.

Theorem wp_InodeType__IsValid (v: w32) :
  {{{ True }}}
    InodeType__IsValid #v
  {{{ RET #(bool_decide (inodeType.is_valid v)); True }}}.
Proof.
  (*@ func (t InodeType) IsValid() bool {                                     @*)
  (*@     return t != Invalid && t <= FileType                                @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ".
  wp_rec. wp_pures.
  iDestruct ("HΦ" with "[//]") as "HΦ".
  destruct_decide (bool_decide_reflect (#v = #(W32 0))) as Heq.
  - rewrite /=; wp_pures. iModIntro.
    iExactEq "HΦ".
    rewrite bool_decide_eq_false_2 //.
    inv Heq.
    rewrite /inodeType.is_valid. word.
  - rewrite /=; wp_pures. iModIntro.
    iExactEq "HΦ".
    repeat f_equal.
    apply bool_decide_ext.
    rewrite /inodeType.is_valid.
    cut (uint.Z v ≠ 0); [ word | ].
    { intros H.
      contradiction Heq.
      repeat f_equal.
      word. }
Qed.

End proof.

Module inode_rep.
Record t := mk {
    typ: inodeType.t;
    len: w64;
    meta: w32; (* a meta is just a w32 mode for simplicity *)
    block_ptrs: vec w32 28;
}.

#[global] Instance eta : Settable _ :=
  settable! (mk) <typ; len; meta; block_ptrs>.

Definition encode (x: t) : list w8 :=
  u32_le (inodeType.rep x.(typ)) ++ u64_le x.(len) ++ u32_le x.(meta) ++
  concat (u32_le <$> vec_to_list x.(block_ptrs)).

Lemma encode_length x : length (encode x) = 128%nat.
Proof.
  rewrite /encode.
  len.
  erewrite length_concat_uniform; [ | by eauto ].
  len.
Qed.

End inode_rep.

Hint Rewrite inode_rep.encode_length : len.

Section proof.
Context `{!heapGS Σ}.

Definition is_meta (v: val) (meta: w32) :=
  v = (#meta, #())%V.

Theorem wp_Meta__AsBytes (meta: w32) :
  {{{ True }}}
    Meta__AsBytes (#meta, #())%V
  {{{ (s : Slice.t), RET (to_val s); own_slice s byteT (DfracOwn 1) (u32_le meta) }}}.
Proof.
  (*@ func (m *Meta) AsBytes() []byte {                                       @*)
  (*@     var buf = []byte{}                                                  @*)
  (*@     buf = marshal.WriteInt32(buf, m.Mode)                               @*)
  (*@     return buf                                                          @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "_".
  rewrite /Meta__AsBytes. wp_pures.
  wp_apply (wp_NewSlice_0). iIntros (s) "Hs".
  wp_apply wp_ref_to; [ auto | ]. iIntros (l) "buf". wp_pures.
  wp_load.
  wp_apply (wp_WriteInt32 with "[$Hs]").
  iIntros (s2) "Hs".
  wp_pures. wp_store. wp_load.
  iModIntro.
  iApply "HΦ".
  rewrite app_nil_l.
  iExact "Hs".
Qed.

Theorem wp_metaFromBytes dq (s : Slice.t) meta bs :
  {{{ own_slice_small s byteT dq (u32_le meta ++ bs) }}}
    metaFromBytes (to_val s)
  {{{ (s': Slice.t), RET ((#meta, #()), s'); own_slice_small s' byteT dq bs }}}.
Proof.
  (*@ func metaFromBytes(bytes []byte) (Meta, []byte) {                       @*)
  (*@     mode, bytes2 := marshal.ReadInt32(bytes)                            @*)
  (*@     return Meta{Mode: mode}, bytes2                                     @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "Hs".
  wp_rec. wp_apply (wp_ReadInt32 with "[$Hs]").
  iIntros (s') "Hs".
  wp_pures.
  iModIntro.
  iApply "HΦ". iFrame.
Qed.

Definition own_inode (l: loc) (x: inode_rep.t): iProp Σ :=
  ∃ (s: Slice.t),
    "typ" ∷ l ↦[Inode :: "typ_"] #(inodeType.rep x.(inode_rep.typ)) ∗
    "length" ∷ l ↦[Inode :: "length"] #x.(inode_rep.len) ∗
    "meta" ∷ l ↦[Inode :: "meta"] (#x.(inode_rep.meta), #()) ∗
    "blockPtrs" ∷ l ↦[Inode :: "blockPtrs"] to_val s ∗
    "HblockPtrs" ∷ own_slice_small s uint32T (DfracOwn 1) (vec_to_list x.(inode_rep.block_ptrs)).

Theorem wp_NewInode (ty_v: u32) (t : inodeType.t) :
  {{{ ⌜ty_v = inodeType.rep t⌝ }}}
    NewInode #ty_v
  {{{ l, RET #l;
      own_inode l {|
          inode_rep.typ := t;
          inode_rep.len := W64 0;
          inode_rep.meta := W32 0;
          inode_rep.block_ptrs := fun_to_vec (λ _ : fin 28, W32 0)
        |} }}}.
Proof.
  (*@ func NewInode(t simplefs.InodeType) *Inode {                            @*)
  (*@     return &Inode{                                                      @*)
  (*@         typ_:      t,                                                   @*)
  (*@         length:    0,                                                   @*)
  (*@         meta:      Meta{Mode: 0},                                       @*)
  (*@         blockPtrs: make([]uint32, NUM_BLOCK_PTRS),                      @*)
  (*@     }                                                                   @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as %->.
  wp_rec. wp_pures.
  wp_apply wp_NewSlice.
  iIntros (s) "Hs".
  iApply own_slice_to_small in "Hs".
  wp_apply wp_allocStruct; [ val_ty | ].
  iIntros (l) "Hl".
  iDestruct (struct_fields_split with "Hl") as "Hl". iNamed "Hl".
  iApply "HΦ".
  rewrite /own_inode. iExists _. rewrite /=.
  iFrame.
Qed.

Theorem wp_Inode__GetLength (i : loc) ino :
  {{{ own_inode i ino }}}
    Inode__GetLength #i
  {{{ RET #(ino.(inode_rep.len)); own_inode i ino }}}.
Proof.
  (*@ func (i *Inode) GetLength() uint64 {                                    @*)
  (*@     return i.length                                                     @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "Hino". iNamed "Hino".
  wp_rec. wp_loadField. iApply "HΦ".
  iFrame.
Qed.

Theorem wp_Inode__SetLength (i : loc) ino (len': w64) :
  {{{ own_inode i ino }}}
    Inode__SetLength #i #len'
  {{{ RET #(); own_inode i (ino <| inode_rep.len := len' |>) }}}.
Proof.
  (*@ func (i *Inode) SetLength(length uint64) {                              @*)
  (*@     i.length = length                                                   @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "Hino". iNamed "Hino".
  wp_rec. wp_storeField. iModIntro. iApply "HΦ".
  iFrame.
Qed.

Theorem wp_Inode__AsBytes (i : loc) ino :
  {{{ own_inode i ino }}}
    Inode__AsBytes #i
  {{{ (s : Slice.t), RET (to_val s); own_slice s byteT (DfracOwn 1) (inode_rep.encode ino) ∗
                                     own_inode i ino }}}.
Proof.
  (*@ func (i *Inode) AsBytes() []byte {                                      @*)
  (*@     var buf = make([]byte, 0)                                           @*)
  (*@     buf = marshal.WriteInt32(buf, uint32(i.typ_))                       @*)
  (*@     buf = marshal.WriteInt(buf, i.length)                               @*)
  (*@     buf = append(buf, i.meta.AsBytes()...)                              @*)
  (*@     for _, ptr := range i.blockPtrs {                                   @*)
  (*@         buf = marshal.WriteInt32(buf, ptr)                              @*)
  (*@     }                                                                   @*)
  (*@     return buf                                                          @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "Hi". iNamed "Hi".
  wp_rec. wp_pures.
  wp_apply (wp_NewSlice_0). iIntros (s1) "Hs".
  wp_apply wp_ref_to; [ auto | ]. iIntros (buf_l) "buf".
  wp_pures.
  wp_loadField. wp_load.
  wp_apply (wp_WriteInt32 with "[$]").
  iIntros (s2) "Hs".
  wp_store. wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (s3) "Hs".
  wp_store. wp_loadField. wp_apply wp_Meta__AsBytes.
  iIntros (meta_s) "Hs_meta".
  iApply own_slice_to_small in "Hs_meta".
  wp_load. wp_apply (wp_SliceAppendSlice with "[$Hs $Hs_meta]"); first done.
  iIntros (s4) "[Hs _]".
  rewrite app_nil_l.
  wp_store.
  wp_loadField.

  set (ino_bs0 := (u32_le (inodeType.rep ino.(inode_rep.typ)) ++ u64_le ino.(inode_rep.len)) ++
    u32_le ino.(inode_rep.meta)).

  iDestruct (own_slice_small_sz with "HblockPtrs") as %Hs_sz.
  assert (uint.Z s.(Slice.sz) = 28).
  { move: Hs_sz. len. }

  wp_apply
    (wp_forSlice (λ (i: w64),
         ∃ (s': Slice.t),
           "buf" ∷ buf_l ↦[slice.T byteT] s' ∗
           "Hs" ∷ own_slice s' byteT (DfracOwn 1)
             (ino_bs0 ++
                concat (u32_le <$> (take (uint.nat i) ino.(inode_rep.block_ptrs)))))%I
                 with "[] [$HblockPtrs $buf Hs]"
    ).
  { iIntros (n x).
    clear Φ.
    iIntros "!>" (Φ) "(I & %Hn & %Hget) HΦ".
    iNamed "I".
    wp_pures. wp_load.
    wp_apply (wp_WriteInt32 with "[$Hs]").
    iIntros (s'') "Hs".
    wp_store.
    iModIntro.
    iApply "HΦ".
    iFrame.
    iExactEq "Hs".
    rewrite /named.
    f_equal.
    rewrite -app_assoc.
    f_equal.
    replace (uint.nat (word.add n (W64 1))) with (S (uint.nat n)) by word.
    erewrite take_S_r; eauto.
    rewrite fmap_app /= concat_app //.
  }
  { iExactEq "Hs". rewrite /named.
    rewrite take_0. rewrite fmap_nil concat_nil app_nil_r //. }
  iIntros "(I & HblockPtrs)". iNamed "I".
  wp_load. iModIntro. iApply "HΦ". iFrame.
  iExactEq "Hs".
  f_equal.
  rewrite take_ge; [ | len ].
  rewrite /inode_rep.encode //.
Qed.

Opaque concat.

Theorem wp_FromBytes (b : Slice.t) bs ino :
  {{{ own_slice b byteT (DfracOwn 1) bs ∗ ⌜bs = inode_rep.encode ino⌝ }}}
    FromBytes (to_val b)
  {{{ (l : loc), RET #l; own_inode l ino }}}.
Proof.
  (*@ func FromBytes(b []byte) *Inode {                                       @*)
  (*@     typ, b2 := marshal.ReadInt32(b)                                     @*)
  (*@     length, b3 := marshal.ReadInt(b2)                                   @*)
  (*@     meta, b4 := metaFromBytes(b3)                                       @*)
  (*@     blockPtrs := make([]uint32, NUM_BLOCK_PTRS)                         @*)
  (*@     var bytes = b4                                                      @*)
  (*@     for idx := range blockPtrs {                                        @*)
  (*@         ptr, b_next := marshal.ReadInt32(bytes)                         @*)
  (*@         bytes = b_next                                                  @*)
  (*@         blockPtrs[idx] = ptr                                            @*)
  (*@     }                                                                   @*)
  (*@     return &Inode{                                                      @*)
  (*@         typ_:      simplefs.InodeType(typ),                             @*)
  (*@         length:    length,                                              @*)
  (*@         meta:      meta,                                                @*)
  (*@         blockPtrs: blockPtrs,                                           @*)
  (*@     }                                                                   @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "[Hbs %]". subst.
  wp_rec. wp_pures.
  iApply own_slice_to_small in "Hbs".
  wp_apply (wp_ReadInt32 with "[$]").
  iIntros (s1) "Hs". wp_pures.
  wp_apply (wp_ReadInt with "[$]").
  iIntros (s2) "Hs". wp_pures.
  wp_apply (wp_metaFromBytes with "[$Hs]").
  iIntros (s3) "Hs". wp_pures.
  wp_apply (wp_NewSliceWithCap_0). iIntros (bptrs_s) "[Hblkptrs _]".
  wp_apply wp_ref_to; [ done | ]. iIntros (l) "blockPtrs".
  wp_apply wp_ref_to; [ done | ]. iIntros (l2) "bytes".
  wp_apply wp_ref_to; [ auto | ]. iIntros (l3) "i".
  wp_pures.
  change (word.add (W64 27) (W64 1)) with (W64 28).
  wp_apply (wp_forUpto
              (λ (i: w64),
                ∃ (bptrs_s: Slice.t) (s': Slice.t),
                "bytes" ∷ l2 ↦[slice.T byteT] s' ∗
                "Hs" ∷ own_slice_small s' byteT (DfracOwn 1)
                       (concat (u32_le <$> (drop (uint.nat i) (ino.(inode_rep.block_ptrs))))) ∗
                "blockptrs" ∷ l ↦[slice.T uint32T] bptrs_s ∗
                "Hblkptrs" ∷ own_slice bptrs_s uint32T (DfracOwn 1)
                  (take (uint.nat i) (ino.(inode_rep.block_ptrs)))
              )%I with "[] [$bytes $blockPtrs Hblkptrs Hs $i] "
           ).
  { word. }
  { iIntros (i). clear Φ.
    iIntros "!>" (Φ) "(I & i & %Hi) HΦ". iNamed "I".
    wp_pures.
    wp_load.
    assert (∃ ptr, vec_to_list ino.(inode_rep.block_ptrs) !! uint.nat i = Some ptr)
      as [ptr Hgeti].
    { apply lookup_lt_is_Some_2. len. }
    wp_apply (wp_ReadInt32 with "[Hs]").
    { erewrite drop_S; [ | eauto ].
      rewrite fmap_cons concat_cons. eauto. }
    iIntros (s'') "Hs".
    wp_pures. wp_store. wp_load.
    change (#ptr) with (to_val ptr).
    wp_apply (wp_SliceAppend with "[$Hblkptrs]").
    iIntros (bptrs_s') "Hblkptrs".
    wp_store.
    iModIntro. iApply "HΦ".
    iFrame.
    rewrite /named.
    iSplitL "Hs".
    - iExactEq "Hs".
      repeat (f_equal; try word).
    - iExactEq "Hblkptrs".
      f_equal.
      replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
      erewrite take_S_r; eauto.
  }
  {
    (* initial invariant *)
    rewrite drop_0 take_0. iFrame.
  }
  iIntros "(I & _)". iNamed "I".
  wp_load.
  wp_apply wp_allocStruct; [ val_ty | ].
  iIntros (l4) "Hino".
  iApply struct_fields_split in "Hino". iNamed "Hino".
  iApply "HΦ".
  iFrame.
  iApply own_slice_to_small in "Hblkptrs".
  rewrite take_ge; [ | len ].
  iFrame.
Qed.


End proof.

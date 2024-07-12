From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.
From Goose.github_com Require Import tchajed.simplefs.
From Goose.github_com Require Import tchajed.simplefs.inode.

From Perennial.program_proof Require Import marshal_stateless_proof disk_lib.
From Perennial.goose_lang.lib Require Import typed_slice.

From Perennial.program_proof.simplefs Require Import concat superblock_proof.
From iris.base_logic.lib Require Import ghost_map.

From Perennial.Helpers Require Import NatDivMod.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial Require Import options.

#[local] Unset Printing Projections.

Record inode_names :=
  { inode_map: gname;
    sb_var: gname;
  }.

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

(* auto hints *)

Lemma rep_invalid : rep invalid = W32 0.
Proof. done. Qed.
Lemma rep_dirType : rep dirType = W32 1.
Proof. done. Qed.
Lemma rep_fileType : rep fileType = W32 2.
Proof. done. Qed.

End inodeType.

Hint Resolve inodeType.rep_invalid inodeType.rep_dirType inodeType.rep_fileType : core.

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

Definition zero :=
  {| typ := inodeType.invalid;
    len := W64 0;
    meta := W32 0;
    block_ptrs := vreplicate _ (W32 0);
  |}.

Lemma encode_zero : encode zero = replicate 128%nat (W8 0).
Proof. reflexivity. Qed.

End inode_rep.

Class inodeG Σ :=
  { inode_superblockG :: superblockG Σ;
    inode_mapG :: ghost_mapG Σ w64 inode_rep.t;
  }.

Hint Rewrite inode_rep.encode_length : len.

Section proof.
Context `{!heapGS Σ} `{!inodeG Σ}.

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

Definition inode_mem (l: loc) (x: inode_rep.t): iProp Σ :=
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
      inode_mem l {|
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
  rewrite /inode_mem. iExists _. rewrite /=.
  iFrame.
Qed.

Theorem wp_Inode__GetLength (i : loc) ino :
  {{{ inode_mem i ino }}}
    Inode__GetLength #i
  {{{ RET #(ino.(inode_rep.len)); inode_mem i ino }}}.
Proof.
  (*@ func (i *Inode) GetLength() uint64 {                                    @*)
  (*@     return i.length                                                     @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "Hino". iNamed "Hino".
  wp_rec. wp_loadField. iApply "HΦ".
  iFrame.
Qed.

Theorem wp_Inode__SetLength (i : loc) ino (len': w64) :
  {{{ inode_mem i ino }}}
    Inode__SetLength #i #len'
  {{{ RET #(); inode_mem i (ino <| inode_rep.len := len' |>) }}}.
Proof.
  (*@ func (i *Inode) SetLength(length uint64) {                              @*)
  (*@     i.length = length                                                   @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "Hino". iNamed "Hino".
  wp_rec. wp_storeField. iModIntro. iApply "HΦ".
  iFrame.
Qed.

Theorem wp_Inode__AsBytes (i : loc) ino :
  {{{ inode_mem i ino }}}
    Inode__AsBytes #i
  {{{ (s : Slice.t), RET (to_val s); own_slice s byteT (DfracOwn 1) (inode_rep.encode ino) ∗
                                     inode_mem i ino }}}.
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
  {{{ own_slice_small b byteT (DfracOwn 1) bs ∗ ⌜bs = inode_rep.encode ino⌝ }}}
    FromBytes (to_val b)
  {{{ (l : loc), RET #l; inode_mem l ino }}}.
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

Transparent concat.

Definition subslice_inode (b: list w8) (inum: w64): list w8 :=
    subslice
    (uint.nat inum `mod` 32 * 128)%nat
    (uint.nat inum `mod` 32 * 128 + 128)%nat b.

(* says that block [b] located at disk block address [off] contains the right
inodes from the map [inodes] *)
Definition block_has_inodes (b: Block) (off: Z) (inodes: gmap w64 inode_rep.t) :=
  (* Quantify over [i], the inode numbers for this block. 32 = INODE_PER_BLOCK. *)
  ∀ (i: w64), off * 32 ≤ uint.Z i < off * 32 + 32 →
              ∃ ino, inodes !! i = Some ino ∧
                     inode_rep.encode ino = subslice_inode b i.

(* NOTE: normally an "auth" resource like this would be in an invariant and
accessed through a fancy update for an atomic step. This file system is not
thread safe or crash safe, and does not protect the in-disk inodes with any
mutex. Instead of using an invariant, we can simply have authoritative access
owned by the file system object and use it for the duration of any inode
access. *)
Definition inode_auth (γ: inode_names) : iProp Σ :=
  ∃ (inodes: gmap w64 inode_rep.t),
    ghost_map_auth γ.(inode_map) 1 inodes ∗
    ∃ sb, is_sb γ.(sb_var) sb ∗
          (* for each inode block... *)
          [∗ list] off ∈ seq 0 (uint.nat sb.(inode_blocks)),
             ∃ b, (sb_inode_start sb + Z.of_nat off) d↦ b ∗
                  ⌜block_has_inodes b off inodes⌝
.

(* tracks (persistently) that an inode number is in bounds wrt the global
superblock (accessed via its ghost variable) *)
Definition is_valid_ino (γ: inode_names) (inum: w64): iProp Σ :=
  (* remember that this [sb] is globally unique and read-only *)
  ∃ sb, is_sb γ.(sb_var) sb ∗
        ⌜uint.Z inum < uint.Z sb.(inode_blocks) * 32⌝.

Definition inode_ptsto (γ: inode_names) (inum: w64) (ino: inode_rep.t): iProp Σ :=
  ghost_map_elem γ.(inode_map) inum (DfracOwn 1) ino ∗
  is_valid_ino γ inum.

Definition init_inode_map (num_inodes: nat) : gmap w64 inode_rep.t :=
  list_to_map ((λ n, (W64 (Z.of_nat n), inode_rep.zero)) <$> seq 0 num_inodes).

Lemma fmap_tuple_fst {A B} (f: nat → A) (g: nat → B) (len: nat) :
  ((λ n, (f n, g n)) <$> seq 0 len).*1 =
  f <$> seq 0 len.
Proof.
  rewrite -list_fmap_compose /compose /=.
  reflexivity.
Qed.

Hint Rewrite seq_length : len.

Lemma seq_to_seqZ n m :
  seq n m = Z.to_nat <$> seqZ (Z.of_nat n) (Z.of_nat m).
Proof.
  rewrite /seqZ.
  apply (list_eq_same_length _ _ m); [ len | len | ].
  intros i x y Hbound Hget1 Hget2.
  rewrite -list_fmap_compose /compose /= in Hget2.
  fmap_Some in Hget2.
  apply lookup_seq in Hget1; intuition subst.
  apply lookup_seq in Hget2; intuition subst.
  lia.
Qed.

Lemma NoDup_w64_keys {A} (f: nat → A) n :
  Z.of_nat n < 2^64 →
  NoDup ((λ n : nat, (W64 n, f n)) <$> seq 0 n).*1.
Proof.
  intros Hbound.
  rewrite fmap_tuple_fst.
  apply NoDup_fmap_2_strong; [ | apply NoDup_seq ].
  intros x y Hx%elem_of_seq Hy%elem_of_seq Heq%(f_equal uint.Z).
  move: Heq; word.
Qed.

(* same as NoDup_w64_keys but with a w64 length *)
Lemma NoDup_w64_keys' {A} (f: nat → A) (n: w64) :
  NoDup ((λ n : nat, (W64 n, f n)) <$> seq 0 (uint.nat n)).*1.
Proof.
  apply NoDup_w64_keys.
  word.
Qed.

Lemma init_inode_map_lookup_Some (num_inodes: nat) (ino: w64) :
  0 ≤ Z.of_nat num_inodes < 2^64 →
  uint.Z ino < Z.of_nat num_inodes →
  init_inode_map num_inodes !! ino = Some inode_rep.zero.
Proof.
  rewrite /init_inode_map.
  intros Hword_bound Hbound.
  apply elem_of_list_to_map_1.
  - apply NoDup_w64_keys.
    lia.
  - apply elem_of_list_lookup.
    exists (uint.nat ino).
    apply list_lookup_fmap_Some.
    eexists. rewrite lookup_seq; split_and!; eauto.
    { move: Hbound. word. }
    f_equal; word.
Qed.

Lemma big_sepL_replicate_seq {A:Type} (Φ: nat → A → iProp Σ) (x: A) n :
  big_opL bi_sep Φ (replicate n x) ≡
    big_opL bi_sep (λ i _, Φ i x) (seq 0 n).
Proof.
  generalize dependent Φ.
  induction n; simpl; auto.
  intros Φ.
  rewrite IHn.
  rewrite (big_sepL_offset _ 1) //.
Qed.

Lemma vec_to_list_block0 `{ext_ty: ext_types} :
  vec_to_list block0 =
  replicate (uint.nat 4096) (W8 0).
Proof. reflexivity. Qed.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma init_zero_inodes (γ_sb: gname) sb :
  is_sb γ_sb sb ∗
  (1 + uint.nat sb.(log_blocks))%nat d↦∗ replicate (uint.nat sb.(inode_blocks)) block0 -∗
  |==> ∃ γ, ⌜γ.(sb_var) = γ_sb⌝ ∗
            inode_auth γ ∗
            [∗ list] inum ∈ seq 0 (uint.nat sb.(inode_blocks) * 32)%nat,
            inode_ptsto γ (W64 (Z.of_nat inum)) (inode_rep.zero).
Proof.
  iIntros "[#Hsb Hd]".
  iAssert (⌜superblock_wf sb⌝)%I as %Hwf.
  { iDestruct "Hsb" as "[_ $]". }
  set (num_inodes := (uint.nat sb.(inode_blocks) * 32)%nat).
  iMod (ghost_map_alloc (init_inode_map num_inodes)) as
    (γ_ino) "[Hauth Hfrags]".
  iModIntro. iExists (Build_inode_names γ_ino γ_sb); simpl.
  iSplit; [ done | ].
  rewrite /inode_auth /=.
  iFrame "Hauth Hsb".
  iSplitL "Hd".
  - rewrite /disk_array.
    rewrite big_sepL_replicate_seq.
    iApply (big_sepL_impl with "Hd").
    iIntros "!>" (k x Hget).
    apply lookup_seq in Hget; intuition subst.
    rewrite Nat.add_0_l.
    iIntros "Hd". iExists block0.
    iSplit.
    + iExactEq "Hd". f_equal.
      rewrite /sb_inode_start.
      word.
    + iPureIntro.
      rewrite /block_has_inodes.
      intros ino Hbound.
      exists inode_rep.zero.
      rewrite init_inode_map_lookup_Some.
      { split; first done.
        rewrite inode_rep.encode_zero.
        rewrite vec_to_list_block0.
        rewrite /subslice_inode subslice_take_drop take_replicate drop_replicate.
        f_equal.
        word. }
      { destruct Hwf.
        word. }
      word.
  - rewrite /init_inode_map big_sepM_list_to_map.
    2: { apply NoDup_w64_keys. rewrite /num_inodes.
         destruct Hwf.
         word. }
    rewrite big_opL_fmap.
    iApply (big_sepL_impl with "Hfrags").
    iIntros "!>" (k x Hget).
    apply lookup_seq in Hget as [-> Hbound].
    rewrite !Nat.add_0_l.
    iIntros "$".
    rewrite /is_valid_ino.
    iExists (sb). iFrame "Hsb".
    iPureIntro.
    destruct Hwf.
    word.
Qed.

Definition own_inode γ inum i ino: iProp _ :=
  inode_mem i ino ∗
  inode_ptsto γ inum ino.

Lemma inode_ptsto_valid γ inum ino sb :
  inode_ptsto γ inum ino -∗
  is_sb γ.(sb_var) sb -∗
  ⌜uint.Z inum < uint.Z sb.(inode_blocks) * 32⌝.
Proof.
  iIntros "[_ Hvalid] Hsb".
  iDestruct "Hvalid" as (sb2) "[Hsb2 %Hbound]".
  iDestruct (is_sb_agree with "Hsb Hsb2") as %<-.
  auto.
Qed.

Lemma inode_ptsto_lookup γ inum ino inodes :
  ghost_map_auth γ.(inode_map) 1 inodes -∗
  inode_ptsto γ inum ino -∗
  ⌜inodes !! inum = Some ino⌝.
Proof.
  iIntros "Hauth [Hptsto _]".
  iDestruct (ghost_map_lookup with "Hauth Hptsto") as "$".
Qed.

Lemma is_block_full_to_typed s (b: Block) :
  is_block_full s b =
  own_slice s byteT (DfracOwn 1) (vec_to_list b).
Proof. reflexivity. Qed.

Hint Unfold sb_inode_start : word.

Lemma inode_auth_lookup γ (inum: w64) ino sb :
  inode_auth γ -∗
  inode_ptsto γ inum ino -∗
  is_sb γ.(sb_var) sb -∗
  ∃ b, "Hb" ∷ (sb_inode_start sb + (uint.nat inum / 32)) d↦b ∗
        "Hptsto" ∷ inode_ptsto γ inum ino ∗
       "%Hinum_bound" ∷ ⌜uint.nat inum / 32 < uint.Z sb.(inode_blocks)⌝ ∗
       "%Hino_encode" ∷ ⌜inode_rep.encode ino = subslice_inode b inum⌝ ∗
       "Hauth_wand" ∷ ((sb_inode_start sb + (uint.nat inum / 32)) d↦b -∗
       inode_auth γ).
Proof.
  rewrite /named.
  iIntros "Hauth Hptsto #Hsb".
  iDestruct (is_sb_to_wf with "Hsb") as %Hwf.
  destruct Hwf.

  iDestruct (inode_ptsto_valid with "Hptsto Hsb") as %Hino_valid.
  iDestruct "Hauth" as (inodes) "[Hauth (%sb2 & Hsb2 & Hblocks)]".
  iDestruct (is_sb_agree with "Hsb Hsb2") as %<-; iClear "Hsb2".

  iDestruct (inode_ptsto_lookup with "[$] [$]") as %Hget.
  assert (uint.Z inum / 32 < uint.Z sb.(inode_blocks)) as Hino_blk_bound.
  { lia. }

  iDestruct (big_sepL_lookup_acc _ _ (Z.to_nat $ uint.Z inum / 32) with "Hblocks")
    as "[(%b & Hb & %Hb_has_inodes) Hblocks]".
  { apply lookup_seq_lt. word. }

  iExists (b). iSplitL "Hb".
  { iExactEq "Hb". repeat f_equal; word. }
  iFrame "Hptsto".
  iSplit; [ iPureIntro; word | ].

  iSplit.
  { iPureIntro.
    destruct (Hb_has_inodes inum) as [ino' [Hino_get Hino_encode]].
    { word. }
    assert (ino' = ino) by congruence; subst ino'.
    rewrite Hino_encode.
    repeat f_equal; word. }

  iIntros "Hb".
  iFrame "Hauth Hsb".
  iDestruct ("Hblocks" with "[Hb]") as "$".
  { iExists (b).
    iSplit; [ | done ].
    iExactEq "Hb". repeat f_equal; word. }
Qed.

Theorem wp_ReadInode (γ: inode_names) (sb_l: loc) sb (inum : w64) ino :
  {{{ inode_auth γ ∗
      inode_ptsto γ inum ino ∗
      is_superblock γ.(sb_var) sb_l sb }}}
    ReadInode #() #sb_l #inum
  {{{ (i : loc), RET #i;
      inode_auth γ ∗
      own_inode γ inum i ino }}}.
Proof.
  (*@ func ReadInode(d disk.Disk, sb *superblock.Superblock, i simplefs.Inum) *Inode { @*)
  (*@     blkNum := sb.InodeStart() + uint64(i)/simplefs.INODES_PER_BLOCK     @*)
  (*@     blkOff := uint64(i) % simplefs.INODES_PER_BLOCK                     @*)
  (*@     blk := d.Read(blkNum)                                               @*)
  (*@     inodeData := blk[blkOff*simplefs.INODE_SIZE : (blkOff+1)*simplefs.INODE_SIZE] @*)
  (*@     ino := FromBytes(inodeData)                                         @*)
  (*@     return ino                                                          @*)
  (*@ }                                                                       @*)

  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "(Hauth & Hptsto & #Hsb)".
  iNamed "Hsb".
  iDestruct (is_sb_to_wf with "Hsb") as %Hwf.
  destruct Hwf.
  iDestruct (inode_auth_lookup with "[$] [$] Hsb") as "H"; iNamed "H".

  wp_rec. wp_pures. wp_apply (wp_Superblock__InodeStart with "[$]").
  iIntros (ino_start Hino_start).
  wp_pures.

  change (word.divu (W64 4096) (W64 128)) with (W64 32).
  wp_apply (wp_Read_eq with "[$Hb]").
  { iPureIntro. word. }
  iIntros (b_s) "[Hb Hb_s]".
  (* done with the disk points-to, reassemble blocks authoritative resource *)
  iDestruct ("Hauth_wand" with "Hb") as "Hauth".

  replace (uint.Z (word.add ino_start (word.divu inum (W64 32)))) with
    (uint.Z ino_start + uint.Z inum / 32) by word.
  wp_pures.
  rewrite is_block_full_to_typed.
  wp_apply (wp_SliceSubslice_full with "Hb_s").
  { autorewrite with len. rewrite /block_bytes.
    word_cleanup.
    rewrite word.unsigned_mul_nowrap; [ | word ].
    rewrite word.unsigned_mul_nowrap; [ | word ].
    word. }
  iIntros (b_s') "Hb_sub".
  wp_pures.
  iApply own_slice_to_small in "Hb_sub".
  wp_apply (wp_FromBytes _ _ ino with "[$Hb_sub]").
  { iPureIntro.
    repeat first [
        rewrite -> word.unsigned_mul_nowrap by word |
            rewrite -> word.unsigned_modu_nowrap by word |
            rewrite -> word.unsigned_divu_nowrap by word |
            rewrite -> word.unsigned_add_nowrap by word
        ].
    word_cleanup.
    rewrite Z.mul_add_distr_r. rewrite Z.mul_1_l.
    rewrite Hino_encode /subslice_inode.
    f_equal; word.
  }
  iIntros (l) "Hinode".
  wp_pures.
  iModIntro.
  iApply "HΦ". iFrame.
Qed.

Hint Unfold block_bytes : word.

Definition bytes_splice_inode (b: list w8) (inum: w64) ino' : list w8 :=
  take (uint.nat inum `mod` 32 * 128) b ++
  inode_rep.encode ino' ++
  drop (uint.nat inum `mod` 32 * 128 + 128) b.

Lemma bytes_splice_inode_length (b: Block) inum ino :
  length (bytes_splice_inode b inum ino) = Z.to_nat 4096.
Proof.
  rewrite /bytes_splice_inode.
  len.
Qed.

Hint Rewrite bytes_splice_inode_length : len.

Hint Rewrite @subslice_length using len : len.

Lemma block_has_inodes_copy (inum : w64) (ino' : inode_rep.t) (inodes : gmap w64 inode_rep.t) (b : Block) :
  block_has_inodes b (uint.nat inum `div` 32)%nat inodes
  → ∀ b' : Block,
  vec_to_list b' = bytes_splice_inode b inum ino'
  → block_has_inodes b' (uint.nat inum `div` 32)%nat (<[inum := ino']> inodes).
Proof.
  intros Hb_has_inodes b' Hb'_eq.
  intros i Hi_bound.
  destruct (decide (inum = i)); subst.
  - rewrite lookup_insert.
    eexists; split; [ by eauto | ].
    rewrite /subslice_inode Hb'_eq /bytes_splice_inode.
    rewrite subslice_drop_take; [ | word ].
    rewrite drop_app_length'; [ | len ].
    rewrite take_app_length'; [ | len ].
    auto.
  - rewrite lookup_insert_ne //.
    destruct (Hb_has_inodes i) as [ino'' ?]; intuition auto.
    eexists; split; [ by eauto | ].
    cut (subslice_inode b' i = subslice_inode b i).
    { congruence. }
    rewrite Hb'_eq /subslice_inode /bytes_splice_inode.
    destruct (decide (uint.Z i < uint.Z inum)).
    + apply (list_eq_same_length _ _ 128%nat); [ len | len | ].
      intros i' b1 b2 Hle.
      repeat rewrite -> subslice_lookup by len.
      repeat rewrite -> lookup_app_l by len.
      rewrite -> lookup_take by len.
      congruence.
    + assert (uint.Z i > uint.Z inum).
      {
        assert (uint.Z i ≠ uint.Z inum); [ | word ].
        intros ?.
        contradiction n; word.
      }

      apply (list_eq_same_length _ _ 128%nat); [ len | len | ].

      intros i' b1 b2 Hle.
      repeat rewrite -> subslice_lookup by len.
      repeat rewrite -> lookup_app_r by len.
      rewrite -> lookup_drop by len.
      autorewrite with len.
      match goal with
      | |- vec_to_list b !! ?n1 = _ → vec_to_list b !! ?n2 = _ -> _ =>
          assert (n1 = n2); [ | congruence ]
      end.
      word.
Qed.

Lemma seq_split_one start len i :
  (start ≤ i < len)%nat →
  seq start len = seq start (i-start)%nat ++ [i] ++ seq (i+1) (len - (i-start) - 1).
Proof.
  intros Hi.
  replace len with ((i-start) + 1 + (len-(i-start)-1))%nat at 1 by lia.
  rewrite !seq_app -app_assoc.
  f_equal.
  f_equal.
  - simpl. f_equal. lia.
  - f_equal. lia.
Qed.

Lemma big_sepL_seq_split_one i (Φ: nat → iProp Σ) start len :
  (start ≤ i < len)%nat →
  big_opL bi_sep (λ _ k, Φ k) (seq start len) ⊣⊢
  big_opL bi_sep (λ _ k, Φ k) (seq start (i - start)%nat) ∗
  Φ i ∗
  big_opL bi_sep (λ _ k, Φ k) (seq (i+1)%nat (len - (i-start) - 1)).
Proof.
  intros H.
  rewrite (seq_split_one start len i) //.
  rewrite !big_sepL_app.
  f_equiv.
  f_equiv.
  simpl. rewrite sep_emp //.
Qed.

Lemma block_has_inodes_insert_other i ino (off0 num: nat) (start: Z) inodes :
  (* the block for this inode is not part of the range *)
  ¬ (off0 ≤ uint.nat i / 32 < off0 + num)%nat →
  ([∗ list] off ∈ seq off0 num,
    ∃ b, (start + Z.of_nat off) d↦ b ∗ ⌜block_has_inodes b off inodes⌝) -∗
  ([∗ list] off ∈ seq off0 num,
    ∃ b, (start + Z.of_nat off) d↦ b ∗ ⌜block_has_inodes b off (<[i := ino]> inodes)⌝).
Proof.
  intros Hother_block.
  iIntros "H".
  iApply (big_sepL_impl with "H").
  iIntros "!>" (k off Hget) "Hb".
  iDestruct "Hb" as (b) "[Hb %Hhas_inodes]".
  iExists _; iFrame.
  iPureIntro.
  apply lookup_seq in Hget as [-> Hbound].
  intros i' Hi'.
  destruct (Hhas_inodes i') as [ino' [Hino' Hencode]]; auto.
  exists ino'.
  rewrite lookup_insert_ne //.
  intros <-.
  lia.
Qed.

Lemma inode_auth_insert γ (inum: w64) ino ino' sb :
  inode_auth γ -∗
  inode_ptsto γ inum ino -∗
  is_sb γ.(sb_var) sb -∗
  |==> ∃ b, "Hb" ∷ (sb_inode_start sb + (uint.nat inum / 32)) d↦b ∗
        "Hptsto" ∷ inode_ptsto γ inum ino' ∗
       "%Hinum_bound" ∷ ⌜uint.nat inum / 32 < uint.Z sb.(inode_blocks)⌝ ∗
       "%Hino_encode" ∷ ⌜inode_rep.encode ino = subslice_inode b inum⌝ ∗
       "Hauth_wand" ∷ (∀ (b': Block),
                         ⌜vec_to_list b' =
                           bytes_splice_inode b inum ino'⌝ ∗
                         (sb_inode_start sb + (uint.nat inum / 32)) d↦b' -∗
       inode_auth γ).
Proof.
  rewrite /named.
  iIntros "Hauth Hptsto #Hsb".
  iDestruct (is_sb_to_wf with "Hsb") as %Hwf.
  destruct Hwf.

  iDestruct (inode_ptsto_valid with "Hptsto Hsb") as %Hino_valid.
  iDestruct "Hauth" as (inodes) "[Hauth (%sb2 & Hsb2 & Hblocks)]".
  iDestruct (is_sb_agree with "Hsb Hsb2") as %<-; iClear "Hsb2".

  iDestruct (inode_ptsto_lookup with "[$] [$]") as %Hget.
  assert (uint.Z inum / 32 < uint.Z sb.(inode_blocks)) as Hino_blk_bound.
  { lia. }

  iDestruct (big_sepL_seq_split_one (uint.nat inum / 32)%nat with "Hblocks") as
    "(Hblocks1 & Hb & Hblocks2)".
  { word. }
  iDestruct "Hb" as "(%b & Hb & %Hb_has_inodes)".

  iDestruct "Hptsto" as "[Hptsto #Hvalid_ino]".
  iMod (ghost_map_update ino' with "Hauth Hptsto") as "[Hauth Hptsto]".
  iModIntro.

  iExists (b). iSplitL "Hb".
  { iExactEq "Hb". repeat f_equal; word. }
  iFrame "Hptsto Hvalid_ino".
  iSplit; [ iPureIntro; word | ].

  iDestruct (block_has_inodes_insert_other inum ino' with "Hblocks1") as "Hblocks1".
  { word. }
  iDestruct (block_has_inodes_insert_other inum ino' with "Hblocks2") as "Hblocks2".
  { word. }

  iSplit.
  { iPureIntro.
    destruct (Hb_has_inodes inum) as [ino2 [Hino_get Hino_encode]].
    { word. }
    assert (ino2 = ino) by congruence; subst ino2.
    rewrite Hino_encode.
    repeat f_equal; word. }

  iIntros (b') "[%Hb'_eq Hb]".
  iFrame "Hauth Hsb".
  iApply big_sepL_seq_split_one; [ | iFrame "Hblocks1 Hblocks2" ].
  { word. }
  iExists (b'). iSplit.
  { iExactEq "Hb". repeat f_equal; word. }
  iPureIntro.
  eapply block_has_inodes_copy; eauto.
Qed.

Lemma wp_copyInodeToBlock (blk : Slice.t) b (inum: w64) (i : loc) ino :
  {{{ is_block_full blk b ∗ inode_mem i ino }}}
    copyInodeToBlock blk #inum #i
  {{{ RET #();
      is_block_full blk (list_to_block (bytes_splice_inode b inum ino)) ∗
      inode_mem i ino
  }}}.
Proof.
  (*@ func copyInodeToBlock(blk disk.Block, inum simplefs.Inum, i *Inode) {   @*)
  (*@     blkOff := uint64(inum) % simplefs.INODES_PER_BLOCK                  @*)
  (*@     copy(blk[blkOff*simplefs.INODE_SIZE:(blkOff+1)*simplefs.INODE_SIZE], i.AsBytes()) @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "[Hb Hino]".
  wp_rec. wp_pures.
  wp_apply (wp_Inode__AsBytes with "Hino").
  iIntros (s) "[Hs Hino]".
  rewrite is_block_full_to_typed.
  iDestruct (own_slice_split_1 with "Hb") as "[Hb Hcap]".
  iApply own_slice_to_small in "Hs".
  wp_apply (wp_SliceCopy_subslice with "[$Hs $Hb]").
  { iPureIntro.
    autorewrite with len.
    change (word.divu (W64 4096) (W64 128)) with (W64 32).
    rewrite word.unsigned_mul_nowrap; [ | word ].
    rewrite word.unsigned_mul_nowrap; [ | word ].
    word.
  }

  iIntros (n) "(% & Hb & Hs)".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame "Hino".
  rewrite is_block_full_to_typed.
  rewrite own_slice_split; iFrame "Hcap".
  iExactEq "Hb".
  f_equal.
  rewrite /bytes_splice_inode.
  rewrite list_to_block_to_list; [ | len ].
  change (word.divu (W64 4096) (W64 128)) with (W64 32).
  rewrite word.unsigned_mul_nowrap; [ | word ].
  rewrite word.unsigned_mul_nowrap; [ | word ].
  rewrite word.unsigned_modu_nowrap; [ | word ].
  repeat f_equal; word.
Qed.

Theorem wp_Inode__Write γ (i : loc) ino (sb_l : loc) sb (inum : w64) :
  {{{ inode_auth γ ∗
      (* permission to write *)
      (∃ ino0, inode_ptsto γ inum ino0) ∗
      (* the new in-memory inode *)
      inode_mem i ino ∗
      is_superblock γ.(sb_var) sb_l sb
  }}}
    Inode__Write #i #() #sb_l #inum
  {{{ RET #(); inode_auth γ ∗
               own_inode γ inum i ino }}}.
Proof.
  (*@ func (i *Inode) Write(d disk.Disk, sb *superblock.Superblock, inum simplefs.Inum) { @*)
  (*@     blkNum := sb.InodeStart() + uint64(inum)/simplefs.INODES_PER_BLOCK  @*)
  (*@     blkOff := uint64(inum) % simplefs.INODES_PER_BLOCK                  @*)
  (*@     blk := d.Read(blkNum)                                               @*)
  (*@     copy(blk[blkOff*simplefs.INODE_SIZE:(blkOff+1)*simplefs.INODE_SIZE], i.AsBytes()) @*)
  (*@     d.Write(blkNum, blk)                                                @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "(Hauth & Hptsto & Hino' & #Hsb)".
  iDestruct "Hptsto" as (ino0) "Hptsto".
  iNamed "Hsb".
  iDestruct (is_sb_to_wf with "Hsb") as %Hwf.
  destruct Hwf.
  iMod (inode_auth_insert with "[$] [$] Hsb") as "H"; iNamed "H".

  wp_rec. wp_pures. wp_apply (wp_Superblock__InodeStart with "[$]").
  iIntros (ino_start Hino_start).
  wp_pures.

  iDestruct (inode_ptsto_valid with "Hptsto Hsb") as %Hino_valid.
  change (word.divu (W64 4096) (W64 128)) with (W64 32).
  wp_apply (wp_Read_eq with "[$Hb]").
  { iPureIntro. word. }
  iIntros (b_s) "[Hb Hb_s]".

  wp_pures.
  wp_apply (wp_copyInodeToBlock with "[$Hb_s $Hino']").
  iIntros "[Hb_s Hino']".
  wp_pures.
  rewrite is_block_full_to_typed.
  iApply own_slice_to_small in "Hb_s".
  wp_apply (wp_Write' with "[$Hb $Hb_s]").
  { iPureIntro. word. }
  iIntros "[Hb Hb_s]".

  iDestruct ("Hauth_wand" with "[$Hb]") as "Hauth".
  { iPureIntro. rewrite list_to_block_to_list; [ | len ].
    eauto.
  }

  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

End proof.

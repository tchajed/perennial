From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_prelude.
From Goose.github_com Require Import tchajed.simplefs.
From Goose.github_com Require Import tchajed.simplefs.inode.

From Perennial.program_proof Require Import marshal_stateless_proof.
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
  {{{ own_slice b byteT (DfracOwn 1) bs ∗ ⌜bs = inode_rep.encode ino⌝ }}}
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

Transparent concat.

Definition block_has_inodes (b: Block) (off: Z) (inodes: gmap w64 inode_rep.t) :=
  ∀ (i: w64), off * 32 ≤ uint.Z i < (off + 1) * 32 →
              ∃ ino, inodes !! i = Some ino ∧
                     inode_rep.encode ino =
                     subslice (Z.to_nat off `mod` 32)%nat (Z.to_nat off `mod` 32 + 128)%nat b.

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

Lemma init_inode_map_lookup_Some (num_inodes: Z) (ino: w64) :
  0 ≤ num_inodes < 2^64 →
  uint.Z ino < uint.Z num_inodes →
  init_inode_map (Z.to_nat num_inodes) !! ino = Some inode_rep.zero.
Proof.
  rewrite /init_inode_map.
  intros Hword_bound Hbound.
  apply elem_of_list_to_map_1.
  - apply NoDup_w64_keys.
    lia.
  - apply elem_of_list_lookup.
    exists (uint.nat ino).
    apply list_lookup_fmap_Some.
    eexists. rewrite lookup_seq; (intuition eauto); try word.
    { move: Hbound. word. }
    f_equal; word.
  (*
  word_cleanup.
  assert (uint.Z num_inodes = Z.of_nat (uint.nat num_inodes)) as HnumZ by lia.
  rewrite -> HnumZ in *.
  generalize dependent (uint.nat num_inodes); intros.
  clear dependent num_inodes.

  induction n.
  - simpl. rewrite bool_decide_eq_false_2; [ | lia]. auto.
  - rewrite Nat2Z.id /=.
    destruct (decide (W64 n = ino)) as [? | Hne]; subst;
      [ rewrite lookup_insert // | rewrite lookup_insert_ne // ].
    + rewrite bool_decide_eq_true_2; [ | word ]. auto.
    + rewrite Nat2Z.id in IHn.
      rewrite IHn; [ | lia ].
      case_bool_decide; case_bool_decide; auto; try lia.
      contradiction Hne; word.
*)
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
            [∗ list] inum ∈ seq 0 (Z.to_nat $ uint.Z sb.(inode_blocks) * 32),
            inode_ptsto γ (W64 (Z.of_nat inum)) (inode_rep.zero).
Proof.
  iIntros "[#Hsb Hd]".
  iAssert (⌜superblock_wf sb⌝)%I as %Hwf.
  { iDestruct "Hsb" as "[_ $]". }
  set (num_inodes := Z.to_nat $ uint.Z sb.(inode_blocks) * 32).
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
        rewrite subslice_take_drop take_replicate drop_replicate.
        f_equal.
        word. }
      { destruct Hwf.
        word. }
      word_cleanup.
      rewrite wrap_small; try lia.
      destruct Hwf.
      split; [ lia | ].
      cut (uint.Z (inode_blocks sb) < (2^64) / 32); word.
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

Admitted.

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
Admitted.

End proof.

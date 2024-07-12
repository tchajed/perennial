From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com Require Import tchajed.simplefs.
From Goose.github_com Require Import tchajed.simplefs.inode.

From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.goose_lang.lib Require Import typed_slice.

Set Default Proof Using "Type".

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
Record t := {
    typ: inodeType.t;
    len: w64;
    meta: w32; (* a meta is just a w32 mode for simplicity *)
    block_ptrs: vec w32 28;
}.
End inode_rep.

Section proof.
Context `{!heapGS Σ}.

Definition is_meta (v: val) (meta: w32) :=
  v = (#meta, #())%V.

Theorem wp_Meta__AsBytes (meta: w32) :
  {{{ True }}}
    Meta__AsBytes (#meta, #())
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


End proof.

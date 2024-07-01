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
    meta: w32; (* a meta ia just a w32 mode for simplicity *)
    block_ptrs: vec w32 28;
}.

Section proof.
Context `{!heapGS Σ}.

Definition is_meta (v: val) (meta: w32) :=
  v = (#meta, #())%V.

End proof.

From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com Require Import tchajed.simplefs.directory.

From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.goose_lang.lib Require Import typed_slice.

Coercion LitString : string >-> base_lit.

Set Default Proof Using "Type".

(*! dir_ent and associated pure theory *)

(* TODO: wrap in Coq Module for namespacing *)
Record dir_ent :=
  mk_dir_ent
    (* in Coq [list] values are easier to work with, while in Go and GooseLang
    [string] is preferred since it's a value *)
    { path: list u8;
      inum: w64; }.

Definition dent_size: Z := 256.
Definition dent_len: Z := 256 - 8.
(* TODO: code ensures there's at least one padding byte, but this isn't
necessary (max_name_len = dent_len should work) *)
Definition max_name_len: Z := 256 - 9.

Record dir_ent_ok (e: dir_ent) :=
  { dir_ent_nonnull: ∀ i b, e.(path) !! i = Some b → b ≠ W8 0;
    dir_ent_fits: Z.of_nat (length e.(path)) < max_name_len;
  }.

Definition pad_path (p: list u8): list u8 :=
  p ++ replicate (Z.to_nat dent_len - length p)%nat (W8 0).

Definition encode_dir_ent (e: dir_ent): list u8 :=
  pad_path e.(path) ++ u64_le e.(inum).

Hint Unfold dent_size max_name_len dent_len : word.
Hint Unfold max_name_len : word.

Lemma encode_dir_ent_length (e: dir_ent) :
  dir_ent_ok e → length (encode_dir_ent e) = Z.to_nat dent_size.
Proof.
  destruct 1.
  rewrite /encode_dir_ent /pad_path; len.
Qed.

(*! list dir_ent theory *)

(* An encoded and in-memory directory is a [list dir_ent]. This has the
a deterministic encoding. *)

Definition encode_dir_ents (es: list dir_ent) : list w8 :=
  concat (encode_dir_ent <$> es).

Record dir_ents_ok (es: list dir_ent) :=
  { forall_ents_ok: Forall dir_ent_ok es;
    paths_unique: NoDup (path <$> es);
  }.

Hint Resolve forall_ents_ok paths_unique : core.

Lemma encode_dir_ents_length (es: list dir_ent) :
  Forall dir_ent_ok es →
  length (encode_dir_ents es) = Z.to_nat (dent_size * (Z.of_nat $ length es)).
Proof.
  rewrite /encode_dir_ents.
  induction es as [|e es]; intros.
   - simpl; auto.
   - simpl.
     rewrite length_app.
     inversion H as [|?? He Hes]; subst.
     fold (fmap encode_dir_ent es).
     rewrite IHes //.
     rewrite encode_dir_ent_length //.
     lia.
Qed.

(*! directory gmap theory *)

Fixpoint interpret_dir_ents (es: list dir_ent) : gmap (list w8) w64 :=
  match es with
  | [] => ∅
  | e::es => <[ e.(path) := e.(inum) ]> (interpret_dir_ents es)
  end.

Section proof.
Context `{!heapGS Σ}.

Definition dir_ent_val (e: dir_ent) : val :=
  (#(bytes_to_string e.(path)), (#e.(inum), #())).

Definition dir_ent_from_val (v: val): option dir_ent :=
  match v with
  | ((LitV (LitString p)), (LitV (LitInt i), #()))%V =>
      Some (mk_dir_ent (string_to_bytes p) i)
  | _ => None
  end.

#[global] Instance dir_ent_IntoVal : IntoVal dir_ent.
Proof.
  refine {| to_val := dir_ent_val;
           from_val := dir_ent_from_val;
           IntoVal_def := (mk_dir_ent [] (W64 0));
         |}.
  destruct v; simpl.
  rewrite bytes_to_string_inj //.
Defined.

Fixpoint non_null_prefix (bs: list w8) :=
  match bs with
  | [] => []
  | b :: bs =>
      if decide (b = W8 0) then [] else b :: non_null_prefix bs
  end.

Lemma non_null_prefix_not_null bs :
  ∀ i b, non_null_prefix bs !! i = Some b →
         b ≠ U8 0.
Proof.
  induction bs; [ done | simpl ].
  intros i b. destruct (decide _); auto.
  intros ?%lookup_cons_Some; (intuition subst); eauto.
Qed.

Theorem wp_tillNullTerminator (s : Slice.t) dq (bs: list w8) :
  {{{ own_slice s byteT dq bs }}}
    tillNullTerminator (slice_val s)
  {{{ (s' : Slice.t), RET (to_val s');
      own_slice s' byteT dq (non_null_prefix bs) }}}.
Proof.
  (*@ func tillNullTerminator(s []byte) []byte {                              @*)
  (*@     // TODO: this awkward implementation is due to Goose loop limitations @*)
  (*@     var nullIndex *uint64                                               @*)
  (*@     for i := uint64(0); i < uint64(len(s)); i++ {                       @*)
  (*@         if nullIndex == nil && s[i] == 0 {                              @*)
  (*@             nullIndex = &i                                              @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@     if nullIndex == nil {                                               @*)
  (*@         return s                                                        @*)
  (*@     } else {                                                            @*)
  (*@         return s[:*nullIndex]                                           @*)
  (*@     }                                                                   @*)
  (*@ }                                                                       @*)
Admitted.

Theorem wp_DirEnt__Encode (e: dir_ent) :
  {{{ ⌜dir_ent_ok e⌝ }}}
    DirEnt__Encode (dir_ent_val e)
  {{{ (s : Slice.t), RET (to_val s); own_slice s byteT (DfracOwn 1) (encode_dir_ent e) }}}.
Proof.
  (*@ func (d DirEnt) Encode() []byte {                                       @*)
  (*@     var buf = []byte(d.Path)                                            @*)
  (*@     buf = append(buf, make([]byte, nameLen-uint64(len(d.Path)))...)     @*)
  (*@     buf = marshal.WriteInt(buf, uint64(d.Inum))                         @*)
  (*@     return buf                                                          @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "%Hok".
  wp_rec. wp_pures.
  wp_apply wp_StringToBytes. iIntros (p_s) "Hpath".
  rewrite bytes_to_string_inj.
  iDestruct (own_slice_sz with "Hpath") as %Hlen.
  wp_apply wp_ref_to; [ auto | ].
  iIntros (l) "buf".
  wp_pures.
  wp_apply wp_NewSlice. iIntros (pad_s) "Hpad".
  wp_load.
  iApply own_slice_to_small in "Hpad".
  wp_apply (wp_SliceAppendSlice with "[$Hpath $Hpad]").
  { auto. }
  iIntros (s2) "[Hs _]".
  wp_store. wp_pures.
  wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (s3) "Hs".
  wp_store. wp_load. iModIntro. iApply "HΦ".
  iExactEq "Hs".
  f_equal.
  rewrite /encode_dir_ent.
  f_equal.
  rewrite /pad_path.
  f_equal.
  f_equal.
  destruct Hok.
  len.
Qed.

Theorem wp_decodeDirEnt s dq (e: dir_ent) (bs: list w8) :
  {{{ own_slice s byteT dq bs ∗ ⌜bs = encode_dir_ent e⌝ }}}
    decodeDirEnt (to_val s)
  {{{ RET (to_val e); own_slice s byteT dq bs }}}.
Proof.
Admitted.

End proof.

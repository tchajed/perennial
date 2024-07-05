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
  { dir_ent_nonnull: Forall (λ b, b ≠ W8 0) e.(path);
    dir_ent_fits: Z.of_nat (length e.(path)) < max_name_len;
  }.

Definition pad_path (p: list u8): list u8 :=
  p ++ replicate (Z.to_nat dent_len - length p)%nat (W8 0).

Lemma pad_path_length p :
  length (pad_path p) = (length p + (Z.to_nat dent_len - length p))%nat.
Proof. rewrite /pad_path. len. Qed.

Hint Rewrite pad_path_length : len.

Definition encode_dir_ent (e: dir_ent): list u8 :=
  pad_path e.(path) ++ u64_le e.(inum).

Lemma encode_dir_ent_inj e1 e2 :
  dir_ent_ok e1 →
  dir_ent_ok e2 →
  encode_dir_ent e1 = encode_dir_ent e2 →
  e1 = e2.
Proof.
  intros [] [].
  rewrite /encode_dir_ent.
  intros Heq.
  destruct e1 as [p1 i1], e2 as [p2 i2]; simpl in *.
  apply app_inj_2 in Heq as [Hpad_eq Hinum_eq]; [ | by len ].
  apply (inj u64_le) in Hinum_eq; subst.
  cut (p1 = p2). { intros; subst; auto. }
  rewrite /pad_path in Hpad_eq.
  apply app_inj_1 in Hpad_eq as [-> ]; [ done | ].
  (* TODO: non-trivial proof: if they had different lengths, the shorter one
  would have a zero byte in its encoding where its padding started, but the
  actual paths cannot have zeros *)
  admit.
Admitted.

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
     rewrite app_length.
     inversion H as [|?? He Hes]; subst.
     fold (fmap encode_dir_ent es).
     rewrite IHes //.
     rewrite encode_dir_ent_length //.
     lia.
Qed.

Lemma encode_dir_ents_cons_not_empty e es :
  encode_dir_ents (e :: es) ≠ [].
Proof.
  rewrite /encode_dir_ents.
  simpl.
  intros H%(f_equal length).
  rewrite app_length /= in H.
  rewrite /encode_dir_ent in H.
  autorewrite with len in H.
  lia.
Qed.

Lemma not_elem_Forall {A} (l: list A) (x: A) :
  x ∉ l ↔ Forall (λ y, y ≠ x) l.
Proof.
  rewrite Forall_forall.
  intuition (subst; eauto).
Qed.

Lemma not_elem_fmap_Forall {A B} (l: list A) (x: B) (f: A → B) :
  x ∉ f <$> l ↔ Forall (λ y, f y ≠ x) l.
Proof.
  rewrite not_elem_Forall.
  rewrite Forall_fmap /compose; simpl.
  auto.
Qed.

Lemma dir_ents_ok_split es :
  dir_ents_ok es ↔
  Forall dir_ent_ok es ∧ NoDup (path <$> es).
Proof.
  split.
  - destruct 1; eauto.
  - intuition; eauto using dir_ents_ok.
Qed.

Lemma dir_ents_ok_cons_inv e es :
  dir_ents_ok (e :: es) ↔
  dir_ent_ok e ∧
  Forall (λ e', e'.(path) ≠ e.(path)) es ∧
  dir_ents_ok es.
Proof.
  rewrite !dir_ents_ok_split.
  rewrite -not_elem_fmap_Forall.
  rewrite Forall_cons.
  rewrite fmap_cons NoDup_cons.
  intuition eauto.
Qed.

Lemma encode_dir_ents_cons e es :
  encode_dir_ents (e :: es) = encode_dir_ent e ++ encode_dir_ents es.
Proof. reflexivity. Qed.

Lemma encode_dir_ents_inj es1 es2 :
  dir_ents_ok es1 →
  dir_ents_ok es2 →
  encode_dir_ents es1 = encode_dir_ents es2 →
  es1 = es2.
Proof.
  generalize dependent es2.
  induction es1 as [|e1 es1].
  - intros es2 _ _ Heq.
    destruct es2; simpl; [ done | ].
    symmetry in Heq.
    apply encode_dir_ents_cons_not_empty in Heq; contradiction.
  - destruct es2 as [|e2 es2].
    + intros _ _ Heq.
      apply encode_dir_ents_cons_not_empty in Heq; contradiction.
    + intros Hok1 Hok2 Heq.
      assert (dir_ents_ok es1) as Hok_es1.
      { apply dir_ents_ok_cons_inv in Hok1; intuition auto. }
      rewrite -> !encode_dir_ents_cons in *.
      apply dir_ents_ok_cons_inv in Hok1.
      apply dir_ents_ok_cons_inv in Hok2.
      apply app_inj_1 in Heq.
      2: {
        rewrite !encode_dir_ent_length; intuition eauto.
      }
      intuition.
      f_equal; eauto using encode_dir_ent_inj.
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

(* [own_directory'] is a low-level fact that is about the encoded directory,
while [own_directory] asserts ownership of the interpreted directory (a map from
paths to inodes) *)

Definition own_directory' l (es: list dir_ent): iProp Σ :=
  ∃ s, "Dents" ∷ l ↦[Directory :: "Dents"] (to_val s) ∗
       "Hdents" ∷ own_slice s (struct.t DirEnt) (DfracOwn 1) es ∗
       "%Hdir_wf" ∷ ⌜dir_ents_ok es⌝.

Theorem wp_Directory__Encode (l : loc) es :
  {{{ own_directory' l es }}}
    Directory__Encode #l
  {{{ (s : Slice.t), RET (to_val s);
      own_slice s byteT (DfracOwn 1) (encode_dir_ents es) ∗
      own_directory' l es
  }}}.
Proof.
  (*@ func (d *Directory) Encode() []byte {                                   @*)
  (*@     var bytes = []byte{}                                                @*)
  (*@     for _, dent := range d.Dents {                                      @*)
  (*@         bytes = append(bytes, dent.Encode()...)                         @*)
  (*@     }                                                                   @*)
  (*@     return bytes                                                        @*)
  (*@ }                                                                       @*)
Admitted.

Theorem wp_DecodeDirectory dq (s : Slice.t) es :
  {{{ own_slice_small s byteT dq (encode_dir_ents es) }}}
    DecodeDirectory (to_val s)
  {{{ l, RET #l; own_directory' l es }}}.
Proof.
  (*@ func DecodeDirectory(b []byte) Directory {                              @*)
  (*@     var dents = []DirEnt{}                                              @*)
  (*@     numEntries := uint64(len(b)) / DENT_SIZE                            @*)
  (*@     for i := uint64(0); i < numEntries; i++ {                           @*)
  (*@         ent := decodeDirEnt(b[i*DENT_SIZE : (i+1)*DENT_SIZE])           @*)
  (*@         if len(ent.Path) > 0 {                                          @*)
  (*@             dents = append(dents, ent)                                  @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@     return Directory{Dents: dents}                                      @*)
  (*@ }                                                                       @*)
Admitted.

Theorem wp_containsNull (s : string) :
  {{{ True }}}
    containsNull #s
  {{{ RET #(bool_decide (W8 0 ∈ string_to_bytes s)); True }}}.
Proof.
  (*@ func containsNull(s string) bool {                                      @*)
  (*@     // TODO: this is awkward due to Goose loop limitations              @*)
  (*@     var nullFound = false                                               @*)
  (*@     b := []byte(s)                                                      @*)
  (*@     for _, c := range b {                                               @*)
  (*@         if c == 0 {                                                     @*)
  (*@             nullFound = true                                            @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@     return nullFound                                                    @*)
  (*@ }                                                                       @*)
Admitted.

Definition own_directory l d: iProp Σ :=
  ∃ es, own_directory' l es ∗ ⌜interpret_dir_ents es = d⌝.

Theorem wp_Directory__Insert (l: loc) d (name : string) (inum : w64) :
  {{{ own_directory l d }}}
    Directory__Insert #l #name #inum
  {{{ RET #(); own_directory l (<[ string_to_bytes name := inum ]> d) }}}.
Proof.
  (*@ func (d *Directory) Insert(name string, inum simplefs.Inum) {           @*)
  (*@     // preconditions                                                    @*)
  (*@     machine.Assert(!containsNull(name))                                 @*)
  (*@     machine.Assert(uint64(len(name)) <= MAX_NAME_LEN)                   @*)
  (*@                                                                         @*)
  (*@     var done = false                                                    @*)
  (*@     for i := uint64(0); i < uint64(len(d.Dents)); i++ {                 @*)
  (*@         if d.Dents[i].Path == name {                                    @*)
  (*@             dent := &d.Dents[i]                                         @*)
  (*@             dent.Inum = inum                                            @*)
  (*@             done = true                                                 @*)
  (*@             break                                                       @*)
  (*@         } else {                                                        @*)
  (*@             continue                                                    @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@     if done {                                                           @*)
  (*@         return                                                          @*)
  (*@     }                                                                   @*)
  (*@     // path not in directory                                            @*)
  (*@                                                                         @*)
  (*@     d.Dents = append(d.Dents, DirEnt{Path: name, Inum: inum})           @*)
  (*@ }                                                                       @*)

  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "(%es & Hd & %Hint)"; subst d.
Admitted.

Theorem wp_Directory__Remove (l: loc) d (name : string) :
  {{{ own_directory l d }}}
    Directory__Remove #l #name
  {{{ RET #(); own_directory l (map_delete (string_to_bytes name) d) }}}.
Proof.
  (*@ func (d *Directory) Remove(name string) {                               @*)
  (*@     // TODO: not a range loop due to goose limitations                  @*)
  (*@     for i := uint64(0); i < uint64(len(d.Dents)); i++ {                 @*)
  (*@         if d.Dents[i].Path == name {                                    @*)
  (*@             d.Dents = append(d.Dents[:i], d.Dents[i+1:]...)             @*)
  (*@             break                                                       @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@ }                                                                       @*)
Admitted.

Theorem wp_Directory__Lookup (l : loc) d (name : string) :
  {{{ own_directory l d }}}
    Directory__Lookup #l #name
  {{{ (inum: w64) (ok : bool), RET (#inum, #ok); own_directory l d ∗
      ⌜if ok then d !! string_to_bytes name = Some inum else
                  d !! string_to_bytes name = None⌝
 }}}.
Proof.
  (*@ func (d *Directory) Lookup(name string) (simplefs.Inum, bool) {         @*)
  (*@     // TODO: awkward due to goose                                       @*)
  (*@     var inum = simplefs.Inum(0)                                         @*)
  (*@     var found = false                                                   @*)
  (*@     for _, dent := range d.Dents {                                      @*)
  (*@         if !found && dent.Path == name {                                @*)
  (*@             inum = dent.Inum                                            @*)
  (*@             found = true                                                @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@     return inum, found                                                  @*)
  (*@ }                                                                       @*)
Admitted.

Theorem wp_Directory__Contains (l: loc) d (name : string) :
  {{{ own_directory l d }}}
    Directory__Contains #l #name
  {{{ RET #(bool_decide (is_Some (d !! string_to_bytes name)));
      own_directory l d }}}.
Proof.
  (*@ func (d *Directory) Contains(name string) bool {                        @*)
  (*@     _, ok := d.Lookup(name)                                             @*)
  (*@     return ok                                                           @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "Hd".
  wp_lam. wp_pures.
  wp_apply (wp_Directory__Lookup with "Hd").
  iIntros (i ok) "[Hd %Hok]".
  wp_pures.
  iModIntro.
  iDestruct ("HΦ" with "Hd") as "HΦ".
  iExactEq "HΦ".
  f_equal.
  f_equal.
  destruct ok.
  - rewrite Hok //.
  - rewrite Hok //.
Qed.

Lemma gmap_not_empty {K} `{Countable K} {V} (m: gmap K V) (k: K) :
  is_Some (m !! k) →
  m ≠ ∅.
Proof.
  destruct 1 as [v Heq].
  intros ->.
  rewrite lookup_empty in Heq.
  congruence.
Qed.

Theorem wp_Directory__IsEmpty (l : loc) d :
  {{{ own_directory l d }}}
    Directory__IsEmpty #l
  {{{RET #(bool_decide (d = ∅)); own_directory l d }}}.
Proof.
  (*@ func (d *Directory) IsEmpty() bool {                                    @*)
  (*@     return len(d.Dents) == 0                                            @*)
  (*@ }                                                                       @*)
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "(%es & Hd & %Hint)"; subst d.
  wp_rec. wp_pures.
  iNamed "Hd".
  wp_loadField.
  iDestruct (own_slice_sz with "Hdents") as %Hsz.
  wp_apply wp_slice_len.
  wp_pures.
  iModIntro.
  iDestruct ("HΦ" with "[$Dents $Hdents]") as "HΦ".
  { eauto. }
  iExactEq "HΦ".
  f_equal. f_equal.
  destruct es.
  - simpl.
    rewrite !bool_decide_eq_true_2 //.
    f_equal.
    f_equal.
    simpl in Hsz.
    word.
  - simpl in Hsz.
    rewrite !bool_decide_eq_false_2 //.
    + intros H.
      inv H as [H']. inv H' as [H''].
      apply (f_equal uint.Z) in H''.
      move: H''. word.
    + apply (gmap_not_empty _ d.(path)).
      rewrite /=.
      apply lookup_insert_is_Some; auto.
Qed.

End proof.

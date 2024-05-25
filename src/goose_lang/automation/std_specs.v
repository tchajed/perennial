From Perennial.goose_lang.automation Require Import goose_lang_auto.
From Perennial.goose_lang.lib Require Import
  struct typed_mem lock into_val slice typed_slice
  string
  control.impl control
  loop.impl
  typed_map
.
From Perennial.program_proof Require Import std_proof.
From Perennial.Helpers Require Import dfrac.

#[global] Opaque NewSlice SliceGet SliceAppend SliceAppendSlice.
#[global] Opaque NewMap impl.MapGet impl.MapInsert impl.MapDelete impl.MapLen.
#[global] Opaque lock.new lock.acquire lock.release.

Section proofs.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  #[global] Instance new_lock_spec :
    SPEC {{ emp }} lock.new #() {{ (l: loc), RET #l; is_free_lock l }}.
  Proof.
    iSteps.
    wp_apply wp_new_free_lock; iSteps.
  Qed.

  #[global] Instance alloc_lock_hint E (lk: loc) N R :
    HINT (is_free_lock lk) ✱ [-; ▷ R] ⊫ [fupd E E]; is_lock N (#lk) R ✱ [emp].
  Proof.
    iSteps.
    iMod (alloc_lock with "[$] [$]") as "Hlock".
    iSteps.
  Qed.

  #[global] Instance lock_acquire_spec lk N R :
    SPEC ⟨⊤⟩ {{ is_lock N lk R }} lock.acquire lk {{ RET #(); locked lk ∗ R }}.
  Proof.
    iStep.
    wp_apply (acquire_spec' with "[$]"); auto.
  Qed.

  #[global] Instance lock_release_spec lk N R :
    SPEC {{ is_lock N lk R ∗ locked lk ∗ R }} lock.release lk {{ RET #(); emp }}.
  Proof.
    iStep as "Hlock Hlocked HR".
    wp_apply (release_spec' with "[$Hlock $Hlocked $HR]"); auto.
  Qed.

  Section slice_specs.

  Context `{!IntoVal V}.
  Implicit Types (s: Slice.t) (vs: list V).

  #[global] Instance NewSlice_spec_0 `{!IntoValForType V t} E :
    SPEC ⟨E⟩
        {{ emp }}
        NewSlice t #(W64 0)
        {{ s, RET (slice_val s); own_slice s t 1 ([]: list V) }} | 10.
  Proof.
    iSteps.
    wp_apply wp_NewSlice.
    iSteps.
  Qed.

  #[global] Instance NewSlice_spec `{!IntoValForType V t} E (sz: w64) :
    SPEC ⟨E⟩
        {{ emp }}
        NewSlice t #sz
        {{ s, RET (slice_val s); own_slice s t 1 (replicate (uint.nat sz) (IntoVal_def V)) }} | 15.
  Proof.
    iSteps.
    wp_apply wp_NewSlice.
    iSteps.
  Qed.

  (* TODO: is this really a good idea? shouldn't we take the slice resource and
  not directly expose slice properties? *)
  #[global] Instance slice_len_spec s E :
    SPEC ⟨E⟩ {{ emp }} slice.len s {{ RET #s.(Slice.sz); emp }}.
  Proof. iStep. wp_apply wp_slice_len. iSteps. Qed.

  #[global] Instance slice_len_hint s t q vs :
   MergablePersist (own_slice_small s t q vs)
   (λ p Pin Pout,
     TCAnd (TCEq Pin (ε₀)%I)
           (TCEq Pout ⌜length vs = uint.nat s.(Slice.sz)⌝)
   )%I.
  Proof.
    move => p?? [-> ->].
    rewrite own_slice_small_sz //.
    iIntros "[% _] !> //".
  Qed.

  #[global] Instance own_slice_small_access_hint s t q vs :
    HINT (own_slice s t q vs) ✱ [-; emp] ⊫ [id]; (own_slice_small s t q vs) ✱ [own_slice_cap s t].
  Proof.
    iSteps.
  Qed.

  #[global] Instance own_slice_merge_hint s t q vs :
    HINT1 (own_slice_small s t q vs) ✱ [own_slice_cap s t] ⊫ [id]; (own_slice s t q vs).
  Proof. iSteps. Qed.

  #[global] Instance SliceGet_spec s t q vs (i: w64) :
    SPEC (v: V),
      {{ own_slice_small s t q vs ∗ ⌜vs !! uint.nat i = Some v⌝ }}
      SliceGet t s #i
      {{ RET (to_val v); own_slice_small s t q vs }}.
  Proof.
    iSteps.
    wp_apply (wp_SliceGet with "[-]").
    { iSteps. }
    iSteps.
  Qed.

  #[global] Instance SliceAppend_spec `{!IntoValForType V t} s vs xx :
    SPEC (x: V),
      {{ own_slice s t 1 vs ∗ ⌜xx = to_val x⌝ }}
      SliceAppend t s xx
    {{ s', RET s'; own_slice s' t 1 (vs ++ [x]) }}.
  Proof.
    iSteps.
    wp_apply (wp_SliceAppend with "[$]").
    iSteps.
  Qed.

  #[global] Instance SliceAppendSlice_spec `{!IntoValForType V t} s vs s' q vs' :
    SPEC {{ ⌜has_zero t⌝ ∗ own_slice s t 1 vs ∗ own_slice_small s' t q vs' }}
      SliceAppendSlice t s s'
    {{ s'', RET s''; own_slice s'' t 1 (vs ++ vs') ∗ own_slice_small s' t q vs' }}.
  Proof.
    iSteps.
    wp_apply (wp_SliceAppendSlice with "[$]"); [ done.. | ].
    iSteps.
  Qed.

  End slice_specs.

  #[global] Instance StringToBytes_spec (s: string) :
   SPEC
     {{ emp }}
      impl.StringToBytes #(str s)
    {{ sl, RET (slice_val sl); own_slice sl byteT 1 (string_to_bytes s) }}.
  Proof.
    iStep. wp_apply wp_StringToBytes. iSteps.
  Qed.

  #[global] Instance StringFromBytes_spec sl :
   SPEC q (bs: list w8),
     {{ own_slice_small sl byteT q bs }}
      impl.StringFromBytes sl
    {{ RET #(str bytes_to_string bs); own_slice_small sl byteT q bs }}.
  Proof.
    iStep as (q). iStep. iStep. wp_apply (wp_StringFromBytes with "[$]"). iSteps.
  Qed.

  #[global] Instance SumAssumeNoOverflow_spec (x y : u64) :
    SPEC
      {{ emp }}
        std.SumAssumeNoOverflow #x #y
      {{ RET #(LitInt $ word.add x y); ⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ }}.
  Proof.
    iStep. (* Careful not to call [iSteps], as this would unfold the function *)
    wp_apply wp_SumAssumeNoOverflow. iIntros (Hoverflow) "!% //".
  Qed.

  #[global] Instance Assume_spec E (cond: bool) :
    SPEC ⟨E⟩
      {{ emp }}
      Assume #cond
      {{ RET #(); ⌜cond = true⌝ }}.
  Proof. iSteps. wp_apply wp_Assume; auto. Qed.

  #[global] Instance Assert_spec E (cond: bool) :
    SPEC ⟨E⟩
      {{ ⌜cond = true⌝ }}
      Assert #cond
      {{ RET #(); emp }}.
  Proof. iSteps. wp_apply wp_Assert; auto. Qed.

  #[global] Instance Exit_spec E (v: val) :
    SPEC ⟨E⟩
        {{ emp }}
        Exit v
        {{ RET #(); False }}.
  Proof. iSteps. wp_apply wp_Exit; auto. Qed.


  Section map_specs.

  #[global] Instance NewMap_spec
    `{!IntoVal V}
    `{!IntoVal K, !EqDecision K, !Countable K}
    `{!IntoValForType V vt} `{!IntoValForType K kt}
    (* the ordering here is crucial! [IntoValComparable] requires K to be resolved,
      which is what the [IntoValForType] typeclass does, so that one should come first. *)
    `{!IntoValComparable K} E :
    SPEC ⟨E⟩
    {{ emp }}
      NewMap kt vt #()
    {{ mref, RET #mref;
        own_map mref 1 (∅: gmap K V) }}.
  Proof. iSteps. wp_apply wp_NewMap. iSteps. Qed.

  #[global] Instance MapInsert_spec E mref kk vv :
    SPEC ⟨E⟩ `(!IntoVal K) `(Countable K) `(!IntoVal V)
      k v' (m: gmap K V),
    {{ own_map mref 1 m ∗ ⌜kk = to_val k⌝ ∗ ⌜vv = to_val v'⌝ }}
      impl.MapInsert #mref kk vv
    {{ RET #(); own_map mref 1 (map_insert m k v') }}.
  Proof.
    iSteps. wp_apply (wp_MapInsert with "[$]"); auto.
  Qed.

  #[global] Instance MapGet_spec E mref kk :
      SPEC ⟨E⟩ `(!IntoVal K) `(Countable K)
        `(!IntoVal V)
        q (m: gmap K V) k,
    {{ own_map mref q m ∗ ⌜kk = to_val k⌝ ∗ ⌜IntoValComparable K⌝ }}
      impl.MapGet #mref kk
    {{ (v: V) ok, RET (to_val v, #ok)%V;
        ⌜map_get m k = (v, ok)⌝ ∗
        own_map mref q m }}.
  Proof.
    iSteps. wp_apply (wp_MapGet with "[$]"). iSteps.
  Qed.

  #[global] Instance MapDelete_spec E mref kk :
      SPEC ⟨E⟩ `(!IntoVal K) `(Countable K)
        `(!IntoVal V)
      (m: gmap K V) k,
    {{ own_map mref 1 m ∗ ⌜kk = to_val k⌝ ∗ ⌜IntoValComparable K⌝ }}
      impl.MapDelete #mref kk
    {{ RET #(); own_map mref 1 (map_del m k) }}.
  Proof.
    iSteps. wp_apply (wp_MapDelete with "[$]"). iSteps.
  Qed.

  End map_specs.

End proofs.

#[global] Opaque typed_slice.own_slice.
#[global] Opaque typed_slice.own_slice_small.
#[global] Opaque own_slice_cap.
#[global] Opaque impl.StringFromBytes.
#[global] Opaque impl.StringToBytes.
#[global] Opaque std.SumAssumeNoOverflow.

#[global] Opaque loop.impl.For loop.impl.Loop.

Hint Extern 4 (IntoValComparable _) => tc_solve : solve_pure_add.

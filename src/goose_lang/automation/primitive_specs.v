From Perennial.goose_lang Require Import automation.goose_lang_auto.
From diaframe.lib Require Import iris_hints.
From Perennial.goose_lang Require Import struct.
From Perennial.goose_lang Require Import typed_mem.
From Perennial.goose_lang Require Import lock.

Set Default Proof Using "Type".

Section goose_lang_instances.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Open Scope expr_scope.

  Global Instance ref_zero_spec t Φ :
    HINT1 ε₀ ✱
      [⌜has_zero t⌝ ∗ ▷ (∀ (l:loc), l ↦[t] (zero_val t) -∗ Φ #l)]
      ⊫ [id]; WP (ref (zero_val t)) {{ Φ }}.
  Proof.
    iSteps.
    wp_apply wp_ref_of_zero; auto.
  Qed.

  Global Instance load_primitive_spec E l :
    SPEC ⟨E⟩ v q, {{ ▷ l ↦{q} v }} ! #l {{ RET v; l ↦{q} v }}.
  Proof.
    iSteps as (v q) "Hl".
    wp_apply (wp_load with "Hl").
    iSteps.
  Qed.

  Global Instance load_at_spec l E t :
    SPEC ⟨E⟩ v q, {{ ▷ l ↦[t]{q} v }} ![t] #l {{ RET v; l ↦[t]{q} v }}.
  Proof.
    iSteps as (v q) "Hl".
    wp_apply (wp_LoadAt with "Hl").
    iSteps.
  Qed.

  Global Instance alloc_spec E e v t:
    IntoVal e v →
    val_ty v t →
    SPEC ⟨E⟩ {{ True }} ref_to t e {{ l, RET #l; l ↦[t] v }} | 20.
  Proof.
    move => <- Hty.
    iStep.
    wp_apply wp_ref_to => //.
    iSteps.
  Qed.

  Global Instance store_primitive_spec l v' E :
    SPEC ⟨E⟩ v, {{ ▷ l ↦ v }} #l <- v' {{ RET #(); l ↦ v' }}.
  Proof.
    iSteps as (v) "Hl".
    iApply (wp_store with "Hl").
    iSteps.
  Qed.

  Global Instance store_at_spec l t v' E :
    val_ty v' t →
    SPEC ⟨E⟩ v, {{ ▷ l ↦[t] v }} #l <-[t] v' {{ RET #(); l ↦[t] v' }}.
  Proof.
    move => Hty.
    iSteps as (v) "Hl".
    wp_apply (wp_StoreAt with "Hl"); first done.
    iSteps.
  Qed.

  Global Instance loadField_spec l q d f E :
    SPEC ⟨E⟩ v, {{ ▷ l ↦[d :: f]{q} v }}
                  struct.loadF d f #l
                {{ RET v; l ↦[d :: f]{q} v }}.
  Proof.
    iSteps as (v) "Hx".
    wp_apply (wp_loadField with "Hx"); auto.
  Qed.

  Global Instance storeField_spec l d f E fv' :
    SPEC ⟨E⟩ fv, {{ ⌜val_ty fv' (field_ty d f)⌝ ∗ ▷ l ↦[d :: f] fv }}
                  struct.storeF d f #l fv'
                {{ RET #(); l ↦[d :: f] fv' }}.
  Proof.
    iSteps as (v' ?) "Hx".
    wp_apply (wp_storeField with "Hx"); auto.
  Qed.

  Global Instance loadField_ro_spec l d f E :
    SPEC ⟨E⟩ v, {{ readonly (struct_field_pointsto l 1%Qp d f v) }}
                  struct.loadF d f #l
                {{ RET v; emp }}.
  Proof.
    iStep.
    iStep.
    wp_apply (wp_loadField_ro with "[$]"). auto.
  Qed.

  Global Instance lock_acquire_spec lk N R :
    SPEC {{ is_lock N lk R }} lock.acquire lk {{ RET #(); locked lk ∗ R }}.
  Proof.
    iStep.
    wp_apply (acquire_spec' with "[$]"); auto.
  Qed.

  Global Instance lock_release_spec lk N R :
    SPEC {{ is_lock N lk R ∗ locked lk ∗ R }} lock.release lk {{ RET #(); emp }}.
  Proof.
    iStep as "Hlock Hlocked HR".
    wp_apply (release_spec' with "[$Hlock $Hlocked $HR]"); auto.
  Qed.

End goose_lang_instances.

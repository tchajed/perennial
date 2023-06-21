From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv lockservice bank.
From Perennial.program_proof.memkv Require Export common_proof memkv_clerk_proof lockservice_proof.


Record bank_names := BankNames {
  bank_ls_names : gname;
  bank_ks_names : gname;
  bank_logBalGN : gname (* Logical balances of accounts; must match the physical balance by the time you give up the lock *)
}.

Definition kv_gn γ := γ.(bank_ks_names).
Definition lk_gn γ := γ.(bank_ls_names).
Definition log_gn γ := γ.(bank_logBalGN).

Add Ring u64ring : (word.ring_theory (word := u64_instance.u64)).


Section bank_defs.

Context `{!invGS Σ, !kvMapG Σ, mapG Σ u64 u64}.

Definition bankPs γ := λ k, (∃ vd v, ⌜ has_encoding_Uint64 vd v ⌝ ∗ kvptsto (kv_gn γ) k vd ∗ k [[log_gn γ]]↦v)%I.

Definition bankN := nroot .@ "grove_bank_of_boston".
Definition lockN : namespace := nroot.@"grove_bank_of_boston_vault".

Definition bal_total : u64 := 1000.

Context (init_flag: u64). (* Account names for bank *)

Definition map_total (m : gmap u64 u64) : u64 :=
  map_fold (λ k v tot, word.add tot v) 0 m.

Lemma map_total_insert m k v :
  m !! k = None ->
  map_total (<[k := v]> m) = word.add (map_total m) v.
Proof.
  intro Hnone.
  rewrite /map_total map_fold_insert_L; eauto.
  intros; ring.
Qed.

Lemma map_total_insert_2 m k v :
  m !! k = Some v ->
  map_total m = word.add (map_total (delete k m)) v.
Proof.
  intro Hsome.
  erewrite <- (map_total_insert _ k).
  2: rewrite lookup_delete //.
  rewrite insert_delete //.
Qed.

Lemma map_total_empty :
  map_total ∅ = 0.
Proof.
  reflexivity.
Qed.

Lemma map_total_dom_empty m :
  dom m = ∅ ->
  map_total m = 0.
Proof.
  intros Hd.
  apply dom_empty_inv_L in Hd; subst.
  reflexivity.
Qed.

Lemma map_total_update : ∀ m k v v',
  m !! k = Some v ->
  map_total (<[k := v']> m) = word.add (word.sub (map_total m) v) v'.
Proof.
  induction m using map_ind.
  - intros k v v'. rewrite lookup_empty. congruence.
  - intros k v v' Hlookup.
    destruct (decide (k = i)); subst.
    + rewrite insert_insert.
      rewrite lookup_insert in Hlookup; inversion Hlookup; subst.
      rewrite map_total_insert //.
      rewrite map_total_insert //.
      ring_simplify.
      done.
    + rewrite insert_commute //.
      rewrite lookup_insert_ne // in Hlookup.
      rewrite (map_total_insert _ i).
      2: { rewrite lookup_insert_ne //. }
      rewrite (map_total_insert _ i) //.
      erewrite IHm; last by eauto.
      ring_simplify.
      done.
Qed.

Definition bank_inv γ (accts : gset u64) : iProp Σ :=
  ∃ (m:gmap u64 u64),
    "HlogBalCtx" ∷ map_ctx (log_gn γ) 1 m ∗
    "%" ∷ ⌜map_total m = bal_total⌝ ∗
    "%" ∷ ⌜dom m = accts⌝
  .

Definition init_lock_inv γlock γkv accts : iProp Σ :=
  (* Uninit case *)
  (kvptsto γkv init_flag [] ∗
   [∗ set] acc ∈ accts, kvptsto γkv acc [] ∗ kvptsto γlock acc []
  ) ∨
  (* Already init case *)
  (∃ γlog,
   let γ := {| bank_ls_names := γlock; bank_ks_names := γkv; bank_logBalGN := γlog |} in
   kvptsto γkv init_flag [U8 0] ∗ inv bankN (bank_inv γ accts) ∗
    [∗ set] acc ∈ accts, is_lock lockN γlock acc (bankPs γ acc)).

End bank_defs.

Section bank_proof.
Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), !erpcG Σ, !urpcregG Σ, !kvMapG Σ, mapG Σ u64 u64}.

Context (init_flag: u64). (* Account names for bank *)


Definition own_bank_clerk γ (bank_ck:loc) (accts : gset u64) : iProp Σ :=
  ∃ (lck kck : loc) (accts_s : Slice.t) (accts_l : list u64),
  "%" ∷ ⌜Permutation (elements accts) (accts_l)⌝ ∗
  "Hlck_own" ∷ own_LockClerk lck γ.(bank_ls_names) ∗
  "Hkck_own" ∷ own_SeqKVClerk kck γ.(bank_ks_names) ∗

  "Hkck" ∷ bank_ck ↦[BankClerk :: "kvck"] #kck ∗
  "Hlck" ∷ bank_ck ↦[BankClerk :: "lck"] #lck ∗
  "Haccts" ∷ bank_ck ↦[BankClerk :: "accts"] (slice_val accts_s) ∗
  "Haccts_slice" ∷ own_slice_small accts_s uint64T 1 accts_l ∗

  "#Haccts_is_lock" ∷ [∗ list] acc ∈ accts_l, is_lock lockN γ.(bank_ls_names) acc (bankPs γ acc)
.


Lemma acquire_two_spec (lck :loc) (ln1 ln2:u64) γ:
{{{
     own_LockClerk lck γ.(bank_ls_names) ∗
     is_lock lockN γ.(bank_ls_names) ln1 (bankPs γ ln1) ∗
     is_lock lockN γ.(bank_ls_names) ln2 (bankPs γ ln2)
}}}
  acquire_two #lck #ln1 #ln2
{{{
     RET #(); own_LockClerk lck γ.(bank_ls_names) ∗
     bankPs γ ln1 ∗
     bankPs γ ln2
}}}.
Proof.
  iIntros (Φ) "(Hlck & #Hln1_islock & #Hln2_islock) Hpost".
  wp_lam.
  wp_pures.
  destruct bool_decide; wp_pures.
  {
    wp_apply (wp_LockClerk__Lock with "[$Hlck $Hln1_islock]").
    iIntros "[Hlck HP1]".
    wp_pures.
    wp_apply (wp_LockClerk__Lock with "[$Hlck $Hln2_islock]").
    iIntros "[Hlck HP2]".
    wp_pures.
    iApply "Hpost". by iFrame.
  }
  {
    wp_apply (wp_LockClerk__Lock with "[$Hlck $Hln2_islock]").
    iIntros "[Hlck HP2]".
    wp_pures.
    wp_apply (wp_LockClerk__Lock with "[$Hlck $Hln1_islock]").
    iIntros "[Hlck HP1]".
    wp_pures.
    iApply "Hpost". by iFrame.
  }
Qed.

Lemma release_two_spec (lck :loc) (ln1 ln2:u64) γ:
{{{
     own_LockClerk lck γ.(bank_ls_names) ∗
     is_lock lockN γ.(bank_ls_names) ln1 (bankPs γ ln1) ∗
     is_lock lockN γ.(bank_ls_names) ln2 (bankPs γ ln2) ∗
     bankPs γ ln1 ∗
     bankPs γ ln2
}}}
  release_two #lck #ln1 #ln2
{{{
     RET #(); own_LockClerk lck γ.(bank_ls_names)
}}}.
Proof.
  iIntros (Φ) "(Hlck & #Hln1_islock & #Hln2_islock & HP1 & HP2) Hpost".
  wp_lam.
  wp_pures.
  wp_apply (wp_LockClerk__Unlock with "[$Hlck $Hln1_islock $HP1]").
  iIntros "Hlck".
  wp_pures.
  wp_apply (wp_LockClerk__Unlock with "[$Hlck $Hln2_islock $HP2]").
  iIntros "Hlck".
  wp_pures.
  iApply "Hpost"; by iFrame.
Qed.

Lemma Bank__transfer_internal_spec (bck:loc) src dst (amount:u64) γ accts :
{{{
     inv bankN (bank_inv γ accts) ∗
     own_bank_clerk γ bck accts ∗
     is_lock lockN γ.(bank_ls_names) src (bankPs γ src) ∗
     is_lock lockN γ.(bank_ls_names) dst (bankPs γ dst) ∗
     ⌜src ≠ dst⌝
}}}
  BankClerk__transfer_internal #bck #src #dst #amount
{{{
     RET #();
     own_bank_clerk γ bck accts
}}}.
Proof.
  iIntros (Φ) "(#Hbinv & Hpre & #Hsrc & #Hdst & %) Hpost".
  iNamed "Hpre".
  wp_lam. wp_pures.
  wp_loadField.
  wp_apply (acquire_two_spec with "[$Hlck_own]"); first iFrame "#".
  iIntros "(Hlck_own & Hacc1_unlocked & Hacc2_unlocked)".
  iDestruct "Hacc1_unlocked" as (bytes1 bal1 Henc1) "(Hacc1_phys & Hacc1_log)".
  iDestruct "Hacc2_unlocked" as (bytes2 bal2 Henc2) "(Hacc2_phys & Hacc2_log)".
  wp_pures.
  wp_loadField.
  wp_apply (wp_SeqKVClerk__Get with "[$Hkck_own]").
  iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
  iExists _. iFrame "Hacc1_phys".
  iIntros "Hacc1_phys". iMod ("Hclo") as "_". iModIntro.
  iIntros (v_bal1_g qp) "(Hkck_own&Hbal1_get)".
  wp_apply (wp_DecodeUint64' with "[$Hbal1_get //]").
  wp_pures.
  destruct bool_decide eqn:HenoughBalance; wp_pures.
  - (* Safe to do the transfer *)
    wp_apply (wp_EncodeUint64).
    iIntros (v_bal1_g' bytes1') "(Hsl&%)".
    wp_loadField.
    iDestruct (own_slice_to_small with "Hsl") as "Hsl".
    iMod (readonly_alloc_1 with "Hsl") as "#Hsl".
    wp_apply (wp_SeqKVClerk__Put with "[$Hkck_own]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc1_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkck_own".
    wp_pures.
    wp_loadField.

    wp_apply (wp_SeqKVClerk__Get with "[$Hkck_own]").
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame "Hacc2_phys".
    iIntros "Hacc2_phys". iMod ("Hclo") as "_". iModIntro.
    iIntros (v_bal2_g qp') "(Hkck_own&Hbal2_get)".
    wp_apply (wp_DecodeUint64' with "[$Hbal2_get //]").
    wp_pures.

    wp_apply (wp_EncodeUint64).
    iIntros (v_bal2_g' bytes2') "(Hsl2&%)".

    wp_loadField.
    iDestruct (own_slice_to_small with "Hsl2") as "Hsl2".
    iMod (readonly_alloc_1 with "Hsl2") as "#Hsl2".
    wp_apply (wp_SeqKVClerk__Put with "[$Hkck_own]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc2_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkck_own".
    wp_pures.
    wp_loadField.

    iApply fupd_wp.
    iInv bankN as ">HbankInv" "HbankInvClose".
    iNamed "HbankInv".
    iDestruct (map_valid with "[$] Hacc1_log") as "%Hval1".
    iDestruct (map_valid with "[$] Hacc2_log") as "%Hval2".
    iMod (map_update src _ (word.sub bal1 amount) with "HlogBalCtx Hacc1_log") as "[HlogBalCtx Hacc1_log]".
    iMod (map_update dst _ (word.add bal2 amount) with "HlogBalCtx Hacc2_log") as "[HlogBalCtx Hacc2_log]".
    iMod ("HbankInvClose" with "[HlogBalCtx]") as "_".
    { iNext. iExists _. iSplitL "HlogBalCtx"; first by iFrame.
      iSplit; iPureIntro.
      + erewrite map_total_update; last by rewrite lookup_insert_ne //.
        erewrite map_total_update; last by eauto.
        ring_simplify. eauto.
      + rewrite dom_insert_lookup_L.
        2: { rewrite lookup_insert_ne //. }
        rewrite dom_insert_lookup_L //.
    }
    iModIntro.
    wp_apply (release_two_spec with "[$Hlck_own Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]").
    { iFrame "#". iSplitL "Hacc1_phys Hacc1_log"; iExists _, _; iFrame; eauto. }
    iIntros "Hlck_own".
    wp_pures. iApply "Hpost".
    iExists _, _, _, _; by iFrame "∗ # %".
  - (* Don't do the transfer *)
    wp_loadField. wp_apply (release_two_spec with "[$Hlck_own Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]").
    { iFrame "#". iSplitL "Hacc1_phys Hacc1_log"; iExists _, _; iFrame; eauto. }
    iIntros "Hlck_own".
    wp_pures. iApply "Hpost".
    iExists _, _, _, _; by iFrame "∗ # %".
Qed.

Lemma Bank__SimpleTransfer_spec (bck:loc) γ accts :
{{{
     inv bankN (bank_inv γ accts) ∗
     own_bank_clerk γ bck accts
}}}
  BankClerk__SimpleTransfer #bck
{{{
     RET #();
     own_bank_clerk γ bck accts
}}}.
Proof.
  iIntros (Φ) "[#Hbinv Hpre] Hpost".
  wp_call.
  wp_forBreak_cond.
  wp_pures.
  wp_apply wp_RandomUint64. iIntros (src) "_".
  wp_apply wp_RandomUint64. iIntros (dst) "_".
  wp_apply wp_RandomUint64. iIntros (amount) "_".

  iNamed "Hpre".

  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  destruct (bool_decide (int.Z src < int.Z accts_s.(Slice.sz))) eqn:Hsrc.
  2: {
    wp_pures. iModIntro. iLeft. iFrame. iSplit; first by done.
    iExists _, _, _, _. iFrame "∗%#".
  }

  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  destruct (bool_decide (int.Z dst < int.Z accts_s.(Slice.sz))) eqn:Hdst.
  2: {
    wp_pures. iModIntro. iLeft. iFrame. iSplit; first by done.
    iExists _, _, _, _. iFrame "∗%#".
  }

  wp_if_destruct.
  2: {
    wp_pures. iModIntro. iLeft. iFrame. iSplit; first by done.
    iExists _, _, _, _. iFrame "∗%#".
  }

  iDestruct (slice.own_slice_small_sz with "Haccts_slice") as %Hslicelen.
  rewrite list_untype_length in Hslicelen.

  destruct (list_lookup_lt _ accts_l (int.nat src)) as (asrc & Hasrc); first by word.
  destruct (list_lookup_lt _ accts_l (int.nat dst)) as (adst & Hadst); first by word.

  wp_loadField.
  wp_apply (wp_SliceGet with "[$Haccts_slice]"); first by eauto.
  iIntros "Haccts_slice".

  wp_loadField.
  wp_apply (wp_SliceGet with "[$Haccts_slice]"); first by eauto.
  iIntros "Haccts_slice".

  iDestruct (big_sepL_lookup _ _ _ asrc with "Haccts_is_lock") as "#Hasrc_is_lock"; first by eauto.
  iDestruct (big_sepL_lookup _ _ _ adst with "Haccts_is_lock") as "#Hadst_is_lock"; first by eauto.

  wp_apply (Bank__transfer_internal_spec with "[-Hpost]").
  { iFrame "#". iSplitL.
    - iExists _, _, _, _. iFrame "∗%#".
    - iPureIntro.
      intro Hc; subst.
      assert (NoDup accts_l) as Hnodup.
      { rewrite -H1. apply NoDup_elements. }
      epose proof (NoDup_lookup _ _ _ _ Hnodup Hasrc Hadst).
      apply Heqb. f_equal. f_equal. word.
  }

  iIntros "Hpre".
  wp_pures.
  iModIntro.
  iLeft.
  iFrame. done.
Qed.

Lemma Bank__get_total_spec (bck:loc) γ accts :
{{{
     inv bankN (bank_inv γ accts) ∗
     own_bank_clerk γ bck accts
}}}
  BankClerk__get_total #bck
{{{
     RET #bal_total;
     own_bank_clerk γ bck accts
}}}.
Proof.
  iIntros (Φ) "[#Hbinv Hpre] Hpost".
  wp_call.
  wp_apply wp_ref_of_zero; first by done.
  iIntros (sum) "Hsum".

  iNamed "Hpre".
  wp_loadField.
  wp_apply (wp_forSlicePrefix (λ done todo,
    ∃ locked,
      "Hlck" ∷ bck ↦[BankClerk :: "lck"] #lck ∗
      "Hlck_own" ∷ own_LockClerk lck γ.(bank_ls_names) ∗
      "Hkck" ∷ bck ↦[BankClerk :: "kvck"] #kck ∗
      "Hkck_own" ∷ own_SeqKVClerk kck γ.(bank_ks_names) ∗
      "Hsum" ∷ sum ↦[uint64T] #(map_total locked) ∗
      "Hml" ∷ [∗ maplist] acc ↦ bal;id ∈ locked;done,
        is_lock lockN γ.(bank_ls_names) acc (bankPs γ acc) ∗
        ⌜ acc = id ⌝ ∗
        (∃ (vd : list u8), ⌜has_encoding_Uint64 vd bal⌝ ∗ kvptsto (kv_gn γ) acc vd ∗ acc [[log_gn γ]]↦ bal))%I
    with "[] [$Haccts_slice Hsum $Hlck $Hlck_own $Hkck $Hkck_own]").
  2: {
    iExists ∅. rewrite map_total_empty. iFrame.
    iApply big_sepML_empty.
  }

  {
    iIntros (i x done todo) "%".
    iIntros (Ψ). iModIntro. iIntros "Hpre HΨ".
    iNamed "Hpre".

    wp_loadField.
    iDestruct (big_sepL_elem_of _ _ x with "Haccts_is_lock") as "#Hx_is_lock".
    { rewrite -H2. set_solver. }
    wp_apply (wp_LockClerk__Lock with "[$Hlck_own $Hx_is_lock]").
    iIntros "[Hlck_own Hx]".
    iDestruct "Hx" as (x_vd x_bal) "[%Hx_enc [Hx_kv Hx_log]]".

    wp_load.
    wp_loadField.
    wp_apply (wp_SeqKVClerk__Get with "[$Hkck_own]").

    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame "Hx_kv".
    iIntros "Hx_kv". iMod ("Hclo") as "_". iModIntro.
    iIntros (v_bal_x_g qp1) "(Hkck_own&Hbal_x_get)".
    wp_apply (wp_DecodeUint64' with "[$Hbal_x_get //]").

    wp_pures.
    wp_store.
    iModIntro.
    iApply "HΨ".
    iExists (<[x := x_bal]> locked).
    iFrame.

    destruct (decide (x ∈ dom locked)).
    {
      apply elem_of_dom in e. destruct e as (?&e).
      iDestruct (big_sepML_lookup_m_acc _ _ _ _ _ e with "Hml") as (??) "(%He & Hml & _)".
      iDestruct "Hml" as "(_ & %Heq & _)".
      subst. exfalso.
      assert (NoDup (done ++ lv :: todo)) as Hnodup.
      { rewrite -H1. eapply NoDup_elements. }
      apply NoDup_app in Hnodup.
      destruct Hnodup as (_ & Hnodup & _).
      specialize (Hnodup lv).
      apply Hnodup; last by econstructor.
      eapply elem_of_list_lookup_2. eauto.
    }

    assert (locked !! x = None) as Hnone.
    { apply not_elem_of_dom_1. eauto. }

    rewrite map_total_insert //.
    iFrame.
    iApply big_sepML_insert_app; first by auto.
    iFrame.
    iFrame "#".
    iSplitR; first by done.
    iExists _. iFrame. done.
  }

  iIntros "[Haccts_slice Hloop]".
  iNamed "Hloop".

  (* Use inv to know that the sum is total_bal *)
  iApply fupd_wp.
  iInv bankN as ">HbankInv" "HbankInvClose".
  iNamed "HbankInv".

(*
  iDestruct (map_valid with "HlogBalCtx Hacc1_log") as %Hacc1_logphys.
  iDestruct (map_valid with "HlogBalCtx Hacc2_log") as %Hacc2_logphys.
*)
  replace (map_total locked) with (map_total m).
  2: {
    (* XXX
     * 1. locked ⊆ m by map_valid for every element in Hml.
     * 2. dom locked = accts_l (by Hml) = accts (by H1) = dom m (by H3)
     * 3. thus, locked=m.
     *)
    admit.
  }

  iMod ("HbankInvClose" with "[HlogBalCtx]") as "_".
  { iNext. iExists _. iFrame "∗ %". }
  iModIntro.

  wp_loadField.
  wp_apply (wp_forSliceEach
    ("Hlck" ∷ bck ↦[BankClerk :: "lck"] #lck ∗
     "Hlck_own" ∷ own_LockClerk lck γ.(bank_ls_names))%I
    (λ acc,
     "#Hacc_islock" ∷ is_lock lockN γ.(bank_ls_names) acc (bankPs γ acc) ∗
     "HbankPs" ∷ bankPs γ acc)%I
    (λ acc, True)%I
    with "[] [$Haccts_slice $Hlck $Hlck_own Hml]").
  {
    iIntros (?? Ψ) "!> [Hi Hp] HΨ".
    iNamed "Hi".
    iNamed "Hp".
    wp_loadField.
    wp_apply (wp_LockClerk__Unlock with "[$Hlck_own $Hacc_islock $HbankPs]").
    iIntros "Hlck_own".
    iApply "HΨ". iFrame.
  }
  {
    iDestruct (big_sepML_sepL_exists with "Hml") as "Hl".
    iApply (big_sepL_impl with "Hl").
    iModIntro. iIntros (??) "%Hsome H".
    iDestruct "H" as (kk vv) "(%Hlocked & #Hislock & %Heq & HbankPs)".
    subst.
    iFrame "Hislock".
    iDestruct "HbankPs" as (vd) "HbankPs".
    iExists _, _. iFrame.
  }

  iIntros "[Haccts_slice [Hi Hq]]".
  iNamed "Hi".

  wp_load.
  replace (map_total m) with (bal_total) by auto.
  iApply "Hpost".
  iModIntro. iExists _, _, _, _. iFrame "∗#%".
Admitted.

Lemma Bank__SimpleAudit_spec (bck:loc) γ accts :
{{{
     inv bankN (bank_inv γ accts) ∗
     own_bank_clerk γ bck accts
}}}
  BankClerk__SimpleAudit #bck
{{{
     RET #(); True
}}}.
Proof.
  iIntros (Φ) "[#Hbinv Hpre] Hpost".
  wp_lam.
  wp_pures.
  iCombine "Hpre Hpost" as "H".
  wp_apply (wp_forBreak' with "[-]").
  { iExact "H". }
  iModIntro. iIntros "[Hpre Hpost]".
  wp_pures.
  wp_apply (Bank__get_total_spec with "[$]").
  iIntros "Hpre". rewrite /bal_total.
  wp_pures.
  iModIntro. iLeft. iFrame. eauto.
Qed.

Lemma wp_MakeBankClerk (lockhost kvhost : u64) cm γ1 γ2 cid accts (accts_s : Slice.t) (accts_l : list u64) acc0 :
  {{{
       is_coord_server lockhost γ1 ∗
       is_coord_server kvhost γ2 ∗
       is_ConnMan cm ∗
       is_lock lockN (γ1.(coord_kv_gn)) init_flag
         (init_lock_inv init_flag γ1.(coord_kv_gn) γ2.(coord_kv_gn) accts) ∗
       own_slice_small accts_s uint64T 1 accts_l ∗
       ⌜Permutation (elements accts) accts_l⌝ ∗
       ⌜accts_l !! int.nat 0 = Some acc0⌝
  }}}
    MakeBankClerk #lockhost #kvhost #cm #init_flag (slice_val accts_s) #cid
  {{{
      γ (ck:loc), RET #ck; own_bank_clerk γ ck accts ∗ inv bankN (bank_inv γ accts)
  }}}
.
Proof.
  iIntros (Φ) "(#Hcoord_lock&#Hcoord_kv&#Hcm&#Hinit_lock&Haccts_slice&%Hperm&%Hnonempty) HΦ".
  rewrite /MakeBankClerk.
  wp_call.
  wp_apply wp_allocStruct; first val_ty.
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_MakeLockClerk with "[$Hcoord_lock $Hcm]").
  iIntros (lkCk) "Hlk".
  wp_storeField.

  wp_apply (wp_MakeSeqKVClerk with "[$Hcoord_kv $Hcm]").
  iIntros (kvCk) "Hkv".
  do 2 wp_storeField.

  wp_loadField.
  wp_apply (wp_LockClerk__Lock with "[$]").
  iIntros "(Hlk&Hinit)".

  wp_pures.
  wp_apply (typed_slice.wp_NewSlice (V:=u8)).
  iIntros (s0) "Hsl0".
  wp_loadField.
  wp_apply (wp_SeqKVClerk__Get with "[$Hkv]").
  iDestruct "Hinit" as "[Huninit|Hinit]".
  - iDestruct "Huninit" as "(Hflag&Haccs)".
    iApply (fupd_mask_weaken ∅); first by set_solver+. iIntros "Hclo'".
    iModIntro. iExists _. iFrame. iIntros "Hflag".
    iMod "Hclo'" as "_". iModIntro.
    iIntros (val_sl_flag q). iIntros "(Hkv&Hsl1)".
    iDestruct (own_slice_to_small with "Hsl0") as "Hsl0".
    wp_apply (wp_BytesEqual with "[Hsl0 Hsl1]").
    { by iFrame. }
    iIntros "(Hsl1&Hsl0)".
    wp_pures.

    wp_loadField.
    wp_apply (wp_forSliceEach
      ("kvck" ∷ l ↦[BankClerk :: "kvck"] #kvCk ∗
       "Hkv" ∷ own_SeqKVClerk kvCk γ2.(coord_kv_gn))%I
      (λ acc,
       "Hkv2" ∷ kvptsto γ2.(coord_kv_gn) acc [] ∗
       "Hkv1" ∷ kvptsto γ1.(coord_kv_gn) acc [])%I
      (λ acc,
       ∃ data,
        kvptsto γ1.(coord_kv_gn) acc [] ∗
        kvptsto γ2.(coord_kv_gn) acc data ∗
        ⌜has_encoding_Uint64 data 0⌝)%I with "[] [$Haccts_slice $kvck $Hkv Haccs]").
    {
      iIntros (???) "!> [Hi Hp] HΨ".
      iNamed "Hi".
      iNamed "Hp".
      wp_apply (wp_EncodeUint64).
      iIntros (??) "(Hval_slice&%)".
      wp_loadField.
      iDestruct (own_slice_to_small with "Hval_slice") as "Hval_slice".
      iMod (readonly_alloc_1 with "Hval_slice") as "#Hval_slice".
      wp_apply (wp_SeqKVClerk__Put with "[$Hkv]"); first by eauto.

      iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
      iExists _. iFrame. iIntros "Hacc1_phys".
      iMod ("Hclo") as "_". iIntros "!> Hkv".
      wp_pures.

      iApply "HΨ".
      iFrame. iExists _. iFrame. done.
    }
    {
      rewrite -Hperm.
      iApply big_sepS_elements.
      iApply (big_sepS_impl with "Haccs").
      iModIntro. iIntros (?) "%Hin [H2 H1]".
      iFrame.
    }
    iIntros "[Haccts_slice [Hi Hq]]".
    iNamed "Hi".

    wp_apply (wp_EncodeUint64).
    iIntros (??) "(Hval_slice&%)".
    wp_loadField.
    iDestruct (own_slice_to_small with "Hval_slice") as "Hval_slice".
    iMod (readonly_alloc_1 with "Hval_slice") as "#Hval_slice".

    wp_apply (wp_SliceGet with "[$Haccts_slice]"); first by eauto.
    iIntros "Haccts_slice".
    wp_loadField.
    wp_apply (wp_SeqKVClerk__Put with "[$Hkv]"); first by eauto.

    admit.
(*
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc1_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkv".
    wp_pures.
  

    wp_apply (typed_slice.wp_NewSlice (V:=u8)).
    iIntros (?) "Hflag_val_slice".
    wp_loadField.
    iDestruct (own_slice_to_small with "Hflag_val_slice") as "Hflag_val_slice".
    iMod (readonly_alloc_1 with "Hflag_val_slice") as "#Hflag_val_Slice".
    wp_apply (wp_SeqKVClerk__Put with "[$Hkv]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hflag_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkv".
    wp_pures.

    wp_loadField.
    iMod (map_init (∅ : gmap u64 u64)) as (γlog) "Hmap_ctx".
    iMod (map_alloc acc2 (U64 0) with "[$]") as "(Hmap_ctx&Hacc2)".
    { rewrite lookup_empty //. }
    iMod (map_alloc acc1 bal_total with "[$]") as "(Hmap_ctx&Hacc1)".
    { rewrite lookup_insert_ne //. }
    set γ := {| bank_ls_names := γ1.(coord_kv_gn);
                bank_ks_names := γ2.(coord_kv_gn);
                bank_logBalGN := γlog |}.
    iMod (lock_alloc lockN _ _ acc1 (bankPs γ acc1) with "[$] [Hacc1_phys Hacc1]") as "#Hlk1".
    { iExists _, _. by iFrame. }
    iMod (lock_alloc lockN _ _ acc2 (bankPs γ acc2) with "[$] [Hacc2_phys Hacc2]") as "#Hlk2".
    { iExists _, _. by iFrame. }
    iMod (inv_alloc bankN _ (bank_inv γ {[acc1; acc2]}) with "[Hmap_ctx]") as "#Hinv".
    { iNext. iExists _. iSplitL "Hmap_ctx".
      { rewrite /named. iFrame. }
      iPureIntro; split.
      { rewrite map_total_insert; last by rewrite lookup_insert_ne //.
        rewrite map_total_insert; last by eauto.
        rewrite map_total_empty. word. }
      { rewrite dom_insert_L dom_insert_L. set_solver. }
    }
    wp_apply (wp_LockClerk__Unlock with "[$Hlk $Hinit_lock Hflag_phys]").
    { iRight. iExists γlog. iFrame "#". iFrame "Hflag_phys". }
    iIntros "H". wp_pures. iApply "HΦ". iModIntro. iFrame "Hinv".
    iExists _, _. iFrame. eauto.
*)
  - iDestruct "Hinit" as (γlog) "(Hflag&#Hinv&#H)".
    iApply (fupd_mask_weaken ∅); first by set_solver+. iIntros "Hclo'".
    iModIntro. iExists _. iFrame. iIntros "Hflag".
    iMod "Hclo'" as "_". iModIntro.
    iIntros (val_sl_flag q). iIntros "(Hkv&Hsl1)".
    iDestruct (own_slice_to_small with "Hsl0") as "Hsl0".
    wp_apply (wp_BytesEqual with "[Hsl0 Hsl1]").
    { by iFrame. }
    iIntros "(Hsl1&Hsl0)".
    wp_pures.
    wp_loadField.
    wp_apply (wp_LockClerk__Unlock with "[$Hlk $Hinit_lock Hflag]").
    { iRight. iExists γlog. iFrame "∗#". }
    iIntros "Hlck_own". wp_pures. iApply "HΦ". iModIntro. iFrame "Hinv".
    iExists _, _, _, _. iFrame "∗#%".
    iDestruct (big_sepS_elements with "H") as "He". rewrite Hperm. iFrame "He".
Admitted.

End bank_proof.

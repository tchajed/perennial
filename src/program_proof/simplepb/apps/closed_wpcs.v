From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import closed.
From iris.base_logic Require Import ghost_map.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require grove_ffi_adequacy.
From Perennial.program_logic Require dist_lang.

From Perennial.program_proof.bank Require Export bank_proof.
From Perennial.program_proof.lock Require Export lock_proof.
From Perennial.program_proof.simplepb Require Import pb_init_proof pb_definitions.
From Perennial.program_proof.simplepb Require Import kv_proof config_proof.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.simplepb.apps Require Import clerkpool_proof.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From Perennial.goose_lang Require Import crash_borrow crash_modality.
From Perennial.goose_lang Require Import recovery_lifting.

Section closed_wpcs.

Context `{!heapGS Σ}.
Context `{!ekvG Σ}.
Context {kvParams:ekvParams.t}.
Lemma wpc_kv_replica_main γ γsrv Φc fname me configHost data :
  ((∃ data' : list u8, fname f↦data' ∗ ▷ kv_crash_resources γ γsrv data') -∗
    Φc) -∗
  ("#Hconf" ∷ is_kv_config_host configHost γ ∗
   "#Hhost" ∷ is_kv_replica_host me γ γsrv ∗
   "Hfile" ∷ fname f↦ data ∗
   "Hcrash" ∷ kv_crash_resources γ γsrv data
  ) -∗
  WPC kv_replica_main #(LitString fname) #me #configHost @ ⊤
  {{ _, True }}
  {{ Φc }}
.
Proof.
  iIntros "HΦc H". iNamed "H".

  unfold kv_replica_main.
  wpc_call.
  { iApply "HΦc". iExists _. iFrame. }

  iCache with "HΦc Hfile Hcrash".
  { iApply "HΦc". iExists _. iFrame. }
  wpc_bind (Primitive2 _ _ _).
  wpc_frame.
  iApply wp_crash_borrow_generate_pre.
  { done. }
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (?) "Hl".
  iIntros "Hpreborrow".
  iNamed 1.
  wpc_pures.
  wpc_bind (store_ty _ _).
  wpc_frame.
  wp_store.
  iModIntro.
  iNamed 1.

  iApply wpc_cfupd.
  wpc_apply (wpc_crash_borrow_inits with "Hpreborrow [Hfile Hcrash] []").
  { iAccu. }
  {
    iModIntro.
    instantiate (1:=(|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ kv_crash_resources γ γsrv data')).
    iIntros "[H1 H2]".
    iModIntro.
    iExists _.
    iFrame.
  }
  iIntros "Hfile_ctx".
  wpc_apply (wpc_crash_mono _ _ _ _ _ (True%I) with "[HΦc]").
  { iIntros "_".
    iIntros "H".
    iMod "H".
    iModIntro.
    iApply "HΦc".
    done. }
  iApply wp_wpc.
  wp_pures.
  wp_apply (wp_Start with "[$Hfile_ctx]").
  { iFrame "#". }
  wp_pures.
  done.
Qed.


Definition dconfigHost : u64 := (U64 10).
Definition dr1Host: u64 := (U64 1).
Definition dr2Host: u64 := (U64 2).

Definition lconfigHost : u64 := (U64 110).
Definition lr1Host: u64 := (U64 101).
Definition lr2Host: u64 := (U64 102).

Lemma wp_dconfig_main γconf :
  "HconfInit" ∷ makeConfigServer_pre γconf [dr1Host; dr2Host] ∗
  "#Hhost" ∷ is_config_host dconfigHost γconf -∗
  WP dconfig_main #() {{ _, True }}
.
Proof.
  iNamed 1.
  wp_call.
  wp_apply (wp_NewSlice).
  iIntros (?) "Hsl".
  wp_apply wp_ref_to.
  { done. }
  iIntros (servers_ptr) "Hservers".
  wp_pures.

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  wp_apply (wp_SliceAppend with "Hsl").
  iIntros (?) "Hsl".
  wp_apply (wp_StoreAt with "[$Hservers]").
  { done. }
  iIntros "Hservers".

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  wp_apply (wp_SliceAppend with "Hsl").
  iIntros (?) "Hsl".
  wp_apply (wp_StoreAt with "[$Hservers]").
  { done. }
  iIntros "Hservers".

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  rewrite replicate_0.
  simpl.
  wp_apply (config_proof.wp_MakeServer with "[$HconfInit $Hsl]").
  iIntros (?) "#Hissrv".
  wp_apply (wp_Server__Serve with "[$]").
  {
    iFrame "Hissrv".
  }
  wp_pures.
  done.
Qed.

Lemma wp_lconfig_main γconf :
  "HconfInit" ∷ makeConfigServer_pre γconf [lr1Host; lr2Host] ∗
  "#Hhost" ∷ is_config_host lconfigHost γconf -∗
  WP lconfig_main #() {{ _, True }}
.
Proof.
  iNamed 1.
  wp_call.
  wp_apply (wp_NewSlice).
  iIntros (?) "Hsl".
  wp_apply wp_ref_to.
  { done. }
  iIntros (servers_ptr) "Hservers".
  wp_pures.

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  wp_apply (wp_SliceAppend with "Hsl").
  iIntros (?) "Hsl".
  wp_apply (wp_StoreAt with "[$Hservers]").
  { done. }
  iIntros "Hservers".

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  wp_apply (wp_SliceAppend with "Hsl").
  iIntros (?) "Hsl".
  wp_apply (wp_StoreAt with "[$Hservers]").
  { done. }
  iIntros "Hservers".

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  rewrite replicate_0.
  simpl.
  wp_apply (config_proof.wp_MakeServer with "[$HconfInit $Hsl]").
  iIntros (?) "#Hissrv".
  wp_apply (wp_Server__Serve with "[$]").
  {
    iFrame "Hissrv".
  }
  wp_pures.
  done.
Qed.

Context `{!bankG Σ}.
Lemma wp_makeBankClerk γlk γkv (kvParams1 kvParams2:ekvParams.t):
  {{{
        "#Hhost1" ∷ is_kv_config_host (params:=kvParams1) dconfigHost γkv ∗
        "#Hhost2" ∷ is_kv_config_host (params:=kvParams2) lconfigHost γlk ∗
        "#Hbank" ∷ is_bank "init" (Build_lock_names (kv_ptsto γlk)) (kv_ptsto γkv) {[ "a1"; "a2" ]}
  }}}
    makeBankClerk #()
  {{{
        (b:loc), RET #b; own_bank_clerk b {[ "a1" ; "a2" ]}
  }}}
.
Proof.
  clear kvParams.
  iIntros (?) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_apply (wp_MakeKv (params:=kvParams1) with "[$Hhost1]").
  iIntros (?) "#Hkv".
  wp_pures.

  wp_apply (wp_MakeKv with "[$Hhost2]").
  iIntros (?) "Hlock_kv".
  wp_apply (wp_MakeLockClerk lockN with "[Hlock_kv]").
  {
    instantiate (3:=(Build_lock_names (kv_ptsto γlk))).
    iFrame. iPureIntro. solve_ndisj.
  }
  iIntros (?) "#Hlck".
  wp_pures.
  wp_apply (wp_MakeBankClerk with "[]").
  { iFrame "#". done. }
  iIntros (?) "Hb".
  iApply "HΦ".
  iFrame.
Qed.

Definition bank_pre : iProp Σ :=
  ∃ γkv γlk (p1 p2:ekvParams.t),
  "#Hhost1" ∷ is_kv_config_host (params:=p1) dconfigHost γkv ∗
  "#Hhost2" ∷ is_kv_config_host (params:=p2) lconfigHost γlk ∗
  "#Hbank" ∷ is_bank "init" (Build_lock_names (kv_ptsto γlk)) (kv_ptsto γkv) {[ "a1"; "a2" ]}
.

Lemma wp_bank_transferer_main :
  {{{
        bank_pre
  }}}
    bank_transferer_main #()
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (?) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_apply (wp_makeBankClerk with "[]").
  { (* FIXME: there are two parameter typeclass instances in context *)
    clear kvParams.
    iFrame "Hbank".
    iSplit.
    { iExact "Hhost1". }
    { iExact "Hhost2". }
  }
  iIntros (?) "Hck".
  wp_pures.
  wp_forBreak.
  wp_pures.
  wp_apply (Bank__SimpleTransfer_spec with "[$]").
  iIntros "Hck".
  wp_pures.
  iModIntro. iLeft. iFrame. done.
Qed.

Lemma wp_bank_auditor_main :
  {{{
        bank_pre
  }}}
    bank_auditor_main #()
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (?) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_apply (wp_makeBankClerk with "[]").
  { (* FIXME: there are two parameter typeclass instances in context *)
    clear kvParams.
    iFrame "Hbank".
    iSplit.
    { iExact "Hhost1". }
    { iExact "Hhost2". }
  }
  iIntros (?) "Hck".
  wp_pures.
  wp_forBreak.
  wp_pures.
  wp_apply (Bank__SimpleAudit_spec with "[$]").
  iIntros "Hck".
  wp_pures.
  iModIntro. iLeft. iFrame. done.
Qed.

End closed_wpcs.

Section closed_wprs.

Context {kvParams:ekvParams.t}.

#[global]
Instance is_kv_config_into_crash `{hG0: !heapGS Σ} `{!ekvG Σ} u γ:
  IntoCrash (is_kv_config_host u γ)
    (λ hG, ⌜ hG0.(goose_globalGS) = hG.(goose_globalGS) ⌝ ∗ is_kv_config_host u γ)%I
.
Proof.
  rewrite /IntoCrash /is_kv_config_host.
  iIntros "$". iIntros; eauto.
Qed.

#[global]
Instance is_kv_replica_host_into_crash `{hG0: !heapGS Σ} `{!ekvG Σ} u γ γsrv:
  IntoCrash (is_kv_replica_host u γ γsrv)
    (λ hG, ⌜ hG0.(goose_globalGS) = hG.(goose_globalGS) ⌝ ∗ is_kv_replica_host u γ γsrv)%I
.
Proof.
  rewrite /IntoCrash /is_kv_replica_host.
  iIntros "$". iIntros; eauto.
Qed.

#[global]
Instance kv_crash_into_crash `{hG0: !heapGS Σ} `{!ekvG Σ} a b c:
  IntoCrash (kv_crash_resources a b c)
    (λ hG, (kv_crash_resources a b c))%I.
Proof.
  rewrite /IntoCrash /file_crash.
  iIntros "$". iIntros; eauto.
Qed.

Local Definition crash_cond {Σ} `{ekvG Σ} {fname γ γsrv} :=
  (λ hG : heapGS Σ, ∃ data, fname f↦ data ∗ ▷ kv_crash_resources γ γsrv data)%I.

Lemma wpr_kv_replica_main fname me configHost γ γsrv {Σ} `{HKV: ekvG Σ}
                               {HG} {HL}:
  let hG := {| goose_globalGS := HG; goose_localGS := HL |} in
  ("#Hconf" ∷ is_kv_config_host configHost γ ∗
   "#Hhost" ∷ is_kv_replica_host me γ γsrv ∗
   "Hcrash" ∷ kv_crash_resources γ γsrv [] ∗
   "Hfile" ∷ fname f↦ []
  ) -∗
  wpr NotStuck ⊤ (kv_replica_main #(LitString fname) #me #configHost) (kv_replica_main #(LitString fname) #me #configHost) (λ _ : goose_lang.val, True)
    (λ _ , True) (λ _ _, True).
Proof.
  intros.
  iNamed 1.
  iApply (idempotence_wpr with "[Hfile Hcrash] []").
  {
    instantiate (1:=crash_cond).
    simpl.
    wpc_apply (wpc_kv_replica_main with "[]").
    { iIntros "$". }
    iFrame "∗#".
  }
  { (* recovery *)
    rewrite /hG.
    clear hG.
    iModIntro.
    iIntros (????) "Hcrash".
    iNext.
    iDestruct "Hcrash" as (?) "[Hfile Hcrash]".
    simpl.
    set (hG' := HeapGS _ _ hL').
    iDestruct "Hconf" as "-#Hconf".
    iDestruct "Hhost" as "-#Hhost".
    iCrash.
    iIntros "_".
    destruct hL as [HG'' ?].
    iSplit; first done.
    iDestruct "Hconf" as "(%&Hconf)".
    iDestruct "Hhost" as "(%&Hhost)".
    subst.
    simpl in *.
    clear hG'.
    clear hL'.
    (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    set (hG2' := HeapGS _ _ goose_localGS).
    simpl.
    wpc_apply (wpc_kv_replica_main (heapGS0:=hG2') with "[]").
    { iIntros "H".
      iDestruct "H" as (?) "[Hfile Hcrash]".
      iExists _.
      iFrame.
    }
    iFrame "∗#".
  }
Qed.

Lemma wpr_dconfig_main {Σ} `{HKV: ekvG Σ} γ
                               {HG} {HL}:
  let hG := {| goose_globalGS := HG; goose_localGS := HL |} in
  ("#Hhost" ∷ is_config_host dconfigHost γ ∗
   "Hcrash" ∷ makeConfigServer_pre γ [dr1Host ; dr2Host]
  ) -∗
  wpr NotStuck ⊤ (dconfig_main #())
      (#()) (λ _ : goose_lang.val, True)
    (λ _ , True) (λ _ _, True).
Proof.
  intros.
  iNamed 1.
  iApply (idempotence_wpr with "[-] []").
  {
    instantiate (1:=(λ _, True)%I).
    simpl.
    iApply wp_wpc.
    wp_apply (wp_dconfig_main with "[$]").
  }
  { (* recovery *)
    rewrite /hG.
    clear hG.
    iModIntro.
    iIntros (????) "Hcrash".
    iNext.
    set (hG' := HeapGS _ _ hL').
    iDestruct "Hhost" as "-#Hhost".
    iCrash.
    iIntros "_".
    iSplit; first done.
    by wpc_pures.
  }
Qed.

Lemma wpr_lconfig_main {Σ} `{HKV: ekvG Σ} γ
                               {HG} {HL}:
  let hG := {| goose_globalGS := HG; goose_localGS := HL |} in
  ("#Hhost" ∷ is_config_host lconfigHost γ ∗
   "Hcrash" ∷ makeConfigServer_pre γ [lr1Host ; lr2Host]
  ) -∗
  wpr NotStuck ⊤ (lconfig_main #())
      (#()) (λ _ : goose_lang.val, True)
    (λ _ , True) (λ _ _, True).
Proof.
  intros.
  iNamed 1.
  iApply (idempotence_wpr with "[-] []").
  {
    instantiate (1:=(λ _, True)%I).
    simpl.
    iApply wp_wpc.
    wp_apply (wp_lconfig_main with "[$]").
  }
  { (* recovery *)
    rewrite /hG.
    clear hG.
    iModIntro.
    iIntros (????) "Hcrash".
    iNext.
    set (hG' := HeapGS _ _ hL').
    iDestruct "Hhost" as "-#Hhost".
    iCrash.
    iIntros "_".
    iSplit; first done.
    by wpc_pures.
  }
Qed.

End closed_wprs.

Section closed_init.

Context `{!gooseGlobalGS Σ}.

Existing Instance toEsmParams1.
Lemma alloc_vkv (params:ekvParams.t) configHost allocated `{!ekvG Σ}:
  length ekvParams.initconfig > 0 →
  configHost c↦ ∅ ∗
  ([∗ list] h ∈ ekvParams.initconfig, h c↦ ∅)
  ={⊤}=∗ (∃ γ,

  (* system-wide: allows clients to connect to the system, and gives them ownership of keys *)
  ([∗ set] k ∈ allocated, kv_ptsto γ k "") ∗
  is_kv_config_host configHost γ ∗

  (* for each kv replica server:  *)
  ([∗ list] host ∈ ekvParams.initconfig,
     ∃ γsrv,
     is_kv_replica_host host γ γsrv ∗
     kv_crash_resources γ γsrv []
  )) ∗

  (* for each the config server:  *)
  (∃ γconf,
    is_config_host configHost γconf ∗
    makeConfigServer_pre γconf ekvParams.initconfig
  )
.
Proof.
  intros.
  iIntros "[HconfChan Hchan]".
  iMod (alloc_simplepb_system with "[$Hchan] [$HconfChan]") as (?) "H"; try done.
  iDestruct "H" as "(Hlog & #Hhosts & Hsrvs & HconfSrvs)".
  iFrame "HconfSrvs".
  iMod (ghost_map_alloc (gset_to_gmap "" allocated)) as (γkv_gn) "[Hauth Hkvs]".
  iExists (Build_kv_names _ _).
  rewrite big_sepM_gset_to_gmap.
  iFrame "Hkvs".
  iAssert (|={⊤}=> is_kv_config_host configHost _)%I with "[Hlog Hauth]" as ">#Hhosts2".
  {
    rewrite /is_kv_config_host.
    iMod (esm_proof.alloc_esm with "Hlog") as (??) "(#He1 & #He2 & Hlog)".
    repeat iExists _.
    instantiate (1:=Build_kv_names _ _). simpl.
    iFrame "#".
    iMod (inv_alloc with "[-]"); last done.
    iNext. repeat iExists _.
    iFrame. rewrite /own_kvs /=.
    iExists _; iFrame.
    iExactEq "Hauth".
    repeat f_equal.
    rewrite /kv_vsm_proof.compute_state /=.
    rewrite map_empty_union. done.
  }
  iModIntro.
  iFrame "#".
  simpl. rewrite app_nil_r.
  iApply (big_sepL_impl with "Hsrvs []").
  iIntros "!# * %Hlookup H".
  iDestruct "H" as (?) "[#HpbHost Hghost]".
  iExists _. rewrite /is_kv_replica_host. iFrame "HpbHost".
  rewrite /kv_crash_resources.
  iLeft. iFrame. done.
Qed.

End closed_init.

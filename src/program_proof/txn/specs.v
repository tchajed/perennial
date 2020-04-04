From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import deletable_heap.

From Goose.github_com.mit_pdos.goose_nfsd Require Import txn.
From Perennial.program_proof Require Import wal.specs wal.heapspec addr.specs buf.specs.

Inductive updatable_buf (T : Type) :=
| UB : forall (v : T) (modifiedSinceInstallG : gname), updatable_buf T
.

Arguments UB {T} v modifiedSinceInstallG.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!gen_heapPreG u64 heap_block Σ}.
Context `{!sigT (fun K => gen_heapPreG u64 (updatable_buf (@bufDataT K)) Σ)}.
Context `{!gen_heapPreG unit
           (gmap u64 (sigT (fun K => gmap u64 (updatable_buf (@bufDataT K)))))
         Σ}.
Context `{!gen_heapPreG addr (sigT (fun K => @bufDataT K)) Σ}.
Context `{!inG Σ (authR (optionUR (exclR boolO)))}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "txnlock".
Definition invN : namespace := nroot .@ "txninv".
Definition walN : namespace := nroot .@ "txnwal".

Definition mapsto_txn {K} (gData : gmap u64 (sigT (fun K => gen_heapG u64 (updatable_buf (@bufDataT K)) Σ))) (a : addr) (v : @bufDataT K) : iProp Σ :=
  ∃ hG γm,
    ⌜ valid_addr a ⌝ ∗
    ⌜ gData !! a.(addrBlock) = Some (existT K hG) ⌝ ∗
    mapsto (hG := hG) a.(addrOff) 1 (UB v γm) ∗
    own γm (◯ (Excl' true)).

Theorem mapsto_txn_2 {K} gData a v0 v1 :
  @mapsto_txn K gData a v0 -∗
  @mapsto_txn K gData a v1 -∗
  False.
Proof.
  rewrite /mapsto_txn.
  iIntros "H0 H1".
  iDestruct "H0" as (g0 m0) "(% & % & H0m & H0own)".
  iDestruct "H1" as (g1 m1) "(% & % & H1m & H1own)".
  rewrite H0 in H2; inversion H2.
  apply eq_sigT_eq_dep in H4.
  apply Eqdep_dec.eq_dep_eq_dec in H4; subst.
  2: apply bufDataKind_eq_dec.
  iDestruct (mapsto_valid_2 with "H0m H1m") as %x.
  exfalso; eauto.
Qed.

Theorem mapsto_txn_valid {K} gData a v :
  @mapsto_txn K gData a v -∗
  ⌜ valid_addr a ⌝.
Proof.
  rewrite /mapsto_txn.
  iIntros "H".
  iDestruct "H" as (h g) "[% _]"; done.
Qed.

Definition txn_bufDataT_in_block {K} (installed : Block) (bs : list Block)
                                 (gm : gmap u64 (updatable_buf (@bufDataT K))) : iProp Σ :=
  (
    [∗ map] off ↦ ub ∈ gm,
      match ub with
      | UB bufData γm =>
        ⌜ is_bufData_at_off (latest_update installed bs) off bufData ⌝ ∗
        ∃ (modifiedSinceInstall : bool),
          own γm (● (Excl' modifiedSinceInstall)) ∗
          if modifiedSinceInstall then emp
          else
            ⌜ ∀ prefix,
              is_bufData_at_off (latest_update installed (take prefix bs)) off bufData ⌝
      end
  )%I.

Global Instance txn_bufDataT_in_block_timeless K installed bs gm : Timeless (@txn_bufDataT_in_block K installed bs gm).
Proof.
  apply big_sepM_timeless; intros.
  destruct x.
  apply sep_timeless; refine _.
  apply exist_timeless.
  destruct x; refine _.
Qed.

Definition gmDataP (gm : sigT (fun K => gmap u64 (updatable_buf (@bufDataT K))))
                   (gh : sigT (fun K => gen_heapG u64 (updatable_buf (@bufDataT K)) Σ)) : iProp Σ.
  refine (if decide (projT1 gm = projT1 gh) then _ else False)%I.
  refine (gen_heap_ctx (hG := projT2 gh) _)%I.
  rewrite <- e.
  refine (projT2 gm).
Defined.

Definition is_txn_always
    (walHeap : gen_heapG u64 heap_block Σ)
    (gData   : gmap u64 (sigT (fun K => gen_heapG u64 (updatable_buf (@bufDataT K)) Σ)))
    γMaps
    : iProp Σ :=
  (
    ∃ (mData : gmap u64 (sigT (fun K => gmap u64 (updatable_buf (@bufDataT K))))),
      ( [∗ map] _ ↦ gm;gh ∈ mData;gData, gmDataP gm gh ) ∗
      mapsto (hG := γMaps) tt (1/2) (mData) ∗
      ( [∗ map] blkno ↦ datamap ∈ mData,
          ∃ installed bs,
            mapsto (hG := walHeap) blkno 1 (HB installed bs) ∗
            txn_bufDataT_in_block installed bs (projT2 datamap) )
  )%I.

Global Instance is_txn_always_timeless walHeap gData γMaps :
  Timeless (is_txn_always walHeap gData γMaps).
Proof.
  apply exist_timeless; intros.
  apply sep_timeless; refine _.
  apply big_sepM2_timeless; intros.
  rewrite /gmDataP.
  destruct (decide (projT1 x1 = projT1 x2)); refine _.
Qed.

Definition is_txn_locked l γMaps : iProp Σ :=
  (
    ∃ (mData : gmap u64 (sigT (fun K => gmap u64 (updatable_buf (@bufDataT K)))))
      (nextId : u64) (pos : u64),
      mapsto (hG := γMaps) tt (1/2) mData ∗
      l ↦[Txn.S :: "nextId"] #nextId ∗
      l ↦[Txn.S :: "pos"] #pos
 )%I.

Definition is_txn (l : loc)
    (gData   : gmap u64 (sigT (fun K => gen_heapG u64 (updatable_buf (@bufDataT K)) Σ)))
    : iProp Σ :=
  (
    ∃ γMaps γLock (walHeap : gen_heapG u64 heap_block Σ) (mu : loc) (walptr : loc) q,
      l ↦[Txn.S :: "mu"]{q} #mu ∗
      l ↦[Txn.S :: "log"]{q} #walptr ∗
      is_wal walN (wal_heap_inv walHeap) walptr ∗
      inv invN (is_txn_always walHeap gData γMaps) ∗
      is_lock lockN γLock #mu (is_txn_locked l γMaps)
  )%I.

Theorem is_txn_dup l gData :
  is_txn l gData -∗
  is_txn l gData ∗
  is_txn l gData.
Proof.
  iIntros "Htxn".
  iDestruct "Htxn" as (????? q) "(Hmu & Hlog & #Hwal & #Hinv & #Hlock)".
  iDestruct (struct_field_mapsto_q with "Hmu") as "[Hmu0 Hmu1]".
  iDestruct (struct_field_mapsto_q with "Hlog") as "[Hlog0 Hlog1]".
  iSplitL "Hmu0 Hlog0".
  - iExists _, _, _, _, _, _. iFrame "Hmu0 Hlog0 Hwal Hinv Hlock".
  - iExists _, _, _, _, _, _. iFrame "Hmu1 Hlog1 Hwal Hinv Hlock".
Qed.

Lemma gmDataP_eq gm gh :
  gmDataP gm gh -∗ ⌜ projT1 gm = projT1 gh ⌝.
Proof.
  iIntros "H".
  rewrite /gmDataP.
  destruct (decide (projT1 gm = projT1 gh)); eauto.
Qed.

Lemma gmDataP_ctx gm (gh : gen_heapG u64 (updatable_buf (@bufDataT (projT1 gm))) Σ) :
  gmDataP gm (existT (projT1 gm) gh) -∗
  gen_heap_ctx (hG := gh) (projT2 gm).
Proof.
  iIntros "H".
  rewrite /gmDataP /=.
  destruct (decide (projT1 gm = projT1 gm)); eauto.
  rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq. iFrame.
Qed.

Lemma gmDataP_ctx' gm (gh : gen_heapG u64 (updatable_buf (@bufDataT (projT1 gm))) Σ) :
  gen_heap_ctx (hG := gh) (projT2 gm) -∗
  gmDataP gm (existT (projT1 gm) gh).
Proof.
  iIntros "H".
  rewrite /gmDataP /=.
  destruct (decide (projT1 gm = projT1 gm)); eauto.
  rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq. iFrame.
Qed.

Theorem wp_txn_Load K l gData a v :
  {{{ is_txn l gData ∗
      mapsto_txn gData a v
  }}}
    Txn__Load #l (addr2val a) #(bufSz K)
  {{{ (bufptr : loc) b, RET #bufptr;
      is_buf bufptr a b ∗
      ⌜ b.(bufDirty) = false ⌝ ∗
      ⌜ existT b.(bufKind) b.(bufData) = existT K v ⌝ ∗
      mapsto_txn gData a v
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hstable) HΦ".
  iDestruct "Htxn" as (γMaps γLock walHeap mu walptr q) "(Hl & Hwalptr & #Hwal & #Hinv & #Hlock)".
  iDestruct "Hstable" as (hG γm) "(% & % & Hstable & Hmod)".

  wp_call.
  wp_loadField.
  wp_call.

  wp_apply (wp_Walog__ReadMem _ _ (λ mb,
    mapsto a.(addrOff) 1 (UB v γm) ∗
    match mb with
    | Some b => own γm (◯ Excl' true) ∗
      ⌜ is_bufData_at_off b a.(addrOff) v ⌝
    | None => own γm (◯ Excl' false)
    end)%I with "[$Hwal Hstable Hmod]").
  {
    iApply (wal_heap_readmem walN invN with "[Hstable Hmod]").

    iInv invN as ">Hinv_inner" "Hinv_closer".
    iDestruct "Hinv_inner" as (mData) "(Hctxdata & Hbigmap & Hdata)".

    iDestruct (big_sepM2_lookup_2_some with "Hctxdata") as %Hblk; eauto.
    destruct Hblk.

    iDestruct (big_sepM2_lookup_acc with "Hctxdata") as "[Hctxdatablk Hctxdata]"; eauto.
    iDestruct (gmDataP_eq with "Hctxdatablk") as "%".
    simpl in *; subst.
    iDestruct (gmDataP_ctx with "Hctxdatablk") as "Hctxdatablk".
    iDestruct (gen_heap_valid with "Hctxdatablk Hstable") as %Hblockoff.
    iDestruct ("Hctxdata" with "[Hctxdatablk]") as "Hctxdata".
    { iApply gmDataP_ctx'. iFrame. }

    iDestruct (big_sepM_lookup_acc with "Hdata") as "[Hdatablk Hdata]"; eauto.
    iDestruct "Hdatablk" as (blk_installed blk_bs) "(Hblk & Hinblk)".

    iExists _, _. iFrame.

    iModIntro.
    iIntros (mb) "Hrmq".
    destruct mb; rewrite /=.

    {
      iDestruct "Hrmq" as "[Hrmq %]".

      iDestruct (big_sepM_lookup_acc with "Hinblk") as "[Hinblk Hinblkother]"; eauto.
      iDestruct "Hinblk" as "(% & Hinblk)".
      iDestruct ("Hinblkother" with "[Hinblk]") as "Hinblk".
      { iFrame. done. }

      iDestruct ("Hinv_closer" with "[-Hmod]") as "Hinv_closer".
      {
        iModIntro.
        iExists _.
        iFrame.
        iApply "Hdata".
        iExists _, _. iFrame.
      }

      iMod "Hinv_closer".
      iModIntro.
      intuition; subst.
      iFrame. done.
    }

    {
      iDestruct (big_sepM_delete with "Hinblk") as "[Hinblk Hinblkother]"; eauto.
      rewrite /=.
      iDestruct "Hinblk" as "[% Hinblk]".
      iDestruct "Hinblk" as (modSince) "[Hγm Hinblk]".
      iDestruct (ghost_var_agree with "Hγm Hmod") as %->.
      iMod (ghost_var_update _ false with "Hγm Hmod") as "[Hγm Hmod]".

      iDestruct ("Hinv_closer" with "[-Hmod]") as "Hinv_closer".
      {
        iModIntro.
        iExists _.
        iFrame.
        iApply "Hdata".
        iExists _, _.
        iFrame.
        iDestruct (big_sepM_mono with "Hinblkother") as "Hinblkother".
        2: {
          replace (projT2 x) with (<[a.(addrOff) := UB v γm]> (delete a.(addrOff) (projT2 x))) at 2.
          2: {
            rewrite insert_delete.
            rewrite insert_id; eauto.
          }
          iApply big_sepM_insert; first apply lookup_delete.
          iFrame.
          iSplitR.
          { simpl. done. }
          iExists _; iFrame.
          iPureIntro; intros.
          rewrite take_nil /=. eauto.
        }

        intros.
        iIntros "H". destruct x0. rewrite /=.
        iDestruct "H" as "[% H]".
        iDestruct "H" as (modSince) "[H Hif]".
        iSplitR; eauto.
        iExists _. iFrame.
        destruct modSince; iFrame.
        iDestruct "Hif" as %Hif.
        iPureIntro. intros. rewrite take_nil. eauto.
      }

      iMod "Hinv_closer".
      iModIntro.
      iFrame.
    }
  }

  iIntros (ok bl) "Hres".
  destruct ok.
  {
    (* Case 1: hit in the cache *)

    iDestruct ("Hres") as (b) "(Hisblock & Hlatest & Hown & %)".
    wp_pures.
    rewrite /abstraction.is_block.
    wp_apply (wp_MkBufLoad with "[$Hisblock]").
    { done. }
    iIntros (bufptr) "Hbuf".
    wp_pures.
    iApply "HΦ". iFrame.
    rewrite /=.
    iSplitR; first done.
    iSplitR; first done.
    iExists _, _. iFrame. done.
  }

  (* Case 2: missed in cache *)
  iDestruct ("Hres") as "(Hlatest & Hown)".
  wp_pures.

  wp_apply (wp_Walog__ReadInstalled _ _
    (λ b, ⌜ is_bufData_at_off b a.(addrOff) v ⌝ ∗
      mapsto (hG := hG) a.(addrOff) 1 (UB v γm) ∗
      own γm (◯ (Excl' true)))%I
    with "[$Hwal Hlatest Hown]").
  {
    iApply (wal_heap_readinstalled walN invN with "[Hlatest Hown]").

    iInv invN as ">Hinv_inner" "Hinv_closer".
    iDestruct "Hinv_inner" as (mData) "(Hctxdata & Hbigmap & Hdata)".

    iDestruct (big_sepM2_lookup_2_some with "Hctxdata") as %Hblk; eauto.
    destruct Hblk.

    iDestruct (big_sepM2_lookup_acc with "Hctxdata") as "[Hctxblock Hctxdata]"; eauto.
    iDestruct (gmDataP_eq with "Hctxblock") as "%".
    simpl in *; subst.
    iDestruct (gmDataP_ctx with "Hctxblock") as "Hctxblock".
    iDestruct (gen_heap_valid with "Hctxblock Hlatest") as %Hblockoff.
    iDestruct ("Hctxdata" with "[Hctxblock]") as "Hctxdata".
    { iApply gmDataP_ctx'. iFrame. }

    iDestruct (big_sepM_lookup_acc with "Hdata") as "[Hblock Hdata]"; eauto.
    iDestruct "Hblock" as (blk_installed blk_bs) "(Hblk & Hinblk)".

    iExists _, _. iFrame "Hblk".

    iModIntro.
    iIntros (b) "Hriq".
    iDestruct "Hriq" as "[Hriq %]".

    iDestruct (big_sepM_lookup_acc with "Hinblk") as "[Hinblk Hinblkother]"; eauto.
    rewrite /=.
    iDestruct "Hinblk" as "[% Hinblk]".
    iDestruct "Hinblk" as (modSince) "[Hγm Hinblk]".
    iDestruct (ghost_var_agree with "Hγm Hown") as %->.
    iMod (ghost_var_update _ true with "Hγm Hown") as "[Hγm Hown]".
    iDestruct "Hinblk" as %Hinblk.
    iFrame.

    iDestruct ("Hinv_closer" with "[-]") as "Hinv_closer".
    {
      iModIntro.
      iExists _.
      iFrame.
      iApply "Hdata".
      iExists _, _. iFrame.
      iApply "Hinblkother".
      iSplitR; first done.
      iExists _; iFrame.
    }

    iMod "Hinv_closer".
    iModIntro.
    iPureIntro.

    apply elem_of_list_lookup_1 in H2.
    destruct H2 as [prefix H2].
    specialize (Hinblk prefix).
    erewrite latest_update_take_some in Hinblk; eauto.
  }

  iIntros (bslice) "Hres".
  iDestruct "Hres" as (b) "(Hb & % & Hlatest & Hmod)".
  wp_pures.
  rewrite /abstraction.is_block.
  wp_apply (wp_MkBufLoad with "[$Hb]").
  { done. }
  iIntros (bufptr) "Hbuf".
  wp_pures.
  iApply "HΦ".
  iFrame. rewrite /=.
  iSplitR; first done.
  iSplitR; first done.
  iExists _, _. iFrame. done.
Qed.

Theorem wp_txn__installBufs l q gData mData walHeap γMaps bufs buflist (bufamap : gmap addr buf) :
  {{{ is_txn l gData ∗
      inv invN (is_txn_always walHeap gData γMaps) ∗
      mapsto (hG := γMaps) tt (1/2) mData ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist,
        ∃ (bufptr : loc) v0,
          ⌜ bufptrval = #bufptr ⌝ ∗
          is_buf bufptr a buf ∗
          @mapsto_txn buf.(bufKind) gData a v0
  }}}
    Txn__installBufs #l (slice_val bufs)
  {{{ (blks : Slice.t) updlist, RET (slice_val blks);
      mapsto (hG := γMaps) tt (1/2) mData ∗
      abstraction.updates_slice blks updlist ∗
      ( [∗ list] _ ↦ walUpd ∈ updlist,
        let blknum := walUpd.(abstraction.update.addr) in
        let walBlock := walUpd.(abstraction.update.b) in
        ∃ K gDataGH,
          ⌜ gData !! blknum = Some (existT K gDataGH) ⌝ ∗
          ∀ diskInstalled diskBs,
            mapsto (hG := walHeap) blknum 1 (HB diskInstalled diskBs) -∗
            let diskLatest := latest_update diskInstalled diskBs in
            ∀ off,
              ⌜ match bufamap !! (Build_addr blknum off) with
                | None => ∀ (bufData : @bufDataT K),
                  is_bufData_at_off diskLatest off bufData ->
                  is_bufData_at_off walBlock off bufData
                | Some buf =>
                  is_bufData_at_off walBlock off buf.(bufData)
                end ⌝
      ) ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ list] _ ↦ bufptrval ∈ buflist,
        ∃ (bufptr : loc) a buf v0,
          ⌜ bufptrval = #bufptr ⌝ ∗
          is_buf bufptr a buf ∗
          @mapsto_txn buf.(bufKind) gData a v0
  }}}.
Proof.
  iIntros (Φ) "(Htxn & #Hinv & Hmdata & Hbufs & Hbufpre) HΦ".

Opaque struct.t.
  wp_call.
  wp_apply wp_new_slice. { repeat econstructor. }
  iIntros (blks) "Hblks".

  wp_apply wp_ref_to; [val_ty|].
  iIntros (blks_l) "Hblks_l".

  wp_pures.
  wp_apply wp_NewMap.
  iIntros (bufsByBlock) "HbufsByBlock".

  wp_apply wp_ref_to; [val_ty|].
  iIntros (bufsByBlock_l) "HbufsByBlock_l".

  wp_pures.
  wp_apply (wp_forSliceEach with "[] [Hbufs]").
  2: {
    iDestruct (is_slice_to_small with "Hbufs") as "Hbufs".
    iFrame.
    admit.
  }
Admitted.

Theorem wp_txn__doCommit l q gData bufs buflist :
  {{{ is_txn l gData ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ list] _ ↦ bufptrval ∈ buflist,
        ∃ (bufptr : loc) a buf v0,
          ⌜ bufptrval = #bufptr ⌝ ∗
          is_buf bufptr a buf ∗
          @mapsto_txn buf.(bufKind) gData a v0
  }}}
    Txn__doCommit #l (slice_val bufs)
  {{{ (commitpos : u64) (ok : bool), RET (#commitpos, #ok);
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ list] _ ↦ bufptrval ∈ buflist,
        ∃ (bufptr : loc) a buf,
          ⌜ bufptrval = #bufptr ⌝ ∗
          is_buf bufptr a buf ∗
          mapsto_txn gData a buf.(bufData)
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hbufs & Hbufpre) HΦ".
  iDestruct (is_txn_dup with "Htxn") as "[Htxn0 Htxn]".
  iDestruct "Htxn" as (γMaps γLock walHeap mu walptr tq) "(Hl & Hwalptr & #Hwal & #Hinv & #Hlock)".

  wp_call.
  wp_loadField.
  wp_apply acquire_spec; eauto.
  iIntros "[Hlocked Htxnlocked]".

  wp_pures.
  iDestruct "Htxnlocked" as (mData nextId pos) "(Hmdata & Hnextid & Hpos)".
  wp_apply (wp_txn__installBufs with "[$Htxn0 $Hinv $Hmdata $Hbufs Hbufpre]").
  { admit. }

  iIntros (blks blklist) "(Hmdata & Hblks & Hpost & Hbufs & Hbufpre)".
  wp_pures.
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.
  wp_apply (wp_Walog__MemAppend with "[$Hwal $Hblks Hpost]").
  { iApply wal_heap_memappend.
    admit. }

  iIntros (npos ok) "Hnpos".
  wp_pures.
  wp_storeField.
  wp_loadField.
  wp_apply (release_spec with "[$Hlock $Hlocked Hnextid Hmdata Hpos]").
  { iExists _, _, _. iFrame. }

  wp_pures.
  iApply "HΦ".
  iFrame "Hbufs".
Admitted.

Theorem wp_txn_CommitWait l q gData bufs buflist (wait : bool) (id : u64) :
  {{{ is_txn l gData ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ list] _ ↦ bufptrval ∈ buflist,
        ∃ (bufptr : loc) a buf v0,
          ⌜ bufptrval = #bufptr ⌝ ∗
          is_buf bufptr a buf ∗
          @mapsto_txn buf.(bufKind) gData a v0
  }}}
    Txn__CommitWait #l (slice_val bufs) #wait #id
  {{{ (ok : bool), RET #ok;
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ list] _ ↦ bufptrval ∈ buflist,
        ∃ (bufptr : loc) a buf,
          ⌜ bufptrval = #bufptr ⌝ ∗
          is_buf bufptr a buf ∗
          mapsto_txn gData a buf.(bufData)
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hbufs & Hbufpre) HΦ".

  wp_call.
  wp_apply wp_ref_to; [val_ty|].
  iIntros (commit) "Hcommit".
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.
  rewrite bool_decide_decide.
  destruct (decide (int.val 0 < int.val bufs.(Slice.sz))).
  - wp_pures.
    wp_apply (wp_txn__doCommit with "[$Htxn $Hbufs $Hbufpre]").
    iIntros (commitpos ok) "[Hq Hbufpost]".

    wp_pures.
    destruct ok.
    + wp_pures.
      destruct wait.
      * wp_pures.
        admit.
      * wp_pures.
        iDestruct (struct_mapsto_singleton with "Hcommit") as "Hcommit"; eauto.
        wp_apply (wp_load with "Hcommit"); iIntros "Hcommit".
        iApply "HΦ".
        iFrame.

    + wp_pures.
      wp_apply util_proof.wp_DPrintf.
      wp_pures.
      iDestruct (struct_mapsto_singleton with "Hcommit") as "Hcommit"; eauto.
      wp_apply (wp_store with "Hcommit"); iIntros "Hcommit".
      wp_pures.
      wp_apply (wp_load with "Hcommit"); iIntros "Hcommit".
      iApply "HΦ".
      iFrame.

  - wp_pures.
    wp_apply util_proof.wp_DPrintf.
    wp_pures.
    iDestruct (struct_mapsto_singleton with "Hcommit") as "Hcommit"; eauto.
    wp_apply (wp_load with "Hcommit"); iIntros "Hcommit".
    iApply "HΦ".

    iDestruct (is_slice_sz with "Hbufs") as %Hbuflistlen.
    iFrame.

    destruct buflist.
    { simpl; eauto. }

    exfalso.
    simpl in Hbuflistlen.
    revert Hbuflistlen.
    revert n.
    word.
Admitted.

Theorem wp_Txn__GetTransId l gData :
  {{{ is_txn l gData }}}
    txn.Txn__GetTransId #l
  {{{ (i : u64), RET #i; emp }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iDestruct "Htxn" as (γMaps γLock walHeap mu walptr tq) "(Hl & Hwalptr & #Hwal & #Hinv & #Hlock)".
  wp_call.
  wp_loadField.
  wp_apply acquire_spec; eauto.
  iIntros "[Hlocked Htxnlocked]".
  iDestruct "Htxnlocked" as (? nextId pos) "(Htxnheap & Hnextid & Hpos)".
  wp_loadField.
  wp_apply wp_ref_to; eauto.
  iIntros (id) "Hid".
  wp_pures.
  iDestruct (struct_mapsto_singleton with "Hid") as "Hid"; eauto.
  wp_apply (wp_load with "Hid"); iIntros "Hid".
  wp_pures.
  destruct (bool_decide (#nextId = #0)); wp_pures.
  - wp_loadField.
    wp_storeField.
    wp_apply (wp_store with "Hid"); iIntros "Hid".
    wp_loadField.
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[$Hlock $Hlocked Htxnheap Hnextid Hpos]").
    {
      iExists _, _, _. iFrame.
    }
    wp_apply (wp_load with "Hid"); iIntros "Hid".
    iApply "HΦ". done.
  - wp_loadField.
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[$Hlock $Hlocked Htxnheap Hnextid Hpos]").
    {
      iExists _, _, _. iFrame.
    }
    wp_apply (wp_load with "Hid"); iIntros "Hid".
    iApply "HΦ". done.
Qed.

End heap.

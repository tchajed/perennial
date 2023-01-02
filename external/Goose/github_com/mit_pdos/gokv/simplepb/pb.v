(* autogenerated from github.com/mit-pdos/gokv/simplepb/pb *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.
From Goose Require github_com.mit_pdos.gokv.reconnectclient.
From Goose Require github_com.mit_pdos.gokv.simplepb.e.
From Goose Require github_com.mit_pdos.gokv.urpc.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* 0_marshal.go *)

Definition Op: ty := slice.T byteT.

Definition ApplyAsBackupArgs := struct.decl [
  "epoch" :: uint64T;
  "index" :: uint64T;
  "op" :: slice.T byteT
].

Definition EncodeApplyAsBackupArgs: val :=
  rec: "EncodeApplyAsBackupArgs" "args" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + #8 + slice.len (struct.loadF ApplyAsBackupArgs "op" "args"))) in
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF ApplyAsBackupArgs "epoch" "args");;
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF ApplyAsBackupArgs "index" "args");;
    "enc" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "enc") (struct.loadF ApplyAsBackupArgs "op" "args");;
    ![slice.T byteT] "enc".

Definition DecodeApplyAsBackupArgs: val :=
  rec: "DecodeApplyAsBackupArgs" "enc_args" :=
    let: "enc" := ref_to (slice.T byteT) "enc_args" in
    let: "args" := struct.alloc ApplyAsBackupArgs (zero_val (struct.t ApplyAsBackupArgs)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF ApplyAsBackupArgs "epoch" "args" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF ApplyAsBackupArgs "index" "args" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    struct.storeF ApplyAsBackupArgs "op" "args" (![slice.T byteT] "enc");;
    "args".

Definition SetStateArgs := struct.decl [
  "Epoch" :: uint64T;
  "NextIndex" :: uint64T;
  "State" :: slice.T byteT
].

Definition EncodeSetStateArgs: val :=
  rec: "EncodeSetStateArgs" "args" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + slice.len (struct.loadF SetStateArgs "State" "args"))) in
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF SetStateArgs "Epoch" "args");;
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF SetStateArgs "NextIndex" "args");;
    "enc" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "enc") (struct.loadF SetStateArgs "State" "args");;
    ![slice.T byteT] "enc".

Definition DecodeSetStateArgs: val :=
  rec: "DecodeSetStateArgs" "enc_args" :=
    let: "enc" := ref_to (slice.T byteT) "enc_args" in
    let: "args" := struct.alloc SetStateArgs (zero_val (struct.t SetStateArgs)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF SetStateArgs "Epoch" "args" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF SetStateArgs "NextIndex" "args" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    struct.storeF SetStateArgs "State" "args" (![slice.T byteT] "enc");;
    "args".

Definition GetStateArgs := struct.decl [
  "Epoch" :: uint64T
].

Definition EncodeGetStateArgs: val :=
  rec: "EncodeGetStateArgs" "args" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 #8) in
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF GetStateArgs "Epoch" "args");;
    ![slice.T byteT] "enc".

Definition DecodeGetStateArgs: val :=
  rec: "DecodeGetStateArgs" "enc" :=
    let: "args" := struct.alloc GetStateArgs (zero_val (struct.t GetStateArgs)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt "enc" in
    struct.storeF GetStateArgs "Epoch" "args" "0_ret";;
    "1_ret";;
    "args".

Definition GetStateReply := struct.decl [
  "Err" :: uint64T;
  "NextIndex" :: uint64T;
  "State" :: slice.T byteT
].

Definition EncodeGetStateReply: val :=
  rec: "EncodeGetStateReply" "reply" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + slice.len (struct.loadF GetStateReply "State" "reply"))) in
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF GetStateReply "Err" "reply");;
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF GetStateReply "NextIndex" "reply");;
    "enc" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "enc") (struct.loadF GetStateReply "State" "reply");;
    ![slice.T byteT] "enc".

Definition DecodeGetStateReply: val :=
  rec: "DecodeGetStateReply" "enc_reply" :=
    let: "enc" := ref_to (slice.T byteT) "enc_reply" in
    let: "reply" := struct.alloc GetStateReply (zero_val (struct.t GetStateReply)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF GetStateReply "Err" "reply" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF GetStateReply "NextIndex" "reply" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    struct.storeF GetStateReply "State" "reply" (![slice.T byteT] "enc");;
    "reply".

Definition BecomePrimaryArgs := struct.decl [
  "Epoch" :: uint64T;
  "Replicas" :: slice.T uint64T
].

Definition EncodeBecomePrimaryArgs: val :=
  rec: "EncodeBecomePrimaryArgs" "args" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + #8 + #8 * slice.len (struct.loadF BecomePrimaryArgs "Replicas" "args"))) in
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF BecomePrimaryArgs "Epoch" "args");;
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (slice.len (struct.loadF BecomePrimaryArgs "Replicas" "args"));;
    ForSlice uint64T <> "h" (struct.loadF BecomePrimaryArgs "Replicas" "args")
      ("enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") "h");;
    ![slice.T byteT] "enc".

Definition DecodeBecomePrimaryArgs: val :=
  rec: "DecodeBecomePrimaryArgs" "enc_args" :=
    let: "enc" := ref_to (slice.T byteT) "enc_args" in
    let: "args" := struct.alloc BecomePrimaryArgs (zero_val (struct.t BecomePrimaryArgs)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF BecomePrimaryArgs "Epoch" "args" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: "replicasLen" := ref (zero_val uint64T) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "replicasLen" <-[uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    struct.storeF BecomePrimaryArgs "Replicas" "args" (NewSlice uint64T (![uint64T] "replicasLen"));;
    ForSlice uint64T "i" <> (struct.loadF BecomePrimaryArgs "Replicas" "args")
      (let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
      SliceSet uint64T (struct.loadF BecomePrimaryArgs "Replicas" "args") "i" "0_ret";;
      "enc" <-[slice.T byteT] "1_ret");;
    "args".

Definition ApplyReply := struct.decl [
  "Err" :: uint64T;
  "Reply" :: slice.T byteT
].

Definition EncodeApplyReply: val :=
  rec: "EncodeApplyReply" "reply" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + slice.len (struct.loadF ApplyReply "Reply" "reply"))) in
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF ApplyReply "Err" "reply");;
    "enc" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "enc") (struct.loadF ApplyReply "Reply" "reply");;
    ![slice.T byteT] "enc".

Definition DecodeApplyReply: val :=
  rec: "DecodeApplyReply" "enc_reply" :=
    let: "enc" := ref_to (slice.T byteT) "enc_reply" in
    let: "reply" := struct.alloc ApplyReply (zero_val (struct.t ApplyReply)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF ApplyReply "Err" "reply" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    struct.storeF ApplyReply "Reply" "reply" (![slice.T byteT] "enc");;
    "reply".

Definition RoApplyAsBackupArgs := struct.decl [
  "epoch" :: uint64T;
  "nextIndex" :: uint64T
].

Definition EncodeRoApplyAsBackupArgs: val :=
  rec: "EncodeRoApplyAsBackupArgs" "args" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + #8)) in
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF RoApplyAsBackupArgs "epoch" "args");;
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF RoApplyAsBackupArgs "nextIndex" "args");;
    ![slice.T byteT] "enc".

Definition DecodeRoApplyAsBackupArgs: val :=
  rec: "DecodeRoApplyAsBackupArgs" "enc_reply" :=
    let: "enc" := ref_to (slice.T byteT) "enc_reply" in
    let: "args" := struct.alloc RoApplyAsBackupArgs (zero_val (struct.t RoApplyAsBackupArgs)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF RoApplyAsBackupArgs "epoch" "args" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    struct.storeF RoApplyAsBackupArgs "nextIndex" "args" "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    "args".

(* 1_statemachine.go *)

Definition StateMachine := struct.decl [
  "StartApply" :: (Op -> (slice.T byteT * (unitT -> unitT)%ht))%ht;
  "ApplyReadonly" :: (Op -> slice.T byteT)%ht;
  "SetStateAndUnseal" :: (slice.T byteT -> uint64T -> uint64T -> unitT)%ht;
  "GetStateAndSeal" :: (unitT -> slice.T byteT)%ht
].

Definition SyncStateMachine := struct.decl [
  "Apply" :: (Op -> slice.T byteT)%ht;
  "ApplyReadonly" :: (Op -> slice.T byteT)%ht;
  "SetStateAndUnseal" :: (slice.T byteT -> uint64T -> uint64T -> unitT)%ht;
  "GetStateAndSeal" :: (unitT -> slice.T byteT)%ht
].

(* clerk.go *)

Definition Clerk := struct.decl [
  "cl" :: ptrT
].

Definition RPC_APPLYASBACKUP : expr := #0.

Definition RPC_SETSTATE : expr := #1.

Definition RPC_GETSTATE : expr := #2.

Definition RPC_BECOMEPRIMARY : expr := #3.

Definition RPC_PRIMARYAPPLY : expr := #4.

Definition RPC_ROAPPLYASBACKUP : expr := #5.

Definition RPC_ROPRIMARYAPPLY : expr := #6.

Definition MakeClerk: val :=
  rec: "MakeClerk" "host" :=
    struct.new Clerk [
      "cl" ::= reconnectclient.MakeReconnectingClient "host"
    ].

Definition Clerk__ApplyAsBackup: val :=
  rec: "Clerk__ApplyAsBackup" "ck" "args" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "err" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" "ck") RPC_APPLYASBACKUP (EncodeApplyAsBackupArgs "args") "reply" #1000 in
    (if: "err" ≠ #0
    then e.Timeout
    else e.DecodeError (![slice.T byteT] "reply")).

Definition Clerk__SetState: val :=
  rec: "Clerk__SetState" "ck" "args" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "err" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" "ck") RPC_SETSTATE (EncodeSetStateArgs "args") "reply" #1000 in
    (if: "err" ≠ #0
    then e.Timeout
    else e.DecodeError (![slice.T byteT] "reply")).

Definition Clerk__GetState: val :=
  rec: "Clerk__GetState" "ck" "args" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "err" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" "ck") RPC_GETSTATE (EncodeGetStateArgs "args") "reply" #10000 in
    (if: "err" ≠ #0
    then
      struct.new GetStateReply [
        "Err" ::= e.Timeout
      ]
    else DecodeGetStateReply (![slice.T byteT] "reply")).

Definition Clerk__BecomePrimary: val :=
  rec: "Clerk__BecomePrimary" "ck" "args" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "err" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" "ck") RPC_BECOMEPRIMARY (EncodeBecomePrimaryArgs "args") "reply" #100 in
    (if: "err" ≠ #0
    then e.Timeout
    else e.DecodeError (![slice.T byteT] "reply")).

Definition Clerk__Apply: val :=
  rec: "Clerk__Apply" "ck" "op" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "err" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" "ck") RPC_PRIMARYAPPLY "op" "reply" #5000 in
    (if: ("err" = #0)
    then
      let: "r" := DecodeApplyReply (![slice.T byteT] "reply") in
      (struct.loadF ApplyReply "Err" "r", struct.loadF ApplyReply "Reply" "r")
    else (e.Timeout, slice.nil)).

Definition Clerk__RoApplyAsBackup: val :=
  rec: "Clerk__RoApplyAsBackup" "ck" "args" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "err" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" "ck") RPC_ROAPPLYASBACKUP (EncodeRoApplyAsBackupArgs "args") "reply" #1000 in
    (if: "err" ≠ #0
    then e.Timeout
    else e.DecodeError (![slice.T byteT] "reply")).

Definition Clerk__ApplyRo: val :=
  rec: "Clerk__ApplyRo" "ck" "op" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "err" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" "ck") RPC_ROPRIMARYAPPLY "op" "reply" #5000 in
    (if: ("err" = #0)
    then
      let: "r" := DecodeApplyReply (![slice.T byteT] "reply") in
      (struct.loadF ApplyReply "Err" "r", struct.loadF ApplyReply "Reply" "r")
    else (e.Timeout, slice.nil)).

(* server.go *)

Definition Server := struct.decl [
  "mu" :: ptrT;
  "epoch" :: uint64T;
  "sealed" :: boolT;
  "sm" :: ptrT;
  "nextIndex" :: uint64T;
  "isPrimary" :: boolT;
  "clerks" :: slice.T (slice.T ptrT);
  "opAppliedConds" :: mapT ptrT;
  "durableNextIndex" :: uint64T;
  "durableNextIndex_cond" :: ptrT;
  "committedNextIndex" :: uint64T;
  "nextRoIndex" :: uint64T;
  "roOpsToPropose_cond" :: ptrT;
  "committedNextRoIndex" :: uint64T;
  "committedNextRoIndex_cond" :: ptrT
].

Definition Server__RoApplyAsBackup: val :=
  rec: "Server__RoApplyAsBackup" "s" "args" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ((struct.loadF RoApplyAsBackupArgs "nextIndex" "args" > struct.loadF Server "durableNextIndex" "s") && (struct.loadF Server "epoch" "s" = struct.loadF RoApplyAsBackupArgs "epoch" "args")) && (struct.loadF Server "sealed" "s" = #false)
      then
        lock.condWait (struct.loadF Server "durableNextIndex_cond" "s");;
        Continue
      else Break));;
    (if: struct.loadF Server "epoch" "s" ≠ struct.loadF RoApplyAsBackupArgs "epoch" "args"
    then
      lock.release (struct.loadF Server "mu" "s");;
      e.Stale
    else
      (if: struct.loadF Server "sealed" "s"
      then
        lock.release (struct.loadF Server "mu" "s");;
        e.Sealed
      else
        (if: struct.loadF RoApplyAsBackupArgs "nextIndex" "args" > struct.loadF Server "durableNextIndex" "s"
        then control.impl.Assert #false
        else #());;
        lock.release (struct.loadF Server "mu" "s");;
        e.None)).

(* This commits read-only operations. This is only necessary if RW operations
   are not being applied. If RW ops are being applied, they will implicitly
   commit RO ops. *)
Definition Server__applyRoThread: val :=
  rec: "Server__applyRoThread" "s" "epoch" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      Skip;;
      (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        (if: (struct.loadF Server "epoch" "s" ≠ "epoch") || ((struct.loadF Server "nextRoIndex" "s" ≠ struct.loadF Server "committedNextRoIndex" "s") && (struct.loadF Server "nextIndex" "s" = struct.loadF Server "durableNextIndex" "s"))
        then Break
        else
          lock.condWait (struct.loadF Server "roOpsToPropose_cond" "s");;
          Continue));;
      (if: struct.loadF Server "epoch" "s" ≠ "epoch"
      then
        lock.release (struct.loadF Server "mu" "s");;
        Break
      else
        let: "nextIndex" := struct.loadF Server "nextIndex" "s" in
        let: "nextRoIndex" := struct.loadF Server "nextRoIndex" "s" in
        let: "clerks" := SliceGet (slice.T ptrT) (struct.loadF Server "clerks" "s") ((Data.randomUint64 #()) `rem` (slice.len (struct.loadF Server "clerks" "s"))) in
        lock.release (struct.loadF Server "mu" "s");;
        let: "wg" := waitgroup.New #() in
        let: "args" := struct.new RoApplyAsBackupArgs [
          "epoch" ::= "epoch";
          "nextIndex" ::= "nextIndex"
        ] in
        let: "errs" := NewSlice uint64T (slice.len "clerks") in
        ForSlice ptrT "i" "clerk" "clerks"
          (let: "i" := "i" in
          let: "clerk" := "clerk" in
          waitgroup.Add "wg" #1;;
          Fork (Skip;;
                (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
                  let: "err" := Clerk__RoApplyAsBackup "clerk" "args" in
                  (if: ("err" = e.OutOfOrder) || ("err" = e.Timeout)
                  then Continue
                  else
                    SliceSet uint64T "errs" "i" "err";;
                    Break));;
                waitgroup.Done "wg"));;
        waitgroup.Wait "wg";;
        let: "err" := ref_to uint64T e.None in
        let: "i" := ref_to uint64T #0 in
        Skip;;
        (for: (λ: <>, ![uint64T] "i" < slice.len "errs"); (λ: <>, Skip) := λ: <>,
          let: "err2" := SliceGet uint64T "errs" (![uint64T] "i") in
          (if: "err2" ≠ e.None
          then "err" <-[uint64T] "err2"
          else #());;
          "i" <-[uint64T] ![uint64T] "i" + #1;;
          Continue);;
        (if: ![uint64T] "err" ≠ e.None
        then
          lock.acquire (struct.loadF Server "mu" "s");;
          (* log.Printf("applyRoThread() exited because of non-retryable RPC error") *)
          control.impl.Assume #false;;
          lock.release (struct.loadF Server "mu" "s");;
          Break
        else
          lock.acquire (struct.loadF Server "mu" "s");;
          (if: (struct.loadF Server "epoch" "s" = "epoch") && (struct.loadF Server "nextIndex" "s" = "nextIndex")
          then
            struct.storeF Server "committedNextRoIndex" "s" "nextRoIndex";;
            lock.condBroadcast (struct.loadF Server "committedNextRoIndex_cond" "s");;
            Continue
          else Continue))));;
    #().

Definition Server__ApplyRo: val :=
  rec: "Server__ApplyRo" "s" "op" :=
    let: "reply" := struct.alloc ApplyReply (zero_val (struct.t ApplyReply)) in
    struct.storeF ApplyReply "Reply" "reply" slice.nil;;
    lock.acquire (struct.loadF Server "mu" "s");;
    (if: ~ (struct.loadF Server "isPrimary" "s")
    then
      lock.release (struct.loadF Server "mu" "s");;
      struct.storeF ApplyReply "Err" "reply" e.Stale;;
      "reply"
    else
      (if: struct.loadF Server "sealed" "s"
      then
        lock.release (struct.loadF Server "mu" "s");;
        struct.storeF ApplyReply "Err" "reply" e.Stale;;
        "reply"
      else
        struct.storeF ApplyReply "Reply" "reply" (struct.loadF StateMachine "ApplyReadonly" (struct.loadF Server "sm" "s") "op");;
        struct.storeF Server "nextRoIndex" "s" (std.SumAssumeNoOverflow (struct.loadF Server "nextRoIndex" "s") #1);;
        let: "nextRoIndex" := struct.loadF Server "nextRoIndex" "s" in
        let: "nextIndex" := struct.loadF Server "nextIndex" "s" in
        let: "epoch" := struct.loadF Server "epoch" "s" in
        (if: (struct.loadF Server "nextIndex" "s" = struct.loadF Server "durableNextIndex" "s")
        then lock.condSignal (struct.loadF Server "roOpsToPropose_cond" "s")
        else #());;
        Skip;;
        (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
          (if: (("epoch" ≠ struct.loadF Server "epoch" "s") || (struct.loadF Server "committedNextIndex" "s" ≥ "nextIndex")) || (struct.loadF Server "committedNextRoIndex" "s" ≥ "nextRoIndex")
          then Break
          else
            lock.condWait (struct.loadF Server "committedNextRoIndex_cond" "s");;
            Continue));;
        lock.release (struct.loadF Server "mu" "s");;
        (if: "epoch" ≠ struct.loadF Server "epoch" "s"
        then
          struct.storeF ApplyReply "Err" "reply" e.Stale;;
          "reply"
        else
          struct.storeF ApplyReply "Err" "reply" e.None;;
          "reply"))).

(* called on the primary server to apply a new operation. *)
Definition Server__Apply: val :=
  rec: "Server__Apply" "s" "op" :=
    let: "reply" := struct.alloc ApplyReply (zero_val (struct.t ApplyReply)) in
    struct.storeF ApplyReply "Reply" "reply" slice.nil;;
    lock.acquire (struct.loadF Server "mu" "s");;
    (if: ~ (struct.loadF Server "isPrimary" "s")
    then
      lock.release (struct.loadF Server "mu" "s");;
      struct.storeF ApplyReply "Err" "reply" e.Stale;;
      "reply"
    else
      (if: struct.loadF Server "sealed" "s"
      then
        lock.release (struct.loadF Server "mu" "s");;
        struct.storeF ApplyReply "Err" "reply" e.Stale;;
        "reply"
      else
        let: ("ret", "waitForDurable") := struct.loadF StateMachine "StartApply" (struct.loadF Server "sm" "s") "op" in
        struct.storeF ApplyReply "Reply" "reply" "ret";;
        let: "nextIndex" := struct.loadF Server "nextIndex" "s" in
        struct.storeF Server "nextIndex" "s" (std.SumAssumeNoOverflow (struct.loadF Server "nextIndex" "s") #1);;
        let: "epoch" := struct.loadF Server "epoch" "s" in
        let: "clerks" := struct.loadF Server "clerks" "s" in
        struct.storeF Server "nextRoIndex" "s" #0;;
        struct.storeF Server "committedNextRoIndex" "s" #0;;
        lock.release (struct.loadF Server "mu" "s");;
        "waitForDurable" #();;
        let: "wg" := waitgroup.New #() in
        let: "args" := struct.new ApplyAsBackupArgs [
          "epoch" ::= "epoch";
          "index" ::= "nextIndex";
          "op" ::= "op"
        ] in
        let: "clerks_inner" := SliceGet (slice.T ptrT) "clerks" ((Data.randomUint64 #()) `rem` (slice.len "clerks")) in
        let: "errs" := NewSlice uint64T (slice.len "clerks_inner") in
        ForSlice ptrT "i" "clerk" "clerks_inner"
          (let: "clerk" := "clerk" in
          let: "i" := "i" in
          waitgroup.Add "wg" #1;;
          Fork (Skip;;
                (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
                  let: "err" := Clerk__ApplyAsBackup "clerk" "args" in
                  (if: ("err" = e.OutOfOrder) || ("err" = e.Timeout)
                  then Continue
                  else
                    SliceSet uint64T "errs" "i" "err";;
                    Break));;
                waitgroup.Done "wg"));;
        waitgroup.Wait "wg";;
        let: "err" := ref_to uint64T e.None in
        let: "i" := ref_to uint64T #0 in
        Skip;;
        (for: (λ: <>, ![uint64T] "i" < slice.len "clerks_inner"); (λ: <>, Skip) := λ: <>,
          let: "err2" := SliceGet uint64T "errs" (![uint64T] "i") in
          (if: "err2" ≠ e.None
          then "err" <-[uint64T] "err2"
          else #());;
          "i" <-[uint64T] ![uint64T] "i" + #1;;
          Continue);;
        struct.storeF ApplyReply "Err" "reply" (![uint64T] "err");;
        lock.acquire (struct.loadF Server "mu" "s");;
        (if: "nextIndex" > struct.loadF Server "committedNextIndex" "s"
        then
          struct.storeF Server "committedNextIndex" "s" "nextIndex";;
          struct.storeF Server "nextRoIndex" "s" #0;;
          struct.storeF Server "committedNextRoIndex" "s" #0;;
          lock.condBroadcast (struct.loadF Server "committedNextRoIndex_cond" "s")
        else #());;
        lock.release (struct.loadF Server "mu" "s");;
        "reply")).

(* requires that we've already at least entered this epoch
   returns true iff stale *)
Definition Server__isEpochStale: val :=
  rec: "Server__isEpochStale" "s" "epoch" :=
    struct.loadF Server "epoch" "s" ≠ "epoch".

(* called on backup servers to apply an operation so it is replicated and
   can be considered committed by primary. *)
Definition Server__ApplyAsBackup: val :=
  rec: "Server__ApplyAsBackup" "s" "args" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    Skip;;
    (for: (λ: <>, ((struct.loadF ApplyAsBackupArgs "index" "args" > struct.loadF Server "nextIndex" "s") && (struct.loadF Server "epoch" "s" = struct.loadF ApplyAsBackupArgs "epoch" "args")) && (~ (struct.loadF Server "sealed" "s"))); (λ: <>, Skip) := λ: <>,
      let: ("cond", "ok") := MapGet (struct.loadF Server "opAppliedConds" "s") (struct.loadF ApplyAsBackupArgs "index" "args") in
      (if: ~ "ok"
      then
        let: "cond" := lock.newCond (struct.loadF Server "mu" "s") in
        MapInsert (struct.loadF Server "opAppliedConds" "s") (struct.loadF ApplyAsBackupArgs "index" "args") "cond";;
        Continue
      else
        lock.condWait "cond";;
        Continue));;
    (if: struct.loadF Server "sealed" "s"
    then
      lock.release (struct.loadF Server "mu" "s");;
      e.Stale
    else
      (if: Server__isEpochStale "s" (struct.loadF ApplyAsBackupArgs "epoch" "args")
      then
        lock.release (struct.loadF Server "mu" "s");;
        e.Stale
      else
        (if: struct.loadF ApplyAsBackupArgs "index" "args" ≠ struct.loadF Server "nextIndex" "s"
        then
          lock.release (struct.loadF Server "mu" "s");;
          e.OutOfOrder
        else
          let: (<>, "waitFn") := struct.loadF StateMachine "StartApply" (struct.loadF Server "sm" "s") (struct.loadF ApplyAsBackupArgs "op" "args") in
          struct.storeF Server "nextIndex" "s" (struct.loadF Server "nextIndex" "s" + #1);;
          let: "opNextIndex" := struct.loadF Server "nextIndex" "s" in
          let: ("cond", "ok") := MapGet (struct.loadF Server "opAppliedConds" "s") (struct.loadF Server "nextIndex" "s") in
          (if: "ok"
          then
            lock.condSignal "cond";;
            MapDelete (struct.loadF Server "opAppliedConds" "s") (struct.loadF Server "nextIndex" "s")
          else #());;
          lock.release (struct.loadF Server "mu" "s");;
          "waitFn" #();;
          lock.acquire (struct.loadF Server "mu" "s");;
          (if: (struct.loadF ApplyAsBackupArgs "epoch" "args" = struct.loadF Server "epoch" "s") && ("opNextIndex" > struct.loadF Server "durableNextIndex" "s")
          then
            struct.storeF Server "durableNextIndex" "s" "opNextIndex";;
            lock.condBroadcast (struct.loadF Server "durableNextIndex_cond" "s");;
            (if: (struct.loadF Server "durableNextIndex" "s" = struct.loadF Server "nextIndex" "s") && (struct.loadF Server "nextRoIndex" "s" ≠ struct.loadF Server "committedNextRoIndex" "s")
            then lock.condSignal (struct.loadF Server "roOpsToPropose_cond" "s")
            else #())
          else #());;
          lock.release (struct.loadF Server "mu" "s");;
          e.None))).

Definition Server__SetState: val :=
  rec: "Server__SetState" "s" "args" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    (if: struct.loadF Server "epoch" "s" > struct.loadF SetStateArgs "Epoch" "args"
    then
      lock.release (struct.loadF Server "mu" "s");;
      e.Stale
    else
      (if: (struct.loadF Server "epoch" "s" = struct.loadF SetStateArgs "Epoch" "args")
      then
        lock.release (struct.loadF Server "mu" "s");;
        e.None
      else
        struct.storeF Server "isPrimary" "s" #false;;
        struct.storeF Server "epoch" "s" (struct.loadF SetStateArgs "Epoch" "args");;
        struct.storeF Server "sealed" "s" #false;;
        struct.storeF Server "nextIndex" "s" (struct.loadF SetStateArgs "NextIndex" "args");;
        struct.loadF StateMachine "SetStateAndUnseal" (struct.loadF Server "sm" "s") (struct.loadF SetStateArgs "State" "args") (struct.loadF SetStateArgs "NextIndex" "args") (struct.loadF SetStateArgs "Epoch" "args");;
        MapIter (struct.loadF Server "opAppliedConds" "s") (λ: <> "cond",
          lock.condSignal "cond");;
        struct.storeF Server "opAppliedConds" "s" (NewMap ptrT #());;
        lock.release (struct.loadF Server "mu" "s");;
        e.None)).

(* XXX: probably should rename to GetStateAndSeal *)
Definition Server__GetState: val :=
  rec: "Server__GetState" "s" "args" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    (if: struct.loadF GetStateArgs "Epoch" "args" < struct.loadF Server "epoch" "s"
    then
      lock.release (struct.loadF Server "mu" "s");;
      struct.new GetStateReply [
        "Err" ::= e.Stale;
        "State" ::= slice.nil
      ]
    else
      struct.storeF Server "sealed" "s" #true;;
      let: "ret" := struct.loadF StateMachine "GetStateAndSeal" (struct.loadF Server "sm" "s") #() in
      let: "nextIndex" := struct.loadF Server "nextIndex" "s" in
      MapIter (struct.loadF Server "opAppliedConds" "s") (λ: <> "cond",
        lock.condSignal "cond");;
      struct.storeF Server "opAppliedConds" "s" (NewMap ptrT #());;
      lock.release (struct.loadF Server "mu" "s");;
      struct.new GetStateReply [
        "Err" ::= e.None;
        "State" ::= "ret";
        "NextIndex" ::= "nextIndex"
      ]).

Definition Server__BecomePrimary: val :=
  rec: "Server__BecomePrimary" "s" "args" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    (if: struct.loadF BecomePrimaryArgs "Epoch" "args" ≠ struct.loadF Server "epoch" "s"
    then
      (* log.Printf("Stale BecomePrimary request (in %d, got %d)", s.epoch, args.Epoch) *)
      lock.release (struct.loadF Server "mu" "s");;
      e.Stale
    else
      (* log.Println("Became Primary") *)
      struct.storeF Server "isPrimary" "s" #true;;
      let: "numClerks" := #32 in
      struct.storeF Server "clerks" "s" (NewSlice (slice.T ptrT) "numClerks");;
      let: "j" := ref_to uint64T #0 in
      Skip;;
      (for: (λ: <>, ![uint64T] "j" < "numClerks"); (λ: <>, Skip) := λ: <>,
        let: "clerks" := NewSlice ptrT (slice.len (struct.loadF BecomePrimaryArgs "Replicas" "args") - #1) in
        let: "i" := ref_to uint64T #0 in
        Skip;;
        (for: (λ: <>, ![uint64T] "i" < slice.len "clerks"); (λ: <>, Skip) := λ: <>,
          SliceSet ptrT "clerks" (![uint64T] "i") (MakeClerk (SliceGet uint64T (struct.loadF BecomePrimaryArgs "Replicas" "args") (![uint64T] "i" + #1)));;
          "i" <-[uint64T] ![uint64T] "i" + #1;;
          Continue);;
        SliceSet (slice.T ptrT) (struct.loadF Server "clerks" "s") (![uint64T] "j") "clerks";;
        "j" <-[uint64T] ![uint64T] "j" + #1;;
        Continue);;
      struct.storeF Server "nextRoIndex" "s" #0;;
      struct.storeF Server "committedNextRoIndex" "s" #0;;
      struct.storeF Server "committedNextIndex" "s" #0;;
      lock.release (struct.loadF Server "mu" "s");;
      let: "epoch" := struct.loadF BecomePrimaryArgs "Epoch" "args" in
      Fork (Server__applyRoThread "s" "epoch");;
      e.None).

Definition MakeServer: val :=
  rec: "MakeServer" "sm" "nextIndex" "epoch" "sealed" :=
    let: "s" := struct.alloc Server (zero_val (struct.t Server)) in
    struct.storeF Server "mu" "s" (lock.new #());;
    struct.storeF Server "epoch" "s" "epoch";;
    struct.storeF Server "sealed" "s" "sealed";;
    struct.storeF Server "sm" "s" "sm";;
    struct.storeF Server "nextIndex" "s" "nextIndex";;
    struct.storeF Server "durableNextIndex" "s" "nextIndex";;
    struct.storeF Server "isPrimary" "s" #false;;
    struct.storeF Server "opAppliedConds" "s" (NewMap ptrT #());;
    struct.storeF Server "durableNextIndex_cond" "s" (lock.newCond (struct.loadF Server "mu" "s"));;
    struct.storeF Server "roOpsToPropose_cond" "s" (lock.newCond (struct.loadF Server "mu" "s"));;
    struct.storeF Server "committedNextRoIndex_cond" "s" (lock.newCond (struct.loadF Server "mu" "s"));;
    "s".

Definition Server__Serve: val :=
  rec: "Server__Serve" "s" "me" :=
    let: "handlers" := NewMap ((slice.T byteT -> ptrT -> unitT)%ht) #() in
    MapInsert "handlers" RPC_APPLYASBACKUP ((λ: "args" "reply",
      "reply" <-[slice.T byteT] e.EncodeError (Server__ApplyAsBackup "s" (DecodeApplyAsBackupArgs "args"));;
      #()
      ));;
    MapInsert "handlers" RPC_SETSTATE ((λ: "args" "reply",
      "reply" <-[slice.T byteT] e.EncodeError (Server__SetState "s" (DecodeSetStateArgs "args"));;
      #()
      ));;
    MapInsert "handlers" RPC_GETSTATE ((λ: "args" "reply",
      "reply" <-[slice.T byteT] EncodeGetStateReply (Server__GetState "s" (DecodeGetStateArgs "args"));;
      #()
      ));;
    MapInsert "handlers" RPC_BECOMEPRIMARY ((λ: "args" "reply",
      "reply" <-[slice.T byteT] e.EncodeError (Server__BecomePrimary "s" (DecodeBecomePrimaryArgs "args"));;
      #()
      ));;
    MapInsert "handlers" RPC_PRIMARYAPPLY ((λ: "args" "reply",
      "reply" <-[slice.T byteT] EncodeApplyReply (Server__Apply "s" "args");;
      #()
      ));;
    MapInsert "handlers" RPC_ROAPPLYASBACKUP ((λ: "args" "reply",
      "reply" <-[slice.T byteT] e.EncodeError (Server__RoApplyAsBackup "s" (DecodeRoApplyAsBackupArgs "args"));;
      #()
      ));;
    MapInsert "handlers" RPC_ROPRIMARYAPPLY ((λ: "args" "reply",
      "reply" <-[slice.T byteT] EncodeApplyReply (Server__ApplyRo "s" "args");;
      #()
      ));;
    let: "rs" := urpc.MakeServer "handlers" in
    urpc.Server__Serve "rs" "me";;
    #().

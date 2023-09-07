(* autogenerated from github.com/mit-pdos/gokv/simplepb/config2 *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.
From Goose Require github_com.mit_pdos.gokv.mpaxos.
From Goose Require github_com.mit_pdos.gokv.reconnectclient.
From Goose Require github_com.mit_pdos.gokv.simplepb.e.
From Goose Require github_com.mit_pdos.gokv.urpc.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* 0_marshal.go *)

Definition EncodeConfig: val :=
  rec: "EncodeConfig" "config" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + (#8 * (slice.len "config")))) in
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (slice.len "config"));;
    ForSlice uint64T <> "h" "config"
      ("enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") "h"));;
    ![slice.T byteT] "enc".

Definition DecodeConfig: val :=
  rec: "DecodeConfig" "enc_config" :=
    let: "enc" := ref_to (slice.T byteT) "enc_config" in
    let: "configLen" := ref (zero_val uint64T) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "configLen" <-[uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: "config" := NewSlice uint64T (![uint64T] "configLen") in
    let: "i" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (slice.len "config")); (λ: <>, Skip) := λ: <>,
      let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
      SliceSet uint64T "config" (![uint64T] "i") "0_ret";;
      "enc" <-[slice.T byteT] "1_ret";;
      "i" <-[uint64T] ((![uint64T] "i") + #1);;
      Continue);;
    "config".

(* client.go *)

Definition Clerk := struct.decl [
  "mu" :: ptrT;
  "cls" :: slice.T ptrT;
  "leader" :: uint64T
].

Definition RPC_RESERVEEPOCH : expr := #0.

Definition RPC_GETCONFIG : expr := #1.

Definition RPC_TRYWRITECONFIG : expr := #2.

Definition RPC_GETLEASE : expr := #3.

Definition MakeClerk: val :=
  rec: "MakeClerk" "hosts" :=
    let: "cls" := ref_to (slice.T ptrT) (NewSlice ptrT #0) in
    ForSlice uint64T <> "host" "hosts"
      ("cls" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "cls") (reconnectclient.MakeReconnectingClient "host")));;
    struct.new Clerk [
      "cls" ::= ![slice.T ptrT] "cls";
      "mu" ::= lock.new #()
    ].

Definition Clerk__ReserveEpochAndGetConfig: val :=
  rec: "Clerk__ReserveEpochAndGetConfig" "ck" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      lock.acquire (struct.loadF Clerk "mu" "ck");;
      let: "l" := struct.loadF Clerk "leader" "ck" in
      lock.release (struct.loadF Clerk "mu" "ck");;
      let: "err" := reconnectclient.ReconnectingClient__Call (SliceGet ptrT (struct.loadF Clerk "cls" "ck") "l") RPC_RESERVEEPOCH (NewSlice byteT #0) "reply" #100 in
      (if: "err" ≠ #0
      then Continue
      else
        let: "err2" := ref (zero_val uint64T) in
        let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "reply") in
        "err2" <-[uint64T] "0_ret";;
        "reply" <-[slice.T byteT] "1_ret";;
        (if: (![uint64T] "err2") = e.NotLeader
        then
          lock.acquire (struct.loadF Clerk "mu" "ck");;
          (if: "l" = (struct.loadF Clerk "leader" "ck")
          then struct.storeF Clerk "leader" "ck" (((struct.loadF Clerk "leader" "ck") + #1) `rem` (slice.len (struct.loadF Clerk "cls" "ck")))
          else #());;
          lock.release (struct.loadF Clerk "mu" "ck");;
          Continue
        else
          (if: (![uint64T] "err2") = e.None
          then Break
          else Continue))));;
    let: "epoch" := ref (zero_val uint64T) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "reply") in
    "epoch" <-[uint64T] "0_ret";;
    "reply" <-[slice.T byteT] "1_ret";;
    let: "config" := DecodeConfig (![slice.T byteT] "reply") in
    (![uint64T] "epoch", "config").

Definition Clerk__GetConfig: val :=
  rec: "Clerk__GetConfig" "ck" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "i" := (rand.RandomUint64 #()) `rem` (slice.len (struct.loadF Clerk "cls" "ck")) in
      let: "err" := reconnectclient.ReconnectingClient__Call (SliceGet ptrT (struct.loadF Clerk "cls" "ck") "i") RPC_GETCONFIG (NewSlice byteT #0) "reply" #100 in
      (if: "err" = #0
      then Break
      else Continue));;
    let: "config" := DecodeConfig (![slice.T byteT] "reply") in
    "config".

Definition Clerk__TryWriteConfig: val :=
  rec: "Clerk__TryWriteConfig" "ck" "epoch" "config" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "args" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + (#8 * (slice.len "config")))) in
    "args" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "args") "epoch");;
    "args" <-[slice.T byteT] (marshal.WriteBytes (![slice.T byteT] "args") (EncodeConfig "config"));;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      lock.acquire (struct.loadF Clerk "mu" "ck");;
      let: "l" := struct.loadF Clerk "leader" "ck" in
      lock.release (struct.loadF Clerk "mu" "ck");;
      let: "err" := reconnectclient.ReconnectingClient__Call (SliceGet ptrT (struct.loadF Clerk "cls" "ck") "l") RPC_TRYWRITECONFIG (![slice.T byteT] "args") "reply" #2000 in
      (if: "err" ≠ #0
      then Continue
      else
        let: ("err2", <>) := marshal.ReadInt (![slice.T byteT] "reply") in
        (if: "err2" = e.NotLeader
        then
          lock.acquire (struct.loadF Clerk "mu" "ck");;
          (if: "l" = (struct.loadF Clerk "leader" "ck")
          then struct.storeF Clerk "leader" "ck" (((struct.loadF Clerk "leader" "ck") + #1) `rem` (slice.len (struct.loadF Clerk "cls" "ck")))
          else #());;
          lock.release (struct.loadF Clerk "mu" "ck");;
          Continue
        else Break)));;
    let: ("err", <>) := marshal.ReadInt (![slice.T byteT] "reply") in
    "err".

(* returns e.None if the lease was granted for the given epoch, and a conservative
   guess on when the lease expires. *)
Definition Clerk__GetLease: val :=
  rec: "Clerk__GetLease" "ck" "epoch" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "args" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 #8) in
    "args" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "args") "epoch");;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      lock.acquire (struct.loadF Clerk "mu" "ck");;
      let: "l" := struct.loadF Clerk "leader" "ck" in
      lock.release (struct.loadF Clerk "mu" "ck");;
      let: "err" := reconnectclient.ReconnectingClient__Call (SliceGet ptrT (struct.loadF Clerk "cls" "ck") "l") RPC_GETLEASE (![slice.T byteT] "args") "reply" #100 in
      (if: "err" ≠ #0
      then Continue
      else
        let: ("err2", <>) := marshal.ReadInt (![slice.T byteT] "reply") in
        (if: "err2" = e.NotLeader
        then
          lock.acquire (struct.loadF Clerk "mu" "ck");;
          (if: "l" = (struct.loadF Clerk "leader" "ck")
          then struct.storeF Clerk "leader" "ck" (((struct.loadF Clerk "leader" "ck") + #1) `rem` (slice.len (struct.loadF Clerk "cls" "ck")))
          else #());;
          lock.release (struct.loadF Clerk "mu" "ck");;
          Continue
        else Break)));;
    let: ("err2", "enc") := marshal.ReadInt (![slice.T byteT] "reply") in
    let: ("leaseExpiration", <>) := marshal.ReadInt "enc" in
    ("err2", "leaseExpiration").

(* server.go *)

(* 1 second *)
Definition LeaseInterval : expr := #1000000000.

Definition state := struct.decl [
  "epoch" :: uint64T;
  "reservedEpoch" :: uint64T;
  "leaseExpiration" :: uint64T;
  "wantLeaseToExpire" :: boolT;
  "config" :: slice.T uint64T
].

Definition encodeState: val :=
  rec: "encodeState" "st" :=
    let: "e" := ref (zero_val (slice.T byteT)) in
    "e" <-[slice.T byteT] (marshal.WriteInt slice.nil (struct.loadF state "epoch" "st"));;
    "e" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "e") (struct.loadF state "reservedEpoch" "st"));;
    "e" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "e") (struct.loadF state "leaseExpiration" "st"));;
    (if: struct.loadF state "wantLeaseToExpire" "st"
    then "e" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "e") #1)
    else "e" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "e") #0));;
    "e" <-[slice.T byteT] (marshal.WriteBytes (![slice.T byteT] "e") (EncodeConfig (struct.loadF state "config" "st")));;
    ![slice.T byteT] "e".

Definition decodeState: val :=
  rec: "decodeState" "e" :=
    let: "st" := struct.alloc state (zero_val (struct.t state)) in
    let: "e2" := ref_to (slice.T byteT) "e" in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "e2") in
    struct.storeF state "epoch" "st" "0_ret";;
    "e2" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "e2") in
    struct.storeF state "reservedEpoch" "st" "0_ret";;
    "e2" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "e2") in
    struct.storeF state "leaseExpiration" "st" "0_ret";;
    "e2" <-[slice.T byteT] "1_ret";;
    let: "wantExp" := ref (zero_val uint64T) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "e2") in
    "wantExp" <-[uint64T] "0_ret";;
    "e2" <-[slice.T byteT] "1_ret";;
    (if: (![uint64T] "wantExp") ≠ #0
    then struct.storeF state "wantLeaseToExpire" "st" #true
    else #());;
    struct.storeF state "config" "st" (DecodeConfig (![slice.T byteT] "e2"));;
    "st".

Definition Server := struct.decl [
  "s" :: ptrT
].

Definition Server__tryAcquire: val :=
  rec: "Server__tryAcquire" "s" :=
    let: (("err", "e"), "relF") := mpaxos.Server__TryAcquire (struct.loadF Server "s" "s") in
    (if: "err" ≠ #0
    then
      let: "p" := ref (zero_val ptrT) in
      (#false, ![ptrT] "p", slice.nil)
    else
      let: "st" := decodeState (![slice.T byteT] "e") in
      let: "releaseFn" := (λ: <>,
        "e" <-[slice.T byteT] (encodeState "st");;
        ("relF" #()) = #0
        ) in
      (#true, "st", "releaseFn")).

Definition Server__ReserveEpochAndGetConfig: val :=
  rec: "Server__ReserveEpochAndGetConfig" "s" "args" "reply" :=
    "reply" <-[slice.T byteT] (marshal.WriteInt slice.nil e.NotLeader);;
    let: (("ok", "st"), "tryReleaseFn") := Server__tryAcquire "s" in
    (if: (~ "ok")
    then #()
    else
      struct.storeF state "reservedEpoch" "st" (std.SumAssumeNoOverflow (struct.loadF state "reservedEpoch" "st") #1);;
      let: "config" := struct.loadF state "config" "st" in
      let: "reservedEpoch" := struct.loadF state "reservedEpoch" "st" in
      (if: (~ ("tryReleaseFn" #()))
      then #()
      else
        "reply" <-[slice.T byteT] (NewSliceWithCap byteT #0 ((#8 + #8) + (#8 * (slice.len "config"))));;
        "reply" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "reply") e.None);;
        "reply" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "reply") "reservedEpoch");;
        "reply" <-[slice.T byteT] (marshal.WriteBytes (![slice.T byteT] "reply") (EncodeConfig "config"));;
        #())).

Definition Server__GetConfig: val :=
  rec: "Server__GetConfig" "s" "args" "reply" :=
    let: "st" := decodeState (mpaxos.Server__WeakRead (struct.loadF Server "s" "s")) in
    "reply" <-[slice.T byteT] (EncodeConfig (struct.loadF state "config" "st"));;
    #().

Definition Server__TryWriteConfig: val :=
  rec: "Server__TryWriteConfig" "s" "args" "reply" :=
    "reply" <-[slice.T byteT] (marshal.WriteInt slice.nil e.NotLeader);;
    let: ("epoch", "enc") := marshal.ReadInt "args" in
    let: "config" := DecodeConfig "enc" in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: (("ok", "st"), "tryReleaseFn") := Server__tryAcquire "s" in
      (if: (~ "ok")
      then Break
      else
        (if: "epoch" < (struct.loadF state "reservedEpoch" "st")
        then
          (if: (~ ("tryReleaseFn" #()))
          then Break
          else
            "reply" <-[slice.T byteT] (marshal.WriteInt slice.nil e.Stale);;
            (* log.Printf("Stale: %d < %d", epoch, st.reservedEpoch) *)
            Break)
        else
          (if: "epoch" > (struct.loadF state "epoch" "st")
          then
            let: ("l", <>) := grove_ffi.GetTimeRange #() in
            (if: "l" ≥ (struct.loadF state "leaseExpiration" "st")
            then
              struct.storeF state "wantLeaseToExpire" "st" #false;;
              struct.storeF state "epoch" "st" "epoch";;
              struct.storeF state "config" "st" "config";;
              (if: (~ ("tryReleaseFn" #()))
              then Break
              else
                (* log.Println("New config is:", st.config) *)
                "reply" <-[slice.T byteT] (marshal.WriteInt slice.nil e.None);;
                Break)
            else
              struct.storeF state "wantLeaseToExpire" "st" #true;;
              let: "timeToSleep" := (struct.loadF state "leaseExpiration" "st") - "l" in
              (if: (~ ("tryReleaseFn" #()))
              then Break
              else
                time.Sleep "timeToSleep";;
                Continue))
          else
            struct.storeF state "config" "st" "config";;
            (if: (~ ("tryReleaseFn" #()))
            then Break
            else
              "reply" <-[slice.T byteT] (marshal.WriteInt slice.nil e.None);;
              Break)))));;
    #().

Definition Server__GetLease: val :=
  rec: "Server__GetLease" "s" "args" "reply" :=
    "reply" <-[slice.T byteT] (marshal.WriteInt slice.nil e.NotLeader);;
    "reply" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "reply") #0);;
    let: ("epoch", <>) := marshal.ReadInt "args" in
    let: (("ok", "st"), "tryReleaseFn") := Server__tryAcquire "s" in
    (if: (~ "ok")
    then #()
    else
      (if: ((struct.loadF state "epoch" "st") ≠ "epoch") || (struct.loadF state "wantLeaseToExpire" "st")
      then
        (* log.Println("Rejected lease request", epoch, st.epoch, st.wantLeaseToExpire) *)
        (if: (~ ("tryReleaseFn" #()))
        then #()
        else
          "reply" <-[slice.T byteT] (marshal.WriteInt slice.nil e.Stale);;
          "reply" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "reply") #0);;
          #())
      else
        let: ("l", <>) := grove_ffi.GetTimeRange #() in
        let: "newLeaseExpiration" := "l" + LeaseInterval in
        (if: "newLeaseExpiration" > (struct.loadF state "leaseExpiration" "st")
        then struct.storeF state "leaseExpiration" "st" "newLeaseExpiration"
        else #());;
        (if: (~ ("tryReleaseFn" #()))
        then #()
        else
          "reply" <-[slice.T byteT] (marshal.WriteInt slice.nil e.None);;
          "reply" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "reply") "newLeaseExpiration");;
          #()))).

Definition makeServer: val :=
  rec: "makeServer" "fname" "paxosMe" "hosts" "initconfig" :=
    let: "s" := struct.alloc Server (zero_val (struct.t Server)) in
    let: "initEnc" := EncodeConfig "initconfig" in
    struct.storeF Server "s" "s" (mpaxos.StartServer "fname" "initEnc" "paxosMe" "hosts");;
    "s".

Definition StartServer: val :=
  rec: "StartServer" "fname" "me" "paxosMe" "hosts" "initconfig" :=
    let: "s" := makeServer "fname" "paxosMe" "hosts" "initconfig" in
    let: "handlers" := NewMap uint64T ((slice.T byteT) -> ptrT -> unitT)%ht #() in
    MapInsert "handlers" RPC_RESERVEEPOCH (Server__ReserveEpochAndGetConfig "s");;
    MapInsert "handlers" RPC_GETCONFIG (Server__GetConfig "s");;
    MapInsert "handlers" RPC_TRYWRITECONFIG (Server__TryWriteConfig "s");;
    MapInsert "handlers" RPC_GETLEASE (Server__GetLease "s");;
    let: "rs" := urpc.MakeServer "handlers" in
    urpc.Server__Serve "rs" "me";;
    "s".

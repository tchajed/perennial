(* autogenerated from github.com/mit-pdos/gokv/simplepb/simplelog *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.gokv.aof.
From Goose Require github_com.mit_pdos.gokv.simplepb.pb.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition InMemoryStateMachine := struct.decl [
  "ApplyVolatile" :: (slice.T byteT -> slice.T byteT)%ht;
  "GetState" :: (unitT -> slice.T byteT)%ht;
  "SetState" :: (slice.T byteT -> unitT)%ht
].

Definition appendOp: val :=
  rec: "appendOp" "fname" "op" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + slice.len "op")) in
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (slice.len "op");;
    "enc" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "enc") "op";;
    grove_ffi.AtomicAppend "fname" (![slice.T byteT] "enc");;
    #().

Definition MAX_LOG_SIZE : expr := #64 * #1024 * #1024 * #1024.

(* File format:
   [N]u8: snapshot
   u64:   epoch
   u64:   nextIndex
   [*]op: ops in the format (op length ++ op)
   ?u8:    sealed; this is only present if the state is sealed in this epoch *)
Definition StateMachine := struct.decl [
  "fname" :: stringT;
  "logFile" :: ptrT;
  "logsize" :: uint64T;
  "sealed" :: boolT;
  "epoch" :: uint64T;
  "nextIndex" :: uint64T;
  "smMem" :: ptrT
].

(* FIXME: better name; this isn't the same as "MakeDurable" *)
Definition StateMachine__makeDurableWithSnap: val :=
  rec: "StateMachine__makeDurableWithSnap" "s" "snap" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + slice.len "snap" + #8 + #8)) in
    marshal.WriteInt (![slice.T byteT] "enc") (slice.len "snap");;
    marshal.WriteBytes (![slice.T byteT] "enc") "snap";;
    marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF StateMachine "epoch" "s");;
    marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF StateMachine "nextIndex" "s");;
    (if: struct.loadF StateMachine "sealed" "s"
    then marshal.WriteBytes (![slice.T byteT] "enc") (NewSlice byteT #1)
    else #());;
    grove_ffi.Write (struct.loadF StateMachine "fname" "s") (![slice.T byteT] "enc");;
    #().

(* XXX: this is not safe to run concurrently with apply() *)
Definition StateMachine__truncateAndMakeDurable: val :=
  rec: "StateMachine__truncateAndMakeDurable" "s" :=
    let: "snap" := struct.loadF InMemoryStateMachine "GetState" (struct.loadF StateMachine "smMem" "s") #() in
    StateMachine__makeDurableWithSnap "s" "snap";;
    #().

Definition StateMachine__apply: val :=
  rec: "StateMachine__apply" "s" "op" :=
    let: "ret" := struct.loadF InMemoryStateMachine "ApplyVolatile" (struct.loadF StateMachine "smMem" "s") "op" in
    struct.storeF StateMachine "nextIndex" "s" (struct.loadF StateMachine "nextIndex" "s" + #1);;
    struct.storeF StateMachine "logsize" "s" (struct.loadF StateMachine "logsize" "s" + slice.len "op");;
    (if: struct.loadF StateMachine "logsize" "s" > MAX_LOG_SIZE
    then
      Panic ("unsupported when using aof");;
      #()
    else
      let: "l" := aof.AppendOnlyFile__Append (struct.loadF StateMachine "logFile" "s") "op" in
      let: "waitFn" := (λ: <>,
        aof.AppendOnlyFile__WaitAppend (struct.loadF StateMachine "logFile" "s") "l";;
        #()
        ) in
      ("ret", "waitFn")).

Definition StateMachine__setStateAndUnseal: val :=
  rec: "StateMachine__setStateAndUnseal" "s" "snap" "nextIndex" "epoch" :=
    struct.storeF StateMachine "epoch" "s" "epoch";;
    struct.storeF StateMachine "nextIndex" "s" "nextIndex";;
    struct.storeF StateMachine "sealed" "s" #false;;
    struct.loadF InMemoryStateMachine "SetState" (struct.loadF StateMachine "smMem" "s") "snap";;
    StateMachine__makeDurableWithSnap "s" "snap";;
    #().

Definition StateMachine__getStateAndSeal: val :=
  rec: "StateMachine__getStateAndSeal" "s" :=
    (if: ~ (struct.loadF StateMachine "sealed" "s")
    then
      struct.storeF StateMachine "sealed" "s" #true;;
      grove_ffi.AtomicAppend (struct.loadF StateMachine "fname" "s") (NewSlice byteT #1)
    else #());;
    let: "snap" := struct.loadF InMemoryStateMachine "GetState" (struct.loadF StateMachine "smMem" "s") #() in
    "snap".

Definition recoverStateMachine: val :=
  rec: "recoverStateMachine" "smMem" "fname" :=
    let: "s" := struct.new StateMachine [
      "fname" ::= "fname";
      "smMem" ::= "smMem"
    ] in
    let: "enc" := ref_to (slice.T byteT) (grove_ffi.Read (struct.loadF StateMachine "fname" "s")) in
    struct.storeF StateMachine "logFile" "s" (aof.CreateAppendOnlyFile "fname");;
    (if: (slice.len (![slice.T byteT] "enc") = #0)
    then "s"
    else
      let: "snapLen" := ref (zero_val uint64T) in
      let: "snap" := ref (zero_val (slice.T byteT)) in
      let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
      "snapLen" <-[uint64T] "0_ret";;
      "enc" <-[slice.T byteT] "1_ret";;
      "snap" <-[slice.T byteT] SliceTake (![slice.T byteT] "enc") (![uint64T] "snapLen");;
      "enc" <-[slice.T byteT] SliceSkip byteT (![slice.T byteT] "enc") (![uint64T] "snapLen");;
      struct.loadF InMemoryStateMachine "SetState" (struct.loadF StateMachine "smMem" "s") (![slice.T byteT] "snap");;
      let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
      struct.storeF StateMachine "epoch" "s" "0_ret";;
      "enc" <-[slice.T byteT] "1_ret";;
      let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
      struct.storeF StateMachine "nextIndex" "s" "0_ret";;
      "enc" <-[slice.T byteT] "1_ret";;
      Skip;;
      (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        (if: slice.len (![slice.T byteT] "enc") > #1
        then
          let: "opLen" := ref (zero_val uint64T) in
          let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
          "opLen" <-[uint64T] "0_ret";;
          "enc" <-[slice.T byteT] "1_ret";;
          let: "op" := SliceTake (![slice.T byteT] "enc") (![uint64T] "opLen") in
          "enc" <-[slice.T byteT] SliceSkip byteT (![slice.T byteT] "enc") (![uint64T] "opLen");;
          struct.loadF InMemoryStateMachine "ApplyVolatile" (struct.loadF StateMachine "smMem" "s") "op";;
          Continue
        else Break));;
      (if: slice.len (![slice.T byteT] "enc") > #0
      then struct.storeF StateMachine "sealed" "s" #true
      else #());;
      "s").

(* XXX: putting this here because MakeServer takes nextIndex, epoch, and sealed
   as input, and the user of simplelog won't have access to the private fields
   index, epoch, etc.

   Maybe we should make those be a part of pb.StateMachine *)
Definition MakePbServer: val :=
  rec: "MakePbServer" "smMem" "fname" :=
    let: "s" := recoverStateMachine "smMem" "fname" in
    let: "sm" := struct.new pb.StateMachine [
      "StartApply" ::= StateMachine__apply "s";
      "SetStateAndUnseal" ::= StateMachine__setStateAndUnseal "s";
      "GetStateAndSeal" ::= StateMachine__getStateAndSeal "s"
    ] in
    pb.MakeServer "sm" (struct.loadF StateMachine "nextIndex" "s") (struct.loadF StateMachine "epoch" "s") (struct.loadF StateMachine "sealed" "s").

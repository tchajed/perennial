(* autogenerated from github.com/mit-pdos/goose-nfsd/super *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

From Goose Require github_com.mit_pdos.goose_nfsd.addr.
From Goose Require github_com.mit_pdos.goose_nfsd.common.

Module FsSuper.
  Definition S := struct.decl [
    "Disk" :: disk.Disk;
    "Size" :: uint64T;
    "nLog" :: uint64T;
    "NBlockBitmap" :: uint64T;
    "NInodeBitmap" :: uint64T;
    "nInodeBlk" :: uint64T;
    "Maxaddr" :: uint64T
  ].
End FsSuper.

Definition MkFsSuper: val :=
  rec: "MkFsSuper" "d" :=
    let: "sz" := disk.Size #() in
    let: "nblockbitmap" := "sz" `quot` common.NBITBLOCK + #1 in
    struct.new FsSuper.S [
      "Disk" ::= "d";
      "Size" ::= "sz";
      "nLog" ::= common.LOGSIZE;
      "NBlockBitmap" ::= "nblockbitmap";
      "NInodeBitmap" ::= common.NINODEBITMAP;
      "nInodeBlk" ::= (common.NINODEBITMAP * common.NBITBLOCK * common.INODESZ) `quot` disk.BlockSize;
      "Maxaddr" ::= "sz"
    ].

Definition FsSuper__MaxBnum: val :=
  rec: "FsSuper__MaxBnum" "fs" :=
    struct.loadF FsSuper.S "Maxaddr" "fs".

Definition FsSuper__BitmapBlockStart: val :=
  rec: "FsSuper__BitmapBlockStart" "fs" :=
    struct.loadF FsSuper.S "nLog" "fs".

Definition FsSuper__BitmapInodeStart: val :=
  rec: "FsSuper__BitmapInodeStart" "fs" :=
    FsSuper__BitmapBlockStart "fs" + struct.loadF FsSuper.S "NBlockBitmap" "fs".

Definition FsSuper__InodeStart: val :=
  rec: "FsSuper__InodeStart" "fs" :=
    FsSuper__BitmapInodeStart "fs" + struct.loadF FsSuper.S "NInodeBitmap" "fs".

Definition FsSuper__DataStart: val :=
  rec: "FsSuper__DataStart" "fs" :=
    FsSuper__InodeStart "fs" + struct.loadF FsSuper.S "nInodeBlk" "fs".

Definition FsSuper__Block2addr: val :=
  rec: "FsSuper__Block2addr" "fs" "blkno" :=
    addr.MkAddr "blkno" #0 common.NBITBLOCK.

Definition FsSuper__NInode: val :=
  rec: "FsSuper__NInode" "fs" :=
    struct.loadF FsSuper.S "nInodeBlk" "fs" * common.INODEBLK.

Definition FsSuper__Inum2Addr: val :=
  rec: "FsSuper__Inum2Addr" "fs" "inum" :=
    addr.MkAddr (FsSuper__InodeStart "fs" + "inum" `quot` common.INODEBLK) ("inum" `rem` common.INODEBLK * common.INODESZ * #8) (common.INODESZ * #8).

Definition FsSuper__DiskBlockSize: val :=
  rec: "FsSuper__DiskBlockSize" "fs" "addr" :=
    (struct.get addr.Addr.S "Sz" "addr" = common.NBITBLOCK).

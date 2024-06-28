(* autogenerated from github.com/tchajed/simplefs *)
From Perennial.goose_lang Require Import prelude.

From Perennial.goose_lang Require Import ffi.disk_prelude.

Definition Inum: ty := uint64T.

Definition ROOT_INUM : expr := #1.

Definition InodeType: ty := uint32T.

Definition Invalid : expr := #(U32 0).

Definition DirType : expr := #(U32 1).

Definition FileType : expr := #(U32 2).

Definition InodeType__IsValid: val :=
  rec: "InodeType__IsValid" "t" :=
    "t" ≠ Invalid.

Definition INODE_SIZE : expr := #128.

Definition INODES_PER_BLOCK : expr := disk.BlockSize `quot` INODE_SIZE.

(* autogenerated from github.com/tchajed/simplefs/alloc *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.tchajed.simplefs.
From Goose Require github_com.tchajed.simplefs.inode.
From Goose Require github_com.tchajed.simplefs.superblock.

From Perennial.goose_lang Require Import ffi.disk_prelude.

Definition BlockAllocator := struct.decl [
  "offset" :: uint64T;
  "bitmap" :: struct.t simplefs.Bitmap;
  "free" :: slice.T uint32T;
  "d" :: disk.Disk
].

Definition NewBlockAllocator: val :=
  rec: "NewBlockAllocator" "d" "sb" :=
    let: "num_bitmaps" := struct.loadF superblock.Superblock "DataBitmapBlocks" "sb" in
    let: "offset" := superblock.Superblock__DataBitmapStart "sb" in
    let: "bitmap_blks" := ref_to (slice.T (slice.T byteT)) (NewSliceWithCap disk.blockT #0 "num_bitmaps") in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < "num_bitmaps"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
      "bitmap_blks" <-[slice.T (slice.T byteT)] (SliceAppend (slice.T byteT) (![slice.T (slice.T byteT)] "bitmap_blks") (disk.Read ("offset" + (![uint64T] "i"))));;
      Continue);;
    let: "bitmap" := simplefs.NewBitmap (![slice.T (slice.T byteT)] "bitmap_blks") in
    let: "free" := ref_to (slice.T uint32T) (NewSlice uint32T #0) in
    let: "i" := ref_to uint32T #(U32 1) in
    (for: (λ: <>, (![uint32T] "i") < (to_u32 (struct.loadF superblock.Superblock "DataBlocks" "sb"))); (λ: <>, "i" <-[uint32T] ((![uint32T] "i") + #1)) := λ: <>,
      (if: (~ (simplefs.Bitmap__Get "bitmap" (to_u64 (![uint32T] "i"))))
      then
        "free" <-[slice.T uint32T] (SliceAppend uint32T (![slice.T uint32T] "free") (![uint32T] "i"));;
        Continue
      else Continue));;
    struct.mk BlockAllocator [
      "offset" ::= "offset";
      "bitmap" ::= "bitmap";
      "free" ::= ![slice.T uint32T] "free";
      "d" ::= "d"
    ].

Definition BlockAllocator__Alloc: val :=
  rec: "BlockAllocator__Alloc" "ba" :=
    (if: (slice.len (struct.loadF BlockAllocator "free" "ba")) = #0
    then (#(U32 0), #false)
    else
      let: "i" := SliceGet uint32T (struct.loadF BlockAllocator "free" "ba") ((slice.len (struct.loadF BlockAllocator "free" "ba")) - #1) in
      struct.storeF BlockAllocator "free" "ba" (SliceTake (struct.loadF BlockAllocator "free" "ba") ((slice.len (struct.loadF BlockAllocator "free" "ba")) - #1));;
      simplefs.Bitmap__Set (struct.loadF BlockAllocator "bitmap" "ba") (to_u64 "i");;
      disk.Write ((struct.loadF BlockAllocator "offset" "ba") + (simplefs.Bitmap__BlockNum (struct.loadF BlockAllocator "bitmap" "ba") (to_u64 "i"))) (simplefs.Bitmap__Block (struct.loadF BlockAllocator "bitmap" "ba") (to_u64 "i"));;
      ("i", #true)).

Definition BlockAllocator__Free: val :=
  rec: "BlockAllocator__Free" "ba" "i" :=
    (if: (~ (simplefs.Bitmap__Get (struct.loadF BlockAllocator "bitmap" "ba") (to_u64 "i")))
    then Panic "freeing free block"
    else #());;
    simplefs.Bitmap__Clear (struct.loadF BlockAllocator "bitmap" "ba") (to_u64 "i");;
    struct.storeF BlockAllocator "free" "ba" (SliceAppend uint32T (struct.loadF BlockAllocator "free" "ba") "i");;
    disk.Write ((struct.loadF BlockAllocator "offset" "ba") + (simplefs.Bitmap__BlockNum (struct.loadF BlockAllocator "bitmap" "ba") (to_u64 "i"))) (simplefs.Bitmap__Block (struct.loadF BlockAllocator "bitmap" "ba") (to_u64 "i"));;
    #().

Definition InodeAllocator := struct.decl [
  "sb" :: ptrT;
  "d" :: disk.Disk;
  "free" :: slice.T simplefs.Inum
].

Definition NewInodeAllocator: val :=
  rec: "NewInodeAllocator" "d" "sb" :=
    let: "free" := ref_to (slice.T simplefs.Inum) (NewSlice simplefs.Inum #0) in
    let: "inode_blocks" := struct.loadF superblock.Superblock "InodeBlocks" "sb" in
    let: "offset" := superblock.Superblock__InodeStart "sb" in
    let: "blk_num" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "blk_num") < "inode_blocks"); (λ: <>, "blk_num" <-[uint64T] ((![uint64T] "blk_num") + #1)) := λ: <>,
      let: "blk" := disk.Read ("offset" + (![uint64T] "blk_num")) in
      let: "i" := ref_to uint64T #0 in
      (for: (λ: <>, (![uint64T] "i") < simplefs.INODES_PER_BLOCK); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
        let: "ino" := inode.FromBytes (SliceSubslice byteT "blk" ((![uint64T] "i") * simplefs.INODE_SIZE) (((![uint64T] "i") + #1) * simplefs.INODE_SIZE)) in
        (if: (inode.Inode__GetType "ino") = simplefs.Invalid
        then
          "free" <-[slice.T simplefs.Inum] (SliceAppend simplefs.Inum (![slice.T simplefs.Inum] "free") (((![uint64T] "blk_num") * simplefs.INODES_PER_BLOCK) + (![uint64T] "i")));;
          Continue
        else Continue));;
      Continue);;
    struct.mk InodeAllocator [
      "sb" ::= "sb";
      "d" ::= "d";
      "free" ::= ![slice.T simplefs.Inum] "free"
    ].

Definition InodeAllocator__Alloc: val :=
  rec: "InodeAllocator__Alloc" "ia" "ty" :=
    control.impl.Assert ("ty" ≠ simplefs.Invalid);;
    (if: (slice.len (struct.loadF InodeAllocator "free" "ia")) = #0
    then (#0, #false)
    else
      let: "i" := SliceGet simplefs.Inum (struct.loadF InodeAllocator "free" "ia") ((slice.len (struct.loadF InodeAllocator "free" "ia")) - #1) in
      struct.storeF InodeAllocator "free" "ia" (SliceTake (struct.loadF InodeAllocator "free" "ia") ((slice.len (struct.loadF InodeAllocator "free" "ia")) - #1));;
      let: "ino" := inode.ReadInode (struct.loadF InodeAllocator "d" "ia") (struct.loadF InodeAllocator "sb" "ia") "i" in
      inode.Inode__SetType "ino" "ty";;
      inode.Inode__Write "ino" (struct.loadF InodeAllocator "d" "ia") (struct.loadF InodeAllocator "sb" "ia") "i";;
      ("i", #true)).

Definition InodeAllocator__Free: val :=
  rec: "InodeAllocator__Free" "ia" "i" :=
    let: "ino" := inode.ReadInode (struct.loadF InodeAllocator "d" "ia") (struct.loadF InodeAllocator "sb" "ia") "i" in
    inode.Inode__SetType "ino" simplefs.Invalid;;
    inode.Inode__Write "ino" (struct.loadF InodeAllocator "d" "ia") (struct.loadF InodeAllocator "sb" "ia") "i";;
    struct.storeF InodeAllocator "free" "ia" (SliceAppend simplefs.Inum (struct.loadF InodeAllocator "free" "ia") "i");;
    #().

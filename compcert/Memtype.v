From Hammer Require Import Hammer.


















From compcert Require Import Coqlib.
From compcert Require Import AST.
From compcert Require Import Integers.
From compcert Require Import Floats.
From compcert Require Import Values.
From compcert Require Import Memdata.



Inductive permission: Type :=
| Freeable: permission
| Writable: permission
| Readable: permission
| Nonempty: permission.



Inductive perm_order: permission -> permission -> Prop :=
| perm_refl:  forall p, perm_order p p
| perm_F_any: forall p, perm_order Freeable p
| perm_W_R:   perm_order Writable Readable
| perm_any_N: forall p, perm_order p Nonempty.

Hint Constructors perm_order: mem.

Lemma perm_order_trans:
forall p1 p2 p3, perm_order p1 p2 -> perm_order p2 p3 -> perm_order p1 p3.
Proof. hammer_hook "Memtype" "Memtype.perm_order_trans".
intros. inv H; inv H0; constructor.
Qed.



Inductive perm_kind: Type :=
| Max: perm_kind
| Cur: perm_kind.

Module Type MEM.


Parameter mem: Type.




Parameter empty: mem.


Parameter alloc: forall (m: mem) (lo hi: Z), mem * block.


Parameter free: forall (m: mem) (b: block) (lo hi: Z), option mem.


Parameter load: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z), option val.


Parameter store: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val), option mem.



Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
match addr with
| Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
| _ => None
end.

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
match addr with
| Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
| _ => None
end.


Parameter loadbytes: forall (m: mem) (b: block) (ofs n: Z), option (list memval).


Parameter storebytes: forall (m: mem) (b: block) (ofs: Z) (bytes: list memval), option mem.


Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
match l with
| nil => Some m
| (b, lo, hi) :: l' =>
match free m b lo hi with
| None => None
| Some m' => free_list m' l'
end
end.



Parameter drop_perm: forall (m: mem) (b: block) (lo hi: Z) (p: permission), option mem.





Parameter nextblock: mem -> block.

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

Axiom valid_not_valid_diff:
forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.


Parameter perm: forall (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission), Prop.



Axiom perm_implies:
forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.



Axiom perm_cur_max:
forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Axiom perm_cur:
forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Axiom perm_max:
forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.


Axiom perm_valid_block:
forall m b ofs k p, perm m b ofs k p -> valid_block m b.




Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
forall ofs, lo <= ofs < hi -> perm m b ofs k p.

Axiom range_perm_implies:
forall m b lo hi k p1 p2,
range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.


Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
range_perm m b ofs (ofs + size_chunk chunk) Cur p
/\ (align_chunk chunk | ofs).

Axiom valid_access_implies:
forall m chunk b ofs p1 p2,
valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
valid_access m chunk b ofs p2.

Axiom valid_access_valid_block:
forall m chunk b ofs,
valid_access m chunk b ofs Nonempty ->
valid_block m b.

Axiom valid_access_perm:
forall m chunk b ofs k p,
valid_access m chunk b ofs p ->
perm m b ofs k p.



Parameter valid_pointer: forall (m: mem) (b: block) (ofs: Z), bool.

Axiom valid_pointer_nonempty_perm:
forall m b ofs,
valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.
Axiom valid_pointer_valid_access:
forall m b ofs,
valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.



Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
valid_pointer m b ofs || valid_pointer m b (ofs - 1).

Axiom weak_valid_pointer_spec:
forall m b ofs,
weak_valid_pointer m b ofs = true <->
valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.
Axiom valid_pointer_implies:
forall m b ofs,
valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.





Axiom nextblock_empty: nextblock empty = 1%positive.
Axiom perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Axiom valid_access_empty:
forall chunk b ofs p, ~valid_access empty chunk b ofs p.




Axiom valid_access_load:
forall m chunk b ofs,
valid_access m chunk b ofs Readable ->
exists v, load chunk m b ofs = Some v.
Axiom load_valid_access:
forall m chunk b ofs v,
load chunk m b ofs = Some v ->
valid_access m chunk b ofs Readable.


Axiom load_type:
forall m chunk b ofs v,
load chunk m b ofs = Some v ->
Val.has_type v (type_of_chunk chunk).


Axiom load_cast:
forall m chunk b ofs v,
load chunk m b ofs = Some v ->
match chunk with
| Mint8signed => v = Val.sign_ext 8 v
| Mint8unsigned => v = Val.zero_ext 8 v
| Mint16signed => v = Val.sign_ext 16 v
| Mint16unsigned => v = Val.zero_ext 16 v
| _ => True
end.

Axiom load_int8_signed_unsigned:
forall m b ofs,
load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs).

Axiom load_int16_signed_unsigned:
forall m b ofs,
load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs).






Axiom range_perm_loadbytes:
forall m b ofs len,
range_perm m b ofs (ofs + len) Cur Readable ->
exists bytes, loadbytes m b ofs len = Some bytes.
Axiom loadbytes_range_perm:
forall m b ofs len bytes,
loadbytes m b ofs len = Some bytes ->
range_perm m b ofs (ofs + len) Cur Readable.


Axiom loadbytes_load:
forall chunk m b ofs bytes,
loadbytes m b ofs (size_chunk chunk) = Some bytes ->
(align_chunk chunk | ofs) ->
load chunk m b ofs = Some(decode_val chunk bytes).


Axiom load_loadbytes:
forall chunk m b ofs v,
load chunk m b ofs = Some v ->
exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
/\ v = decode_val chunk bytes.


Axiom loadbytes_length:
forall m b ofs n bytes,
loadbytes m b ofs n = Some bytes ->
length bytes = Z.to_nat n.

Axiom loadbytes_empty:
forall m b ofs n,
n <= 0 -> loadbytes m b ofs n = Some nil.


Axiom loadbytes_concat:
forall m b ofs n1 n2 bytes1 bytes2,
loadbytes m b ofs n1 = Some bytes1 ->
loadbytes m b (ofs + n1) n2 = Some bytes2 ->
n1 >= 0 -> n2 >= 0 ->
loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Axiom loadbytes_split:
forall m b ofs n1 n2 bytes,
loadbytes m b ofs (n1 + n2) = Some bytes ->
n1 >= 0 -> n2 >= 0 ->
exists bytes1, exists bytes2,
loadbytes m b ofs n1 = Some bytes1
/\ loadbytes m b (ofs + n1) n2 = Some bytes2
/\ bytes = bytes1 ++ bytes2.





Axiom nextblock_store:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
nextblock m2 = nextblock m1.
Axiom store_valid_block_1:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom store_valid_block_2:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
forall b', valid_block m2 b' -> valid_block m1 b'.

Axiom perm_store_1:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Axiom perm_store_2:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.

Axiom valid_access_store:
forall m1 chunk b ofs v,
valid_access m1 chunk b ofs Writable ->
{ m2: mem | store chunk m1 b ofs v = Some m2 }.
Axiom store_valid_access_1:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
forall chunk' b' ofs' p,
valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Axiom store_valid_access_2:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
forall chunk' b' ofs' p,
valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Axiom store_valid_access_3:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
valid_access m1 chunk b ofs Writable.



Axiom load_store_similar:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
forall chunk',
size_chunk chunk' = size_chunk chunk ->
align_chunk chunk' <= align_chunk chunk ->
exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.

Axiom load_store_same:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
load chunk m2 b ofs = Some (Val.load_result chunk v).

Axiom load_store_other:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
forall chunk' b' ofs',
b' <> b
\/ ofs' + size_chunk chunk' <= ofs
\/ ofs + size_chunk chunk <= ofs' ->
load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.



Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
match chunk1, chunk2 with
| (Mint32 | Many32), (Mint32 | Many32) => True
| (Mint64 | Many64), (Mint64 | Many64) => True
| _, _ => False
end.

Axiom load_store_pointer_overlap:
forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
load chunk' m2 b ofs' = Some v ->
ofs' <> ofs ->
ofs' + size_chunk chunk' > ofs ->
ofs + size_chunk chunk > ofs' ->
v = Vundef.
Axiom load_store_pointer_mismatch:
forall chunk m1 b ofs v_b v_o m2 chunk' v,
store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
load chunk' m2 b ofs = Some v ->
~compat_pointer_chunks chunk chunk' ->
v = Vundef.
Axiom load_pointer_store:
forall chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
store chunk m1 b ofs v = Some m2 ->
load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
(v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
\/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').



Axiom loadbytes_store_same:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v).
Axiom loadbytes_store_other:
forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
forall b' ofs' n,
b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.



Axiom store_signed_unsigned_8:
forall m b ofs v,
store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Axiom store_signed_unsigned_16:
forall m b ofs v,
store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
Axiom store_int8_zero_ext:
forall m b ofs n,
store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
store Mint8unsigned m b ofs (Vint n).
Axiom store_int8_sign_ext:
forall m b ofs n,
store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
store Mint8signed m b ofs (Vint n).
Axiom store_int16_zero_ext:
forall m b ofs n,
store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
store Mint16unsigned m b ofs (Vint n).
Axiom store_int16_sign_ext:
forall m b ofs n,
store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
store Mint16signed m b ofs (Vint n).





Axiom range_perm_storebytes:
forall m1 b ofs bytes,
range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ->
{ m2 : mem | storebytes m1 b ofs bytes = Some m2 }.
Axiom storebytes_range_perm:
forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable.
Axiom perm_storebytes_1:
forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Axiom perm_storebytes_2:
forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Axiom storebytes_valid_access_1:
forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
forall chunk' b' ofs' p,
valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Axiom storebytes_valid_access_2:
forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
forall chunk' b' ofs' p,
valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Axiom nextblock_storebytes:
forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
nextblock m2 = nextblock m1.
Axiom storebytes_valid_block_1:
forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom storebytes_valid_block_2:
forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
forall b', valid_block m2 b' -> valid_block m1 b'.



Axiom storebytes_store:
forall m1 b ofs chunk v m2,
storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
(align_chunk chunk | ofs) ->
store chunk m1 b ofs v = Some m2.

Axiom store_storebytes:
forall m1 b ofs chunk v m2,
store chunk m1 b ofs v = Some m2 ->
storebytes m1 b ofs (encode_val chunk v) = Some m2.



Axiom loadbytes_storebytes_same:
forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
loadbytes m2 b ofs (Z.of_nat (length bytes)) = Some bytes.
Axiom loadbytes_storebytes_other:
forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
forall b' ofs' len,
len >= 0 ->
b' <> b
\/ ofs' + len <= ofs
\/ ofs + Z.of_nat (length bytes) <= ofs' ->
loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Axiom load_storebytes_other:
forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
forall chunk b' ofs',
b' <> b
\/ ofs' + size_chunk chunk <= ofs
\/ ofs + Z.of_nat (length bytes) <= ofs' ->
load chunk m2 b' ofs' = load chunk m1 b' ofs'.



Axiom storebytes_concat:
forall m b ofs bytes1 m1 bytes2 m2,
storebytes m b ofs bytes1 = Some m1 ->
storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 = Some m2 ->
storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Axiom storebytes_split:
forall m b ofs bytes1 bytes2 m2,
storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
exists m1,
storebytes m b ofs bytes1 = Some m1
/\ storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 = Some m2.





Axiom alloc_result:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
b = nextblock m1.



Axiom nextblock_alloc:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
nextblock m2 = Pos.succ (nextblock m1).

Axiom valid_block_alloc:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom fresh_block_alloc:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
~(valid_block m1 b).
Axiom valid_new_block:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
valid_block m2 b.
Axiom valid_block_alloc_inv:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.



Axiom perm_alloc_1:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Axiom perm_alloc_2:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable.
Axiom perm_alloc_3:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi.
Axiom perm_alloc_4:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Axiom perm_alloc_inv:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall b' ofs k p,
perm m2 b' ofs k p ->
if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p.



Axiom valid_access_alloc_other:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall chunk b' ofs p,
valid_access m1 chunk b' ofs p ->
valid_access m2 chunk b' ofs p.
Axiom valid_access_alloc_same:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall chunk ofs,
lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
valid_access m2 chunk b ofs Freeable.
Axiom valid_access_alloc_inv:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall chunk b' ofs p,
valid_access m2 chunk b' ofs p ->
if eq_block b' b
then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
else valid_access m1 chunk b' ofs p.



Axiom load_alloc_unchanged:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall chunk b' ofs,
valid_block m1 b' ->
load chunk m2 b' ofs = load chunk m1 b' ofs.
Axiom load_alloc_other:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall chunk b' ofs v,
load chunk m1 b' ofs = Some v ->
load chunk m2 b' ofs = Some v.
Axiom load_alloc_same:
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall chunk ofs v,
load chunk m2 b ofs = Some v ->
v = Vundef.
Axiom load_alloc_same':
forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
forall chunk ofs,
lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
load chunk m2 b ofs = Some Vundef.





Axiom range_perm_free:
forall m1 b lo hi,
range_perm m1 b lo hi Cur Freeable ->
{ m2: mem | free m1 b lo hi = Some m2 }.
Axiom free_range_perm:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
range_perm m1 bf lo hi Cur Freeable.



Axiom nextblock_free:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
nextblock m2 = nextblock m1.
Axiom valid_block_free_1:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
forall b, valid_block m1 b -> valid_block m2 b.
Axiom valid_block_free_2:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
forall b, valid_block m2 b -> valid_block m1 b.



Axiom perm_free_1:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
forall b ofs k p,
b <> bf \/ ofs < lo \/ hi <= ofs ->
perm m1 b ofs k p ->
perm m2 b ofs k p.
Axiom perm_free_2:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Axiom perm_free_3:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
forall b ofs k p,
perm m2 b ofs k p -> perm m1 b ofs k p.



Axiom valid_access_free_1:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
forall chunk b ofs p,
valid_access m1 chunk b ofs p ->
b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
valid_access m2 chunk b ofs p.
Axiom valid_access_free_2:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
forall chunk ofs p,
lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
~(valid_access m2 chunk bf ofs p).
Axiom valid_access_free_inv_1:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
forall chunk b ofs p,
valid_access m2 chunk b ofs p ->
valid_access m1 chunk b ofs p.
Axiom valid_access_free_inv_2:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
forall chunk ofs p,
valid_access m2 chunk bf ofs p ->
lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.



Axiom load_free:
forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
forall chunk b ofs,
b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
load chunk m2 b ofs = load chunk m1 b ofs.



Axiom nextblock_drop:
forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
nextblock m' = nextblock m.
Axiom drop_perm_valid_block_1:
forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
forall b', valid_block m b' -> valid_block m' b'.
Axiom drop_perm_valid_block_2:
forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
forall b', valid_block m' b' -> valid_block m b'.

Axiom range_perm_drop_1:
forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
range_perm m b lo hi Cur Freeable.
Axiom range_perm_drop_2:
forall m b lo hi p,
range_perm m b lo hi Cur Freeable -> { m' | drop_perm m b lo hi p = Some m' }.

Axiom perm_drop_1:
forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
Axiom perm_drop_2:
forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
Axiom perm_drop_3:
forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Axiom perm_drop_4:
forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.

Axiom load_drop:
forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
forall chunk b' ofs,
b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
load chunk m' b' ofs = load chunk m b' ofs.







Parameter extends: mem -> mem -> Prop.

Axiom extends_refl:
forall m, extends m m.

Axiom load_extends:
forall chunk m1 m2 b ofs v1,
extends m1 m2 ->
load chunk m1 b ofs = Some v1 ->
exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.

Axiom loadv_extends:
forall chunk m1 m2 addr1 addr2 v1,
extends m1 m2 ->
loadv chunk m1 addr1 = Some v1 ->
Val.lessdef addr1 addr2 ->
exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.

Axiom loadbytes_extends:
forall m1 m2 b ofs len bytes1,
extends m1 m2 ->
loadbytes m1 b ofs len = Some bytes1 ->
exists bytes2, loadbytes m2 b ofs len = Some bytes2
/\ list_forall2 memval_lessdef bytes1 bytes2.

Axiom store_within_extends:
forall chunk m1 m2 b ofs v1 m1' v2,
extends m1 m2 ->
store chunk m1 b ofs v1 = Some m1' ->
Val.lessdef v1 v2 ->
exists m2',
store chunk m2 b ofs v2 = Some m2'
/\ extends m1' m2'.

Axiom store_outside_extends:
forall chunk m1 m2 b ofs v m2',
extends m1 m2 ->
store chunk m2 b ofs v = Some m2' ->
(forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
extends m1 m2'.

Axiom storev_extends:
forall chunk m1 m2 addr1 v1 m1' addr2 v2,
extends m1 m2 ->
storev chunk m1 addr1 v1 = Some m1' ->
Val.lessdef addr1 addr2 ->
Val.lessdef v1 v2 ->
exists m2',
storev chunk m2 addr2 v2 = Some m2'
/\ extends m1' m2'.

Axiom storebytes_within_extends:
forall m1 m2 b ofs bytes1 m1' bytes2,
extends m1 m2 ->
storebytes m1 b ofs bytes1 = Some m1' ->
list_forall2 memval_lessdef bytes1 bytes2 ->
exists m2',
storebytes m2 b ofs bytes2 = Some m2'
/\ extends m1' m2'.

Axiom storebytes_outside_extends:
forall m1 m2 b ofs bytes2 m2',
extends m1 m2 ->
storebytes m2 b ofs bytes2 = Some m2' ->
(forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z.of_nat (length bytes2) -> False) ->
extends m1 m2'.

Axiom alloc_extends:
forall m1 m2 lo1 hi1 b m1' lo2 hi2,
extends m1 m2 ->
alloc m1 lo1 hi1 = (m1', b) ->
lo2 <= lo1 -> hi1 <= hi2 ->
exists m2',
alloc m2 lo2 hi2 = (m2', b)
/\ extends m1' m2'.

Axiom free_left_extends:
forall m1 m2 b lo hi m1',
extends m1 m2 ->
free m1 b lo hi = Some m1' ->
extends m1' m2.

Axiom free_right_extends:
forall m1 m2 b lo hi m2',
extends m1 m2 ->
free m2 b lo hi = Some m2' ->
(forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
extends m1 m2'.

Axiom free_parallel_extends:
forall m1 m2 b lo hi m1',
extends m1 m2 ->
free m1 b lo hi = Some m1' ->
exists m2',
free m2 b lo hi = Some m2'
/\ extends m1' m2'.

Axiom valid_block_extends:
forall m1 m2 b,
extends m1 m2 ->
(valid_block m1 b <-> valid_block m2 b).
Axiom perm_extends:
forall m1 m2 b ofs k p,
extends m1 m2 -> perm m1 b ofs k p -> perm m2 b ofs k p.
Axiom valid_access_extends:
forall m1 m2 chunk b ofs p,
extends m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p.
Axiom valid_pointer_extends:
forall m1 m2 b ofs,
extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
Axiom weak_valid_pointer_extends:
forall m1 m2 b ofs,
extends m1 m2 ->
weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true.





Parameter inject: meminj -> mem -> mem -> Prop.

Axiom valid_block_inject_1:
forall f m1 m2 b1 b2 delta,
f b1 = Some(b2, delta) ->
inject f m1 m2 ->
valid_block m1 b1.

Axiom valid_block_inject_2:
forall f m1 m2 b1 b2 delta,
f b1 = Some(b2, delta) ->
inject f m1 m2 ->
valid_block m2 b2.

Axiom perm_inject:
forall f m1 m2 b1 b2 delta ofs k p,
f b1 = Some(b2, delta) ->
inject f m1 m2 ->
perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.

Axiom valid_access_inject:
forall f m1 m2 chunk b1 ofs b2 delta p,
f b1 = Some(b2, delta) ->
inject f m1 m2 ->
valid_access m1 chunk b1 ofs p ->
valid_access m2 chunk b2 (ofs + delta) p.

Axiom valid_pointer_inject:
forall f m1 m2 b1 ofs b2 delta,
f b1 = Some(b2, delta) ->
inject f m1 m2 ->
valid_pointer m1 b1 ofs = true ->
valid_pointer m2 b2 (ofs + delta) = true.

Axiom weak_valid_pointer_inject:
forall f m1 m2 b1 ofs b2 delta,
f b1 = Some(b2, delta) ->
inject f m1 m2 ->
weak_valid_pointer m1 b1 ofs = true ->
weak_valid_pointer m2 b2 (ofs + delta) = true.

Axiom address_inject:
forall f m1 m2 b1 ofs1 b2 delta p,
inject f m1 m2 ->
perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
f b1 = Some (b2, delta) ->
Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.

Axiom valid_pointer_inject_no_overflow:
forall f m1 m2 b ofs b' delta,
inject f m1 m2 ->
valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
f b = Some(b', delta) ->
0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Axiom weak_valid_pointer_inject_no_overflow:
forall f m1 m2 b ofs b' delta,
inject f m1 m2 ->
weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
f b = Some(b', delta) ->
0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Axiom valid_pointer_inject_val:
forall f m1 m2 b ofs b' ofs',
inject f m1 m2 ->
valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.

Axiom weak_valid_pointer_inject_val:
forall f m1 m2 b ofs b' ofs',
inject f m1 m2 ->
weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.

Axiom inject_no_overlap:
forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
inject f m1 m2 ->
b1 <> b2 ->
f b1 = Some (b1', delta1) ->
f b2 = Some (b2', delta2) ->
perm m1 b1 ofs1 Max Nonempty ->
perm m1 b2 ofs2 Max Nonempty ->
b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Axiom different_pointers_inject:
forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
inject f m m' ->
b1 <> b2 ->
valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
f b1 = Some (b1', delta1) ->
f b2 = Some (b2', delta2) ->
b1' <> b2' \/
Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).

Axiom load_inject:
forall f m1 m2 chunk b1 ofs b2 delta v1,
inject f m1 m2 ->
load chunk m1 b1 ofs = Some v1 ->
f b1 = Some (b2, delta) ->
exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.

Axiom loadv_inject:
forall f m1 m2 chunk a1 a2 v1,
inject f m1 m2 ->
loadv chunk m1 a1 = Some v1 ->
Val.inject f a1 a2 ->
exists v2, loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2.

Axiom loadbytes_inject:
forall f m1 m2 b1 ofs len b2 delta bytes1,
inject f m1 m2 ->
loadbytes m1 b1 ofs len = Some bytes1 ->
f b1 = Some (b2, delta) ->
exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
/\ list_forall2 (memval_inject f) bytes1 bytes2.

Axiom store_mapped_inject:
forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
inject f m1 m2 ->
store chunk m1 b1 ofs v1 = Some n1 ->
f b1 = Some (b2, delta) ->
Val.inject f v1 v2 ->
exists n2,
store chunk m2 b2 (ofs + delta) v2 = Some n2
/\ inject f n1 n2.

Axiom store_unmapped_inject:
forall f chunk m1 b1 ofs v1 n1 m2,
inject f m1 m2 ->
store chunk m1 b1 ofs v1 = Some n1 ->
f b1 = None ->
inject f n1 m2.

Axiom store_outside_inject:
forall f m1 m2 chunk b ofs v m2',
inject f m1 m2 ->
(forall b' delta ofs',
f b' = Some(b, delta) ->
perm m1 b' ofs' Cur Readable ->
ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
store chunk m2 b ofs v = Some m2' ->
inject f m1 m2'.

Axiom storev_mapped_inject:
forall f chunk m1 a1 v1 n1 m2 a2 v2,
inject f m1 m2 ->
storev chunk m1 a1 v1 = Some n1 ->
Val.inject f a1 a2 ->
Val.inject f v1 v2 ->
exists n2,
storev chunk m2 a2 v2 = Some n2 /\ inject f n1 n2.

Axiom storebytes_mapped_inject:
forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
inject f m1 m2 ->
storebytes m1 b1 ofs bytes1 = Some n1 ->
f b1 = Some (b2, delta) ->
list_forall2 (memval_inject f) bytes1 bytes2 ->
exists n2,
storebytes m2 b2 (ofs + delta) bytes2 = Some n2
/\ inject f n1 n2.

Axiom storebytes_unmapped_inject:
forall f m1 b1 ofs bytes1 n1 m2,
inject f m1 m2 ->
storebytes m1 b1 ofs bytes1 = Some n1 ->
f b1 = None ->
inject f n1 m2.

Axiom storebytes_outside_inject:
forall f m1 m2 b ofs bytes2 m2',
inject f m1 m2 ->
(forall b' delta ofs',
f b' = Some(b, delta) ->
perm m1 b' ofs' Cur Readable ->
ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
storebytes m2 b ofs bytes2 = Some m2' ->
inject f m1 m2'.

Axiom alloc_right_inject:
forall f m1 m2 lo hi b2 m2',
inject f m1 m2 ->
alloc m2 lo hi = (m2', b2) ->
inject f m1 m2'.

Axiom alloc_left_unmapped_inject:
forall f m1 m2 lo hi m1' b1,
inject f m1 m2 ->
alloc m1 lo hi = (m1', b1) ->
exists f',
inject f' m1' m2
/\ inject_incr f f'
/\ f' b1 = None
/\ (forall b, b <> b1 -> f' b = f b).

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Axiom alloc_left_mapped_inject:
forall f m1 m2 lo hi m1' b1 b2 delta,
inject f m1 m2 ->
alloc m1 lo hi = (m1', b1) ->
valid_block m2 b2 ->
0 <= delta <= Ptrofs.max_unsigned ->
(forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
(forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
inj_offset_aligned delta (hi-lo) ->
(forall b delta' ofs k p,
f b = Some (b2, delta') ->
perm m1 b ofs k p ->
lo + delta <= ofs + delta' < hi + delta -> False) ->
exists f',
inject f' m1' m2
/\ inject_incr f f'
/\ f' b1 = Some(b2, delta)
/\ (forall b, b <> b1 -> f' b = f b).

Axiom alloc_parallel_inject:
forall f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
inject f m1 m2 ->
alloc m1 lo1 hi1 = (m1', b1) ->
lo2 <= lo1 -> hi1 <= hi2 ->
exists f', exists m2', exists b2,
alloc m2 lo2 hi2 = (m2', b2)
/\ inject f' m1' m2'
/\ inject_incr f f'
/\ f' b1 = Some(b2, 0)
/\ (forall b, b <> b1 -> f' b = f b).

Axiom free_inject:
forall f m1 l m1' m2 b lo hi m2',
inject f m1 m2 ->
free_list m1 l = Some m1' ->
free m2 b lo hi = Some m2' ->
(forall b1 delta ofs k p,
f b1 = Some(b, delta) -> perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
inject f m1' m2'.

Axiom free_parallel_inject:
forall f m1 m2 b lo hi m1' b' delta,
inject f m1 m2 ->
free m1 b lo hi = Some m1' ->
f b = Some(b', delta) ->
exists m2',
free m2 b' (lo + delta) (hi + delta) = Some m2'
/\ inject f m1' m2'.

Axiom drop_outside_inject:
forall f m1 m2 b lo hi p m2',
inject f m1 m2 ->
drop_perm m2 b lo hi p = Some m2' ->
(forall b' delta ofs k p,
f b' = Some(b, delta) ->
perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
inject f m1 m2'.



Definition flat_inj (thr: block) : meminj :=
fun (b: block) => if plt b thr then Some(b, 0) else None.

Parameter inject_neutral: forall (thr: block) (m: mem), Prop.

Axiom neutral_inject:
forall m, inject_neutral (nextblock m) m ->
inject (flat_inj (nextblock m)) m m.

Axiom empty_inject_neutral:
forall thr, inject_neutral thr empty.

Axiom alloc_inject_neutral:
forall thr m lo hi b m',
alloc m lo hi = (m', b) ->
inject_neutral thr m ->
Plt (nextblock m) thr ->
inject_neutral thr m'.

Axiom store_inject_neutral:
forall chunk m b ofs v m' thr,
store chunk m b ofs v = Some m' ->
inject_neutral thr m ->
Plt b thr ->
Val.inject (flat_inj thr) v v ->
inject_neutral thr m'.

Axiom drop_inject_neutral:
forall m b lo hi p m' thr,
drop_perm m b lo hi p = Some m' ->
inject_neutral thr m ->
Plt b thr ->
inject_neutral thr m'.

End MEM.

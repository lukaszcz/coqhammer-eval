From Hammer Require Import Hammer.






Set Warnings "-notation-overridden,-parsing".
From LF Require Export Lists.











Inductive boollist : Type :=
| bool_nil
| bool_cons (b : bool) (l : boollist).





Inductive list (X:Type) : Type :=
| nil
| cons (x : X) (l : list X).



Check list.




Check (nil nat).




Check (cons nat 3 (nil nat)).




Check nil.




Check cons.






Check (cons nat 2 (cons nat 1 (nil nat))).





Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
match count with
| 0 => nil X
| S count' => cons X x (repeat X x count')
end.



Example test_repeat1 :
repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. hammer_hook "Poly" "Poly.test_repeat1". reflexivity.  Qed.



Example test_repeat2 :
repeat bool false 1 = cons bool false (nil bool).
Proof. hammer_hook "Poly" "Poly.test_repeat2". reflexivity.  Qed.




Module MumbleGrumble.

Inductive mumble : Type :=
| a
| b (x : mumble) (y : nat)
| c.

Inductive grumble (X:Type) : Type :=
| d (m : mumble)
| e (x : X).



End MumbleGrumble.


Definition manual_grade_for_mumble_grumble : option (nat*string) := None.







Fixpoint repeat' X x count : list X :=
match count with
| 0        => nil X
| S count' => cons X x (repeat' X x count')
end.



Check repeat'.

Check repeat.









Fixpoint repeat'' X x count : list X :=
match count with
| 0        => nil _
| S count' => cons _ x (repeat'' _ x count')
end.



Definition list123 :=
cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).



Definition list123' :=
cons _ 1 (cons _ 2 (cons _ 3 (nil _))).






Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.



Definition list123'' := cons 1 (cons 2 (cons 3 nil)).



Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
match count with
| 0        => nil
| S count' => cons x (repeat''' x count')
end.



Inductive list' {X:Type} : Type :=
| nil'
| cons' (x : X) (l : list').





Fixpoint app {X : Type} (l1 l2 : list X)
: (list X) :=
match l1 with
| nil      => l2
| cons h t => cons h (app t l2)
end.

Fixpoint rev {X:Type} (l:list X) : list X :=
match l with
| nil      => nil
| cons h t => app (rev t) (cons h nil)
end.

Fixpoint length {X : Type} (l : list X) : nat :=
match l with
| nil => 0
| cons _ l' => S (length l')
end.

Example test_rev1 :
rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. hammer_hook "Poly" "Poly.test_rev1". reflexivity.  Qed.

Example test_rev2:
rev (cons true nil) = cons true nil.
Proof. hammer_hook "Poly" "Poly.test_rev2". reflexivity.  Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. hammer_hook "Poly" "Poly.test_length1". reflexivity.  Qed.






Fail Definition mynil := nil.



Definition mynil : list nat := nil.



Check @nil.

Definition mynil' := @nil nat.



Notation "x :: y" := (cons x y)
(at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
(at level 60, right associativity).



Definition list123''' := [1; 2; 3].






Theorem app_nil_r : forall (X:Type), forall l:list X,
l ++ [] = l.
Proof. hammer_hook "Poly" "Poly.app_nil_r".
Admitted.

Theorem app_assoc : forall A (l m n:list A),
l ++ m ++ n = (l ++ m) ++ n.
Proof. hammer_hook "Poly" "Poly.app_assoc".
Admitted.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
length (l1 ++ l2) = length l1 + length l2.
Proof. hammer_hook "Poly" "Poly.app_length".
Admitted.




Theorem rev_app_distr: forall X (l1 l2 : list X),
rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof. hammer_hook "Poly" "Poly.rev_app_distr".
Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
rev (rev l) = l.
Proof. hammer_hook "Poly" "Poly.rev_involutive".
Admitted.







Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.



Notation "( x , y )" := (pair x y).



Notation "X * Y" := (prod X Y) : type_scope.







Definition fst {X Y : Type} (p : X * Y) : X :=
match p with
| (x, y) => x
end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
match p with
| (x, y) => y
end.



Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
: list (X*Y) :=
match lx, ly with
| [], _ => []
| _, [] => []
| x :: tx, y :: ty => (x, y) :: (combine tx ty)
end.





Fixpoint split {X Y : Type} (l : list (X*Y))
: (list X) * (list Y)
. Admitted.

Example test_split:
split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. hammer_hook "Poly" "Poly.test_split".
Admitted.







Module OptionPlayground.

Inductive option (X:Type) : Type :=
| Some (x : X)
| None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.



Fixpoint nth_error {X : Type} (l : list X) (n : nat)
: option X :=
match l with
| [] => None
| a :: l' => if n =? O then Some a else nth_error l' (pred n)
end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. hammer_hook "Poly" "Poly.test_nth_error1". reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. hammer_hook "Poly" "Poly.test_nth_error2". reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. hammer_hook "Poly" "Poly.test_nth_error3". reflexivity. Qed.



Definition hd_error {X : Type} (l : list X) : option X
. Admitted.



Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Admitted.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
Admitted.












Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
f (f (f n)).



Check @doit3times.


Example test_doit3times: doit3times minustwo 9 = 3.
Proof. hammer_hook "Poly" "Poly.test_doit3times". reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. hammer_hook "Poly" "Poly.test_doit3times'". reflexivity.  Qed.






Fixpoint filter {X:Type} (test: X->bool) (l:list X)
: (list X) :=
match l with
| []     => []
| h :: t => if test h then h :: (filter test t)
else       filter test t
end.



Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. hammer_hook "Poly" "Poly.test_filter1". reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
(length l) =? 1.

Example test_filter2:
filter length_is_1
[ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
= [ [3]; [4]; [8] ].
Proof. hammer_hook "Poly" "Poly.test_filter2". reflexivity.  Qed.



Definition countoddmembers' (l:list nat) : nat :=
length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. hammer_hook "Poly" "Poly.test_countoddmembers'1". reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. hammer_hook "Poly" "Poly.test_countoddmembers'2". reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. hammer_hook "Poly" "Poly.test_countoddmembers'3". reflexivity.  Qed.






Example test_anon_fun':
doit3times (fun n => n * n) 2 = 256.
Proof. hammer_hook "Poly" "Poly.test_anon_fun'". reflexivity.  Qed.





Example test_filter2':
filter (fun l => (length l) =? 1)
[ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
= [ [3]; [4]; [8] ].
Proof. hammer_hook "Poly" "Poly.test_filter2'". reflexivity.  Qed.



Definition filter_even_gt7 (l : list nat) : list nat
. Admitted.

Example test_filter_even_gt7_1 :
filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Admitted.

Example test_filter_even_gt7_2 :
filter_even_gt7 [5;2;6;19;129] = [].
Admitted.




Definition partition {X : Type}
(test : X -> bool)
(l : list X)
: list X * list X
. Admitted.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Admitted.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Admitted.







Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
match l with
| []     => []
| h :: t => (f h) :: (map f t)
end.



Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. hammer_hook "Poly" "Poly.test_map1". reflexivity.  Qed.



Example test_map2:
map oddb [2;1;2;5] = [false;true;false;true].
Proof. hammer_hook "Poly" "Poly.test_map2". reflexivity.  Qed.



Example test_map3:
map (fun n => [evenb n;oddb n]) [2;1;2;5]
= [[true;false];[false;true];[true;false];[false;true]].
Proof. hammer_hook "Poly" "Poly.test_map3". reflexivity.  Qed.






Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
map f (rev l) = rev (map f l).
Proof. hammer_hook "Poly" "Poly.map_rev".
Admitted.




Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
: (list Y)
. Admitted.

Example test_flat_map1:
flat_map (fun n => [n;n;n]) [1;5;4]
= [1; 1; 1; 5; 5; 5; 4; 4; 4].
Admitted.




Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
: option Y :=
match xo with
| None => None
| Some x => Some (f x)
end.








Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
: Y :=
match l with
| nil => b
| h :: t => f h (fold f t b)
end.



Check (fold andb).


Example fold_example1 :
fold mult [1;2;3;4] 1 = 24.
Proof. hammer_hook "Poly" "Poly.fold_example1". reflexivity. Qed.

Example fold_example2 :
fold andb [true;true;false;true] true = false.
Proof. hammer_hook "Poly" "Poly.fold_example2". reflexivity. Qed.

Example fold_example3 :
fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. hammer_hook "Poly" "Poly.fold_example3". reflexivity. Qed.






Definition manual_grade_for_fold_types_different : option (nat*string) := None.







Definition constfun {X: Type} (x: X) : nat->X :=
fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. hammer_hook "Poly" "Poly.constfun_example1". reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. hammer_hook "Poly" "Poly.constfun_example2". reflexivity. Qed.



Check plus.




Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. hammer_hook "Poly" "Poly.test_plus3". reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. hammer_hook "Poly" "Poly.test_plus3'". reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. hammer_hook "Poly" "Poly.test_plus3''". reflexivity.  Qed.




Module Exercises.



Definition fold_length {X : Type} (l : list X) : nat :=
fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. hammer_hook "Poly" "Poly.Exercises.test_fold_length1". reflexivity. Qed.



Theorem fold_length_correct : forall X (l : list X),
fold_length l = length l.
Proof. hammer_hook "Poly" "Poly.Exercises.fold_length_correct".
Admitted.




Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y
. Admitted.






Definition manual_grade_for_fold_map : option (nat*string) := None.






Definition prod_curry {X Y Z : Type}
(f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).



Definition prod_uncurry {X Y Z : Type}
(f : X -> Y -> Z) (p : X * Y) : Z
. Admitted.



Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. hammer_hook "Poly" "Poly.Exercises.test_map1'". reflexivity.  Qed.



Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
(f : X -> Y -> Z)
x y,
prod_curry (prod_uncurry f) x y = f x y.
Proof. hammer_hook "Poly" "Poly.Exercises.uncurry_curry".
Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
(f : (X * Y) -> Z) (p : X * Y),
prod_uncurry (prod_curry f) p = f p.
Proof. hammer_hook "Poly" "Poly.Exercises.curry_uncurry".
Admitted.






Definition manual_grade_for_informal_proof : option (nat*string) := None.




Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.



Definition one : cnat :=
fun (X : Type) (f : X -> X) (x : X) => f x.



Definition two : cnat :=
fun (X : Type) (f : X -> X) (x : X) => f (f x).



Definition zero : cnat :=
fun (X : Type) (f : X -> X) (x : X) => x.



Definition three : cnat := @doit3times.






Definition succ (n : cnat) : cnat
. Admitted.

Example succ_1 : succ zero = one.
Proof. hammer_hook "Poly" "Poly.Exercises.Church.succ_1".  Admitted.

Example succ_2 : succ one = two.
Proof. hammer_hook "Poly" "Poly.Exercises.Church.succ_2".  Admitted.

Example succ_3 : succ two = three.
Proof. hammer_hook "Poly" "Poly.Exercises.Church.succ_3".  Admitted.






Definition plus (n m : cnat) : cnat
. Admitted.

Example plus_1 : plus zero one = one.
Proof. hammer_hook "Poly" "Poly.Exercises.Church.plus_1".  Admitted.

Example plus_2 : plus two three = plus three two.
Proof. hammer_hook "Poly" "Poly.Exercises.Church.plus_2".  Admitted.

Example plus_3 :
plus (plus two two) three = plus one (plus three three).
Proof. hammer_hook "Poly" "Poly.Exercises.Church.plus_3".  Admitted.






Definition mult (n m : cnat) : cnat
. Admitted.

Example mult_1 : mult one one = one.
Proof. hammer_hook "Poly" "Poly.Exercises.Church.mult_1".  Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. hammer_hook "Poly" "Poly.Exercises.Church.mult_2".  Admitted.

Example mult_3 : mult two three = plus three three.
Proof. hammer_hook "Poly" "Poly.Exercises.Church.mult_3".  Admitted.









Definition exp (n m : cnat) : cnat
. Admitted.

Example exp_1 : exp two two = plus two two.
Proof. hammer_hook "Poly" "Poly.Exercises.Church.exp_1".  Admitted.

Example exp_2 : exp three zero = one.
Proof. hammer_hook "Poly" "Poly.Exercises.Church.exp_2".  Admitted.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. hammer_hook "Poly" "Poly.Exercises.Church.exp_3".  Admitted.



End Church.

End Exercises.




From Hammer Require Import Hammer.

Require Import Bool.
Require Import NArith.
Require Import Ndigits.
Require Import Ndec.
Require Import Nnat.
From IntMap Require Import Allmaps.
Require Import OrderedType.
Require Import OrderedTypeEx.
Require Import FMapInterface.
Require Import FMapList.


Set Implicit Arguments.







Module NUsualOrderedType <: UsualOrderedType.
Definition t:=N.
Definition eq:=@eq N.
Definition eq_refl := @refl_equal t.
Definition eq_sym := @sym_eq t.
Definition eq_trans := @trans_eq t.

Definition lt p q:= Nless p q = true.

Definition lt_trans := Nless_trans.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.NUsualOrderedType.lt_not_eq".
intros; intro.
rewrite H0 in H.
red in H.
rewrite Nless_not_refl in H; discriminate.
Qed.

Definition compare : forall x y : t, Compare lt eq x y.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.NUsualOrderedType.compare".
intros x y.
destruct (Nless_total x y) as [[H|H]|H].
apply LT; unfold lt; auto.
apply GT; unfold lt; auto.
apply EQ; auto.
Qed.

Definition eq_dec := N_as_OT.eq_dec.

End NUsualOrderedType.




Module MapIntMap <: S with Module E:=NUsualOrderedType.

Module E:=NUsualOrderedType.
Module ME:=OrderedTypeFacts(E).
Module PE:=KeyOrderedType(E).

Definition key := N.

Definition t := Map.

Section A.
Variable A:Type.

Definition empty : t A := M0 A.

Definition is_empty (m : t A) : bool :=
MapEmptyp _ (MapCanonicalize _ m).

Definition find (x:key)(m: t A) : option A := MapGet _ m x.

Definition mem (x:key)(m: t A) : bool :=
match find x m with
| Some _ => true
| None => false
end.

Definition add (x:key)(v:A)(m:t A) : t A := MapPut _ m x v.

Definition remove (x:key)(m:t A) : t A := MapRemove _ m x.

Definition elements (m : t A) : list (N*A) := alist_of_Map _ m.

Definition cardinal (m : t A) : nat := MapCard _ m.

Definition MapsTo (x:key)(v:A)(m:t A) := find x m = Some v.

Definition In (x:key)(m:t A) := exists e:A, MapsTo x e m.

Definition Empty m := forall (a : key)(e:A) , ~ MapsTo a e m.

Definition eq_key (p p':key*A) := E.eq (fst p) (fst p').

Definition eq_key_elt (p p':key*A) :=
E.eq (fst p) (fst p') /\ (snd p) = (snd p').

Definition lt_key (p p':key*A) := E.lt (fst p) (fst p').

Lemma Empty_alt : forall m, Empty m <-> forall a, find a m = None.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.Empty_alt".
unfold Empty, MapsTo.
intuition.
generalize (H a).
destruct (find a m); intuition.
elim (H0 a0); auto.
rewrite H in H0; discriminate.
Qed.

Section Spec.
Variable  m m' m'' : t A.
Variable x y z : key.
Variable e e' : A.

Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.MapsTo_1". intros; rewrite <- H; auto. Qed.

Lemma find_1 : MapsTo x e m -> find x m = Some e.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.find_1". unfold MapsTo; auto. Qed.

Lemma find_2 : find x m = Some e -> MapsTo x e m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.find_2". red; auto. Qed.

Lemma empty_1 : Empty empty.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.empty_1".
rewrite Empty_alt; intros; unfold empty, find; simpl; auto.
Qed.

Lemma is_empty_1 : Empty m -> is_empty m = true.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.is_empty_1".
unfold Empty, is_empty, find; intros.
cut (MapCanonicalize _ m = M0 _).
intros; rewrite H0; simpl; auto.
apply mapcanon_unique.
apply mapcanon_exists_2.
constructor.
red; red; simpl; intros.
rewrite <- (mapcanon_exists_1 _ m).
unfold MapsTo, find in *.
generalize (H a).
destruct (MapGet _ m a); auto.
intros; generalize (H0 a0); destruct 1; auto.
Qed.

Lemma is_empty_2 : is_empty m = true -> Empty m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.is_empty_2".
unfold Empty, is_empty, MapsTo, find; intros.
generalize (MapEmptyp_complete _ _ H); clear H; intros.
rewrite (mapcanon_exists_1 _ m).
rewrite H; simpl; auto.
discriminate.
Qed.

Lemma mem_1 : In x m -> mem x m = true.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.mem_1".
unfold In, MapsTo, mem.
destruct (find x m); auto.
destruct 1; discriminate.
Qed.

Lemma mem_2 : forall m x, mem x m = true -> In x m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.mem_2".
unfold In, MapsTo, mem.
intros.
destruct (find x0 m0); auto; try discriminate.
exists a; auto.
Qed.

Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.add_1".
unfold MapsTo, find, add.
intro H; rewrite H; clear H.
rewrite MapPut_semantics.
rewrite Neqb_correct; auto.
Qed.

Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.add_2".
unfold MapsTo, find, add.
intros.
rewrite MapPut_semantics.
rewrite H0.
generalize (Neqb_complete x y).
destruct (N.eqb x y); auto.
intros.
elim H; auto.
apply H1; auto.
Qed.

Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.add_3".
unfold MapsTo, find, add.
rewrite MapPut_semantics.
intro H.
generalize (Neqb_complete x y).
destruct (N.eqb x y); auto.
intros; elim H; auto.
apply H0; auto.
Qed.

Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.remove_1".
unfold In, MapsTo, find, remove.
rewrite MapRemove_semantics.
intro H.
rewrite H; rewrite Neqb_correct.
red; destruct 1; discriminate.
Qed.

Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.remove_2".
unfold MapsTo, find, remove.
rewrite MapRemove_semantics.
intros.
rewrite H0.
generalize (Neqb_complete x y).
destruct (N.eqb x y); auto.
intros; elim H; apply H1; auto.
Qed.

Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.remove_3".
unfold MapsTo, find, remove.
rewrite MapRemove_semantics.
destruct (N.eqb x y); intros; auto.
discriminate.
Qed.

Lemma alist_sorted_sort : forall l, alist_sorted A l=true -> sort lt_key l.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.alist_sorted_sort".
induction l.
auto.
simpl.
destruct a.
destruct l.
auto.
destruct p.
intros; destruct (andb_prop _ _ H); auto.
Qed.

Lemma elements_3 : sort lt_key (elements m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.elements_3".
unfold elements.
apply alist_sorted_sort.
apply alist_of_Map_sorts.
Qed.

Lemma elements_3w : NoDupA eq_key (elements m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.elements_3w".
change eq_key with (@PE.eqk A).
apply PE.Sort_NoDupA; apply elements_3; auto.
Qed.

Lemma elements_1 :
MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.elements_1".
unfold MapsTo, find, elements.
rewrite InA_alt.
intro H.
exists (x,e).
split.
red; simpl; unfold E.eq; auto.
rewrite alist_of_Map_semantics in H.
generalize H.
set (l:=alist_of_Map A m); clearbody l; clear.
induction l; simpl; auto.
intro; discriminate.
destruct a; simpl; auto.
generalize (Neqb_complete a x).
destruct (N.eqb a x); auto.
left.
injection H0; auto.
intros; f_equal; auto.
Qed.

Lemma elements_2 :
InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.elements_2".
generalize elements_3.
unfold MapsTo, find, elements.
rewrite InA_alt.
intros H ((e0,a),(H0,H1)).
red in H0; simpl in H0; unfold E.eq in H0; destruct H0; subst.
rewrite alist_of_Map_semantics.
generalize H H1; clear H H1.
set (l:=alist_of_Map A m); clearbody l; clear.
induction l; simpl; auto.
intro; contradiction.
intros.
destruct a0; simpl.
inversion H1.
injection H0; intros; subst.
rewrite Neqb_correct; auto.
assert (InA eq_key (e0,a) l).
rewrite InA_alt.
exists (e0,a); split; auto.
red; simpl; auto; red; auto.
generalize (PE.Sort_In_cons_1 H H2).
unfold PE.ltk; simpl.
intros H3; generalize (E.lt_not_eq H3).
generalize (Neqb_complete a0 e0).
destruct (N.eqb a0 e0); auto.
destruct 2.
apply H4; auto.
inversion H; auto.
Qed.

Lemma cardinal_1 : forall m, cardinal m = length (elements m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.cardinal_1". exact (@MapCard_as_length _). Qed.

Definition Equal m m' := forall y, find y m = find y m'.
Definition Equiv (eq_elt:A->A->Prop) m m' :=
(forall k, In k m <-> In k m') /\
(forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
Definition Equivb (cmp: A->A->bool) := Equiv (Cmp cmp).



Definition fold (B:Type)(f:key -> A -> B -> B)(m:t A)(i:B) : B :=
fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.

Lemma fold_1 :
forall (B:Type) (i : B) (f : key -> A -> B -> B),
fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.fold_1". auto. Qed.

End Spec.

Variable B : Type.

Fixpoint mapi_aux (pf:N->N)(f : N -> A -> B)(m:t A) { struct m }: t B :=
match m with
| M0 => M0 _
| M1 x y => M1 _ x (f (pf x) y)
| M2 m0 m1 =>  M2 _ (mapi_aux (fun n => pf (N.double n)) f m0)
(mapi_aux (fun n => pf (Ndouble_plus_one n)) f m1)
end.

Definition mapi := mapi_aux (fun n => n).

Definition map (f:A->B) := mapi (fun _ => f).

End A.

Lemma mapi_aux_1 : forall (elt elt':Type)(m: t elt)(pf:N->N)(x:key)(e:elt)
(f:key->elt->elt'), MapsTo x e m ->
exists y, E.eq y x /\ MapsTo x (f (pf y) e) (mapi_aux pf f m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.mapi_aux_1".
unfold MapsTo; induction m; simpl; auto.
inversion 1.

intros.
exists x; split; [red; auto|].
generalize (Neqb_complete a x).
destruct (N.eqb a x); try discriminate.
injection H; intros; subst; auto.
rewrite H1; auto.

intros.
exists x; split; [red;auto|].
destruct x; simpl in *.
destruct (IHm1 (fun n : N => pf (N.double n)) _ _ f H) as (y,(Hy,Hy')).
rewrite Hy in Hy'; simpl in Hy'; auto.
destruct p; simpl in *.
destruct (IHm2 (fun n : N => pf (Ndouble_plus_one n)) _ _ f H) as (y,(Hy,Hy')).
rewrite Hy in Hy'; simpl in Hy'; auto.
destruct (IHm1 (fun n : N => pf (N.double n)) _ _ f H) as (y,(Hy,Hy')).
rewrite Hy in Hy'; simpl in Hy'; auto.
destruct (IHm2 (fun n : N => pf (Ndouble_plus_one n)) _ _ f H) as (y,(Hy,Hy')).
rewrite Hy in Hy'; simpl in Hy'; auto.
Qed.

Lemma mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
(f:key->elt->elt'), MapsTo x e m ->
exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.mapi_1".
intros elt elt' m; exact (mapi_aux_1 (fun n => n)).
Qed.

Lemma mapi_aux_2 : forall (elt elt':Type)(m: t elt)(pf:N->N)(x:key)
(f:key->elt->elt'), In x (mapi_aux pf f m) -> In x m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.mapi_aux_2".
unfold In, MapsTo.
induction m; simpl in *.
intros pf x f (e,He); inversion He.
intros pf x f (e,He).
exists a0.
destruct (N.eqb a x); try discriminate; auto.
intros pf x f (e,He).
destruct x; [|destruct p]; eauto.
Qed.

Lemma mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
(f:key->elt->elt'), In x (mapi f m) -> In x m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.mapi_2".
intros elt elt' m. exact (@mapi_aux_2 _ elt' m (fun n => n)).
Qed.

Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
MapsTo x e m -> MapsTo x (f e) (map f m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.map_1".
unfold map; intros.
destruct (@mapi_1 _ _ m x e (fun _ => f)) as (e',(_,H0)); auto.
Qed.

Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
In x (map f m) -> In x m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.map_2".
unfold map; intros.
eapply mapi_2; eauto.
Qed.

Module L := FMapList.Raw E.



Definition anti_elements (A:Type)(l:list (key*A)) := L.fold (@add _) l (empty _).

Definition map2 (A B C:Type)(f:option A->option B -> option C)(m:t A)(m':t B) : t C :=
anti_elements (L.map2 f (elements m) (elements m')).

Lemma add_spec : forall (A:Type)(m:t A) x y e,
find x (add y e m) = if E.eq_dec x y then Some e else find x m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.add_spec".
intros.
destruct (E.eq_dec x y).
apply find_1.
eapply MapsTo_1 with y; eauto.
red; auto.
apply add_1; auto.
red; auto.
case_eq (find x m); intros.
apply find_1.
apply add_2; unfold E.eq in *; auto.
case_eq (find x (add y e m)); auto; intros.
rewrite <- H; symmetry.
apply find_1; auto.
apply (@add_3 _ m y x a e); unfold E.eq in *; auto.
Qed.

Lemma anti_elements_mapsto_aux : forall (A:Type)(l:list (key*A)) m k e,
NoDupA (eq_key (A:=A)) l ->
(forall x, L.PX.In x l -> In x m -> False) ->
(MapsTo k e (L.fold (@add _) l m) <-> L.PX.MapsTo k e l \/ MapsTo k e m).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.anti_elements_mapsto_aux".
induction l.
simpl; auto.
intuition.
inversion H2.
simpl; destruct a; intros.
inversion_clear H.
rewrite IHl; clear IHl; auto.
intuition.
red in H3.
rewrite add_spec in H3; auto.
destruct (E.eq_dec k0 k).
inversion_clear H3; subst; auto.
right; apply find_2; auto.
inversion_clear H3; auto.
compute in H; destruct H.
subst; right; apply add_1; auto.
red; auto.
destruct (E.eq_dec k0 k) as [H|H].
subst.
destruct (H0 k); eauto.
red; eauto.
right; apply add_2; unfold E.eq in *; auto.

intros.
assert (~E.eq x k).
contradict H1.
destruct H.
apply InA_eqA with (x,x0); eauto with *.
apply (H0 x).
destruct H; exists x0; auto.
revert H3.
unfold In.
intros (e',He').
exists e'; apply (@add_3 _ m k x e' a); unfold E.eq; auto.
Qed.

Lemma anti_elements_mapsto : forall (A:Type) l k e, NoDupA (eq_key (A:=A)) l ->
(MapsTo k e (anti_elements l) <-> L.PX.MapsTo k e l).
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.anti_elements_mapsto".
intros.
unfold anti_elements.
rewrite anti_elements_mapsto_aux; auto; unfold empty; auto.
intuition.
inversion H1.
inversion 2.
inversion H2.
Qed.

Lemma find_anti_elements : forall (A:Type)(l: list (key*A)) x, sort (@lt_key _) l ->
find x (anti_elements l) = L.find x l.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.find_anti_elements".
intros.
case_eq (L.find x l); intros.
apply find_1.
rewrite anti_elements_mapsto; auto using L.PX.Sort_NoDupA, L.find_2.
case_eq (find x (anti_elements l)); auto; intros.
rewrite <- H0; symmetry.
apply L.find_1; auto.
rewrite <- anti_elements_mapsto; auto using L.PX.Sort_NoDupA, find_2.
Qed.

Lemma find_elements : forall (A:Type)(m: t A) x,
L.find x (elements m) = find x m.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.find_elements".
intros.
case_eq (find x m); intros.
apply L.find_1.
apply elements_3; auto.
red; apply elements_1.
apply find_2; auto.
case_eq (L.find x (elements m)); auto; intros.
rewrite <- H; symmetry.
apply find_1; auto.
apply elements_2.
apply L.find_2; auto.
Qed.

Lemma elements_in : forall (A:Type)(s:t A) x, L.PX.In x (elements s) <-> In x s.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.elements_in".
intros.
unfold L.PX.In, In.
firstorder.
exists x0.
red; rewrite <- find_elements; auto.
apply L.find_1; auto.
apply elements_3.
exists x0.
apply L.find_2.
rewrite find_elements; auto.
Qed.

Lemma map2_1 : forall (A B C:Type)(m: t A)(m': t B)(x:key)
(f:option A->option B ->option C),
In x m \/ In x m' -> find x (map2 f m m') = f (find x m) (find x m').
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.map2_1".
unfold map2; intros.
rewrite find_anti_elements; auto.
rewrite <- find_elements; auto.
rewrite <- find_elements; auto.
apply L.map2_1; auto.
apply elements_3; auto.
apply elements_3; auto.
do 2 rewrite elements_in; auto.
apply L.map2_sorted; auto.
apply elements_3; auto.
apply elements_3; auto.
Qed.

Lemma map2_2 : forall (A B C:Type)(m: t A)(m': t B)(x:key)
(f:option A->option B ->option C),
In x (map2 f m m') -> In x m \/ In x m'.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.map2_2".
unfold map2; intros.
do 2 rewrite <- elements_in.
apply L.map2_2 with (f:=f); auto.
apply elements_3; auto.
apply elements_3; auto.
destruct H.
exists x0.
rewrite <- anti_elements_mapsto; auto.
apply L.PX.Sort_NoDupA; auto.
apply L.map2_sorted; auto.
apply elements_3; auto.
apply elements_3; auto.
Qed.



Definition equal (A:Type)(cmp:A -> A -> bool)(m m' : t A) : bool :=
L.equal cmp (elements m) (elements m').

Lemma equal_1 :
forall (A:Type)(m: t A)(m': t A)(cmp: A -> A -> bool),
Equivb cmp m m' -> equal cmp m m' = true.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.equal_1".
unfold equal, Equivb, Equiv, Cmp.
intros.
apply L.equal_1.
apply elements_3.
apply elements_3.
unfold L.Equivb.
destruct H.
split; intros.
do 2 rewrite elements_in; auto.
apply (H0 k);
red; rewrite <- find_elements; apply L.find_1; auto;
apply elements_3.
Qed.

Lemma equal_2 :
forall (A:Type)(m: t A)(m': t A)(cmp: A -> A -> bool),
equal cmp m m' = true -> Equivb cmp m m'.
Proof. hammer_hook "FMapIntMap" "FMapIntMap.MapIntMap.equal_2".
unfold equal, Equivb, Equiv, Cmp.
intros.
destruct (L.equal_2 (elements_3 m) (elements_3 m') H); clear H.
split.
intros; do 2 rewrite <- elements_in; auto.
intros; apply (H1 k);
apply L.find_2; rewrite find_elements;auto.
Qed.

End MapIntMap.

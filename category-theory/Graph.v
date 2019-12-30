From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Coq.FSets.FMaps.
Require Import Category.Lib.FMapExt.
Require Import Coq.Vectors.Vector.
Require Import Coq.omega.Omega.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Module PO := PairOrderedType Nat_as_OT Nat_as_OT.

Module M := FMapList.Make(PO).

Module Import FMapExt := FMapExt PO M.
Module P := FMapExt.P.
Module F := P.F.



Record Metagraph := {
objects : nat;
object := Fin.t objects;

num_arrows : nat;
arrows : Vector.t (object * object) num_arrows;
arrow := Fin.t num_arrows;

domain   (f : arrow) : object := fst (nth arrows f);
codomain (f : arrow) : object := snd (nth arrows f)
}.



Record Metasemigroupoid := {
is_metagraph :> Metagraph;

pairs : M.t (arrow is_metagraph);

pairs_correct : ∀ k, M.In k pairs ->
(fst k < num_arrows is_metagraph ∧ snd k < num_arrows is_metagraph)%nat;

composite (f g h : arrow is_metagraph) :=
M.MapsTo (` (Fin.to_nat f), ` (Fin.to_nat g)) h pairs;


composite_correct : ∀ (f g : arrow is_metagraph),
domain is_metagraph f = codomain is_metagraph g ->
∃ fg, composite f g fg ∧
domain   is_metagraph fg = domain   is_metagraph g ∧
codomain is_metagraph fg = codomain is_metagraph f;

composition_law (k g f kg gf : arrow is_metagraph) :
composite k g kg ->
composite g f gf ->
∀ kgf, composite kg f kgf ↔ composite k gf kgf
}.

Definition composition (M : Metasemigroupoid) (f g : arrow (is_metagraph M)) :
domain (is_metagraph M) f = codomain (is_metagraph M) g ->
arrow (is_metagraph M) := fun H => `1 (composite_correct M f g H).

Lemma composition_correct (M : Metasemigroupoid)
(f g : arrow (is_metagraph M))
(H : domain (is_metagraph M) f = codomain (is_metagraph M) g) :
∀ fg, fg = composition M f g H ->
domain   (is_metagraph M) fg = domain   (is_metagraph M) g ∧
codomain (is_metagraph M) fg = codomain (is_metagraph M) f.
Proof. hammer_hook "Graph" "Graph.composition_correct".
intros.
unfold composition in H0.
destruct (composite_correct M f g H).
simpl in *; subst; intuition.
Qed.

Lemma composition_associative (M : Metasemigroupoid)
(f g k : arrow (is_metagraph M))
(Hfg : domain (is_metagraph M) f = codomain (is_metagraph M) g)
(Hgk : domain (is_metagraph M) g = codomain (is_metagraph M) k)
(Hf_gk : domain M f = codomain M (composition M g k Hgk))
(Hfg_k : domain M (composition M f g Hfg) = codomain M k) :
composition M f (composition M g k Hgk) Hf_gk =
composition M (composition M f g Hfg) k Hfg_k.
Proof. hammer_hook "Graph" "Graph.composition_associative".
unfold composition in *.
destruct (composite_correct M g k Hgk).
destruct (composite_correct M f g Hfg).
simplify; simpl in *.
destruct (composite_correct M f x Hf_gk).
destruct (composite_correct M x0 k Hfg_k).
simplify; simpl in *.
spose (fst (composition_law M _ _ _ _ _ p0 p x2) p2) as X.
apply (FMapExt.F.MapsTo_fun p1 X).
Qed.



Record Metacategory := {
is_metasemigroupoid :> Metasemigroupoid;

identity (x : object is_metasemigroupoid) : arrow is_metasemigroupoid;

identity_correct : ∀ x f,
f = identity x ->
domain   is_metasemigroupoid f = x ∧
codomain is_metasemigroupoid f = x;

identity_left_law : ∀ f u,
u = identity (codomain is_metasemigroupoid f) ->
composite is_metasemigroupoid u f f;

identity_right_law : ∀ f u,
u = identity (domain is_metasemigroupoid f) ->
composite is_metasemigroupoid f u f
}.

Lemma identity_left (M : Metacategory) : ∀ f u,
u = identity M (codomain M f) ->
∀ (H : domain M u = codomain M f),
composition M u f H = f.
Proof. hammer_hook "Graph" "Graph.identity_left".
unfold composition; intros.
pose proof (identity_left_law M f u H).
unfold composite in H1.
destruct (composite_correct M u f H0); simpl.
simplify.
eapply F.MapsTo_fun; eauto.
Qed.

Lemma identity_right (M : Metacategory) : ∀ f u,
u = identity M (domain M f) ->
∀ (H : domain M f = codomain M u),
composition M f u H = f.
Proof. hammer_hook "Graph" "Graph.identity_right".
unfold composition; intros.
pose proof (identity_right_law M f u H).
unfold composite in H1.
destruct (composite_correct M f u H0); simpl.
simplify.
eapply F.MapsTo_fun; eauto.
Qed.





Import VectorNotations.
Import Fin.

Program Definition TwoG : Metagraph := {|
objects := 2;
arrows  := [(F1, F1); (FS F1, FS F1); (F1, FS F1)]
|}.

Notation "[map ]" := (M.empty _) (at level 9, only parsing).
Notation "x +=> y" := (M.add x y) (at level 9, y at level 100, only parsing).
Notation "[map  a ; .. ; b ]" := (a .. (b [map]) ..) (only parsing).

Ltac cleanup :=
FMapExt.simplify_maps;
repeat (right; intuition; try discriminate; FMapExt.simplify_maps).

Program Definition TwoMS : Metasemigroupoid := {|
is_metagraph := TwoG;
pairs := [map (0, 0) +=> F1
;    (1, 1) +=> FS F1
;    (1, 2) +=> FS (FS F1)
;    (2, 0) +=> FS (FS F1) ]%nat
|}.
Next Obligation.
destruct k; simpl in *.
destruct n, n0; simpl in *.
- destruct (fst (in_mapsto_iffT _ _ _) H); clear H.
cleanup.
- destruct (fst (in_mapsto_iffT _ _ _) H); clear H.
cleanup.
destruct H1; discriminate.
cleanup.
destruct H1; discriminate.
cleanup.
destruct H1; discriminate.
cleanup.
destruct H1; discriminate.
- destruct (fst (in_mapsto_iffT _ _ _) H); clear H.
cleanup.
destruct H1; discriminate.
cleanup.
destruct H1; discriminate.
cleanup.
destruct H1; discriminate.
cleanup.
destruct H1.
inversion_clear H.
inversion_clear H1.
split; omega.
- destruct (fst (in_mapsto_iffT _ _ _) H); clear H.
cleanup.
destruct H1; discriminate.
cleanup.
destruct H1.
simpl in *.
rewrite <- H, <- H0.
split; omega.
cleanup.
destruct H1.
simpl in *.
rewrite <- H, <- H1.
split; omega.
cleanup.
destruct H1.
inversion_clear H.
inversion_clear H1.
Qed.
Next Obligation.
unfold arrow in *.
repeat destruct f using caseS';
repeat destruct g using caseS'; simpl;
vm_compute in H;
try discriminate;
try inversion f;
try inversion g;
match goal with
[ |- ∃ _, M.MapsTo (?X, ?Y) _ _ ∧ _ ∧ _ ] =>
match goal with
[ |- context[M.add (X, Y) ?F _ ] ] =>
exists F
end
end;
split; intuition; cleanup.
Qed.
Next Obligation.
split; intros;
repeat FMapExt.simplify_maps;
simpl in *;
destruct H0, H1, H2; subst;
intuition idtac; try discriminate; cleanup.
Qed.

Program Definition TwoC : Metacategory := {|
is_metasemigroupoid := TwoMS;
identity := fun x => _
|}.
Next Obligation.
destruct x using caseS'. exact F1.
destruct p using caseS'. exact (FS F1).
inversion p.
Defined.
Next Obligation.
destruct x using caseS'. intuition.
destruct p using caseS'. intuition.
inversion p.
Qed.
Next Obligation.
unfold composite; simpl.
repeat destruct f using caseS';
repeat destruct p using caseS'; cleanup.
inversion p.
Qed.
Next Obligation.
unfold composite; simpl.
repeat destruct f using caseS';
repeat destruct p using caseS'; cleanup.
inversion p.
Qed.

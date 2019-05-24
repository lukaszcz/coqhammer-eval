From mathcomp Require Import all_ssreflect.
From Hammer Require Import Hammer Reconstr.
Require Import Classical.

(*
  This utility module proves a few induction principles
  used in other proofs.
 *)

(* Two strong induction principles over natural numbers,
   as represented in the MathComp library.
   Adapted from work by Tej Chajed. *)

Section StrongInductionLtn.

  Variable P:nat -> Prop.

  (** The stronger inductive hypothesis given in strong induction. The standard
  [nat ] induction principle provides only n = pred m, with [P 0] required
  separately. *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

  Lemma P0 : P 0.
  Proof.
    hammer_hook "casper" "casper.StrongInductionLtn.P0".
    apply IH; intros.
    exfalso; inversion H.
  Qed.

  Hint Resolve P0.

  Lemma pred_increasing : forall (n m : nat),
      n <= m ->
      n.-1 <= m.-1.
  Proof. hammer_hook "casper" "casper.StrongInductionLtn.pred_increasing". by elim => //= n IH'; case. Qed.

  Local Lemma strong_induction_all : forall n,
      (forall m, m <= n -> P m).
  Proof.
    hammer_hook "casper" "casper.StrongInductionLtn.strong_induction_all".
    elim => //=; first by case.
    move => n IH' m Hm.
    apply: IH.
    move => n' Hn'.
    apply: IH'.
    have Hnn: n < n.+1 by apply ltnSn.
    move: Hm.
    rewrite leq_eqVlt.
    move/orP.
    case.
    - move/eqP => Hm.
      by move: Hm Hn' =>->.
    - move => Hm.
      have Hmn: m <= n by [].
      suff Hsuff: n' < n.
        rewrite leq_eqVlt.
        apply/orP.
        by right.
      by apply: leq_trans; eauto.
  Qed.

  Theorem strong_induction_ltn : forall n, P n.
  Proof.
    hammer_hook "casper" "casper.StrongInductionLtn.strong_induction_ltn".
    eauto using strong_induction_all.
  Qed.

End StrongInductionLtn.

Section StrongInductionSub.

  Variable k : nat.

  Variable T : Type.

  Variable P : nat -> T -> Prop.

  Hypothesis IH : forall (v1 : nat) (h1 : T), (forall (v1a : nat) (h1a : T), k < v1a -> v1a - k < v1 - k -> P v1a h1a) -> P v1 h1.

  Theorem strong_induction_sub : forall n t, P n t.
  Proof.
    hammer_hook "casper" "casper.StrongInductionLtn.strong_induction_sub".
    elim/strong_induction_ltn.
    move => m IH' t.
    apply IH.
    move => v1a h1a Hlt Hlt'.
    apply: IH'.
    rewrite ltn_subRL in Hlt'.
    rewrite subnKC in Hlt' => //.
    rewrite leq_eqVlt.
    by apply/orP; right.
  Qed.

End StrongInductionSub.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This module proves the Accountable Safety theorem for Casper
   from an abstract model of the blockchain and validator sets.
   Assumes a static set of validators.
   Based on CasperOneMessage.thy by Yiochi Hirai.
*)

Section CasperOneMessage.

Variable Validator : finType.
Variable Hash : finType.

(* all sets containing "2/3" of all validators or more *)
Variable quorum_1 : {set {set Validator}}.
(* all sets containing "1/3" of all validators or more *)
Variable quorum_2 : {set {set Validator}}.

(* generalized assumption on validator sets containing fractions of all validators *)
Hypothesis quorums_intersection :
  forall q1 q2, q1 \in quorum_1 -> q2 \in quorum_1 ->
  exists q3, q3 \in quorum_2 /\ q3 \subset q1 /\ q3 \subset q2.

Lemma quorums_property :
 forall q1 q2, q1 \in quorum_1 -> q2 \in quorum_1 ->
 exists q3, q3 \in quorum_2 /\ forall n, n \in q3 -> n \in q1 /\ n \in q2.
Proof.
  hammer_hook "casper" "casper.quorums_property".
move => q1 q2 Hq1 Hq2.
have [q3 [Hq3 [Hq13 Hq23]]] := (quorums_intersection Hq1 Hq2).
exists q3.
split => //.
move => n Hn.
split.
- by apply/(subsetP Hq13).
- by apply/(subsetP Hq23).
Qed.

(* global state is a function defining the votes cast (and not cast) by validators *)
(* first natural number is hash (target) distance from genesis hash *)
(* second natural number is (implicit) source hash distance from genesis hash *)
Record State :=
 mkSt { vote_msg : Validator -> Hash -> nat -> nat -> bool }.

(* abstract representation of a block tree *)
Variable hash_parent : rel Hash.

Notation "h1 <~ h2" := (hash_parent h1 h2) (at level 50).

(* hash for genesis block *)
Variable genesis : Hash.

Hypothesis hash_at_most_one_parent :
  forall h1 h2 h3, h2 <~ h1 -> h3 <~ h1 -> h2 = h3.

Definition hash_ancestor h1 h2 :=
 connect hash_parent h1 h2.

Notation "h1 <~* h2" := (hash_ancestor h1 h2) (at level 50).

Notation "h1 </~* h2" := (~ hash_ancestor h1 h2) (at level 50).

Lemma hash_ancestor_base : forall h1 h2,
  h1 <~ h2 -> h1 <~* h2.
Proof.
  hammer_hook "casper" "casper.hash_ancestor_base".
by apply/connect1.
Qed.

Lemma hash_ancestor_step : forall h1 h2 h3,
 h1 <~ h2 -> h2 <~* h3 -> h1 <~* h3.
Proof.
  hammer_hook "casper" "casper.hash_ancestor_step".
move => h1 h2 h3.
move/connect1.
by apply/connect_trans.
Qed.

Lemma hash_ancestor_intro' :
  forall h1 h2 h3, h1 <~* h2 -> h2 <~ h3 -> h1 <~* h3.
Proof.
  hammer_hook "casper" "casper.hash_ancestor_intro".
move => h1 h2 h3 H1 H2.
apply: connect_trans; eauto.
by apply/connect1.
Qed.

Lemma hash_ancestor_concat :
  forall h1 h2 h3, h2 <~* h3 -> h1 <~* h2 -> h1 <~* h3.
Proof.
  hammer_hook "casper" "casper.hash_ancestor_concat".
move => h1 h2 h3 H2 H1.
by apply: connect_trans; eauto.
Qed.

Lemma hash_ancestor_other:
  forall h1 h2 p, h1 <~* h2 -> p </~* h2 -> p </~* h1.
Proof.
  hammer_hook "casper" "casper.hash_ancestor_other".
move => h1 h2 p H1 H2.
move => Hp.
case: H2.
move: Hp H1.
by apply/connect_trans.
Qed.

(* predicate stating first hash is ancestor of second hash at the indicated distance *)
Inductive nth_ancestor : nat -> Hash -> Hash -> Prop :=
| nth_ancestor_0 : forall h1, nth_ancestor 0 h1 h1
| nth_ancestor_nth : forall n h1 h2 h3,
    nth_ancestor n h1 h2 -> h2 <~ h3 ->
    nth_ancestor n.+1 h1 h3.

Example parent_ancestor : forall h1 h2,
  h1 <~ h2 -> nth_ancestor 1 h1 h2.
Proof.
  hammer_hook "casper" "casper.parent_ancestor".
move => h1 h2 Hp.
apply: nth_ancestor_nth; eauto.
exact: nth_ancestor_0.
Qed.

(* "1/3" or more of validators have voted for a justified link *)
Definition justified_link s q parent pre new now :=
  q \in quorum_1 /\
  (forall n, n \in q -> vote_msg s n new now pre) /\
  nth_ancestor (now - pre) parent new /\
  now > pre.

Lemma ancestor_means :
  forall n parent new,
  nth_ancestor n parent new -> n > 0 -> parent <~* new.
Proof.
  hammer_hook "casper" "casper.ancestor_means".
elim => //=.
move => n IH parent new Hn.
inversion Hn; subst.
case Hn0: (n == 0).
  move/eqP: Hn0 H0 -> => Hnt Hlt.
  inversion Hnt; subst.
  by apply/connect1.
move/negP/negP: Hn0 => Hn0 Hltn.
have Hnn: 0 < n.
  apply: neq0_lt0n.
  by apply/negP/negP.
move: (IH _ _ H0 Hnn) => Hp.
apply: connect_trans; eauto.
by apply/connect1.
Qed.

Lemma justified_means_ancestor :
  forall s q parent pre new now,
  justified_link s q parent pre new now -> parent <~* new.
Proof.
move => s q parent pre new now.
case => [Hn [Ha [Hnn Hw]]] {Ha}.
move: now pre parent new Hw Hnn.
elim => //=.
move => n IH pre parent new Hlt Ha.
inversion Ha; subst; first by apply/connect0.
have Hn0: n0 = n - pre.
  rewrite subSn // in H.
  by apply/succn_inj.
rewrite Hn0 in H0.
case H'n0: (n0 == 0).
  move/eqP: H'n0 => H'n0.
  rewrite H'n0 in Hn0.
  rewrite -Hn0 in H0.
  inversion H0 .
  exact/connect1.
move/negP/negP: H'n0 => H'n0.
have Hp: pre < n.
  rewrite Hn0 in H'n0.
  rewrite -subn_gt0.
  case Hnn: (n - pre); last by apply ltn0Sn.
  rewrite Hnn in Hn0.
  by move/eqP: H'n0.
have IH' := IH _ _ _ Hp H0.
apply: connect_trans; eauto.
by apply/connect1.
Qed.

(* genesis block is justified, and blocks reachable by a justified link are justified *)
Inductive justified : State -> Hash -> nat -> Prop :=
| orig : forall s, justified s genesis 0
| follow : forall s parent pre q new now,
    justified s parent pre ->
    justified_link s q parent pre new now ->
    justified s new now.

(* finalized blocks are children of justified blocks and have a justified link *)
Definition finalized s q h v child :=
 h <~ child /\ justified s h v /\ justified_link s q h v child v.+1.

(* a state has a fork when blocks in different branches are both finalized *)
Definition finalization_fork s :=
  exists h1 h2 q1 q2 v1 v2 c1 c2,
    finalized s q1 h1 v1 c1 /\
    finalized s q2 h2 v2 c2 /\
    h2 </~* h1 /\ h1 </~* h2 /\ h1 <> h2.

(* validator slashing conditions *)
Definition slashed_dbl_vote s n :=
 exists h1 h2, h1 <> h2 /\ exists v s1 s2, vote_msg s n h1 v s1 /\ vote_msg s n h2 v s2.

Definition slashed_surround s n :=
  exists h1 h2 v1 v2 s1 s2,
    vote_msg s n h1 v1 s1 /\
     vote_msg s n h2 v2 s2 /\
     v1 > v2 /\ s2 > s1.

Definition slashed s n : Prop :=
 slashed_dbl_vote s n \/ slashed_surround s n.

(* "1/3" or more of validators are slashed *)
Definition quorum_slashed s :=
 exists q, q \in quorum_2 /\ forall n, n \in q -> slashed s n.

Lemma l0 : forall s q1 h2 v2 h1 v1,
 justified_link s q1 h2 v2 h1 v1 ->
 v1 > v2.
Proof.
  hammer_hook "casper" "casper.l0".
  Reconstr.reasy Reconstr.Empty (@CasperOneMessage.justified_link).
Qed.

Lemma l02 : forall s q1 q2 h2 v2 h1 v3 h3 c3,
    justified_link s q1 h2 v2 h1 v3.+1 ->
    finalized s q2 h3 v3 c3 ->
    h3 </~* h1 -> v2 < v3 ->
    exists q, q \in quorum_2 /\ forall n, n \in q -> slashed_dbl_vote s n.
Proof.
move => s q1 q2 h2 v2 h1 v3 h3 c3 Hj Hf Hh Hv.
have Hn1: forall n, n \in q1 -> vote_msg s n h1 v3.+1 v2.
  hammer_hook "casper" "casper.l02.subgoal_1".
  by Reconstr.htrivial (@Hj)
                Reconstr.Empty
                (@justified_link).
have Hn2: forall n, n \in q2 -> vote_msg s n c3 v3.+1 v3.
  hammer_hook "casper" "casper.l02.subgoal_2".
  by Reconstr.htrivial (@Hf)
                Reconstr.Empty
                (@finalized, @justified_link).
have Hq1: q1 \in quorum_1.
  hammer_hook "casper" "casper.l02.subgoal_3".
  by Reconstr.scrush.
have Hq2: q2 \in quorum_1.
  hammer_hook "casper" "casper.l02.subgoal_4".
  by Reconstr.htrivial (@Hf)
                Reconstr.Empty
                (@finalized, @justified_link).
have He: exists q, q \in quorum_2 /\ forall n, n \in q -> n \in q1 /\ n \in q2.
  hammer_hook "casper" "casper.l02.subgoal_5".
  by Reconstr.htrivial (@Hq1, @Hq2)
                (@quorums_property)
                Reconstr.Empty.
have He': exists q, q \in quorum_2 /\ forall n, n \in q -> vote_msg s n h1 v3.+1 v2 /\ vote_msg s n c3 v3.+1 v3.
  hammer_hook "casper" "casper.l02.subgoal_6".
  move: He => [q [Hq Hn]].
  exists q.
  split => //.
  move => n.
  move/Hn => [Hq'1 Hq'2].
  split.
  - by apply Hn1.
  - by apply Hn2.
have Hne: h1 <> c3.
  hammer_hook "casper" "casper.l02.subgoal_7".
  by Reconstr.htrivial (@Hf, @Hh)
                (@hash_ancestor_base)
                (@finalized); auto.
have Hnen: h1 <> c3 /\ (exists q, q \in quorum_2 /\ forall n, n \in q -> vote_msg s n h1 v3.+1 v2 /\ vote_msg s n c3 v3.+1 v3) by auto.
clear Hn1 Hn2 Hq1 Hq2 He He' Hne.
hammer_hook "casper" "casper.l02.subgoal_8".
by Reconstr.hobvious (@Hnen)
                Reconstr.Empty
                (@Coq.Init.Datatypes.is_true, @slashed_dbl_vote).
Qed.

Lemma l01 : forall s q1 q2 h2 v2 h1 h3 v3 c3,
  justified_link s q1 h2 v2 h1 v3.+1 ->
  finalized s q2 h3 v3 c3 ->
  h3 </~* h1 -> v2 < v3 ->
  quorum_slashed s.
Proof.
  hammer_hook "casper" "casper.l01".
move => s q1 q2 h2 v2 h1 h3 v3 c3 Hl Hf Hh Hv.
have Hq: exists q, q \in quorum_2 /\ forall n, n \in q -> slashed_dbl_vote s n.
  hammer_hook "casper" "casper.l01.subgoal_1".
  by Reconstr.hobvious (@Hf, @Hh, @Hv, @Hl)
                (@l02)
                Reconstr.Empty.
hammer_hook "casper" "casper.l01.subgoal_2".
by Reconstr.hobvious (@Hq)
                Reconstr.Empty
                (@slashed, @quorum_slashed).
Qed.

Lemma l04 : forall s q1 q2 h2 v2 h1 v1 v3 h3 c3,
 justified_link s q1 h2 v2 h1 v1 ->
 finalized s q2 h3 v3 c3 ->
 v3.+1 < v1 ->
 h3 </~* h1 ->
 v2 < v3 ->
 exists q, q \in quorum_2 /\ forall n, n \in q -> slashed_surround s n.
Proof.
move => s q1 q2 h2 v2 h1 v1 v3 h3 c3 Hj Hf Hv Hh Hv'.
have Hq1: q1 \in quorum_1 by Reconstr.scrush.
have Hq2: q2 \in quorum_1.
  hammer_hook "casper" "casper.l04.subgoal_1".
  by Reconstr.htrivial (@Hf)
                Reconstr.Empty
                (@finalized, @justified_link).
have H'q1: forall n, n \in q1 -> vote_msg s n h1 v1 v2.
  hammer_hook "casper" "casper.l04.subgoal_2".
  by Reconstr.htrivial (@Hj)
                Reconstr.Empty
                (@justified_link).
have H'q2: forall n, n \in q2 -> vote_msg s n c3 v3.+1 v3.
  hammer_hook "casper" "casper.l04.subgoal_3".
  by Reconstr.htrivial (@Hf)
                Reconstr.Empty
                (@finalized, @justified_link).
have Hq: exists q, q \in quorum_2 /\ forall n, n \in q -> n \in q1 /\ n \in q2.
  hammer_hook "casper" "casper.l04.subgoal_4".
  by Reconstr.htrivial (@Hq1, @Hq2)
                (@quorums_property)
                Reconstr.Empty.
have Hq': exists q, q \in quorum_2 /\ forall n, n \in q -> vote_msg s n h1 v1 v2 /\ vote_msg s n c3 v3.+1 v3.
  hammer_hook "casper" "casper.l04.subgoal_5".
  have [q [Hq0 Hq']] := Hq.
  exists q; split => //.
  by Reconstr.scrush.
have Hn: forall n, (vote_msg s n h1 v1 v2 /\ vote_msg s n c3 v3.+1 v3) -> slashed_surround s n.
  hammer_hook "casper" "casper.l04.subgoal_6".
  move => n [Hvm Hvm'].
  by exists h1, c3, v1, v3.+1, v2, v3.
hammer_hook "casper" "casper.l04.subgoal_7".
by Reconstr.ryelles6 Reconstr.Empty (@Coq.Init.Datatypes.is_true).
Qed.

Lemma l03 : forall s q1 q2 h2 v2 h1 h3 v1 v3 c3,
  justified_link s q1 h2 v2 h1 v1 ->
  finalized s q2 h3 v3 c3 ->
  v1 > v3.+1 ->
  h3 </~* h1 ->
  v2 < v3 ->
  quorum_slashed s.
Proof.
move => s q1 q2 h2 v2 h1 h3 v1 v3 c3 Hj Hf Hlt Ha Hlt'.
have Hq: exists q, q \in quorum_2 /\ forall n, n \in q -> slashed_surround s n.
  hammer_hook "casper" "casper.l03.subgoal_1".
  by Reconstr.hobvious (@Hf, @Hlt, @Ha, @Hlt', @Hj)
                (@l04)
                Reconstr.Empty.
hammer_hook "casper" "casper.l03.subgoal_2".
by Reconstr.hobvious (@Hq)
                Reconstr.Empty
                (@slashed, @quorum_slashed).
Qed.

Lemma l00 : forall s q1 q2 h2 v2 h1 h3 v1 v3 c3,
  justified_link s q1 h2 v2 h1 v1 ->
  finalized s q2 h3 v3 c3 ->
  v1 > v3 ->
  h3 </~* h1 ->
  v2 < v3 ->
  quorum_slashed s.
Proof.
move => s q1 q2 h2 v2 h1 h3 v1 v3 c3 Hj Hf Hv Hh Hv'.
case Hn: (v1 == v3.+1).
  move/eqP: Hn => Hn.
  hammer_hook "casper" "casper.l00.subgoal_1".
  by Reconstr.hobvious (@Hf, @Hh, @Hv', @Hn, @Hj)
                (@l01)
                (@hash_ancestor).
hammer_hook "casper" "casper.l00.subgoal_2".
move/negP/negP/eqP: Hn => Hn.
have Hgt: v3.+1 < v1.
  apply/ltP.
  move/ltP: Hv => Hv.
  by intuition.
hammer_hook "casper" "casper.l00.subgoal_3".
by Reconstr.hobvious (@Hf, @Hh, @Hv', @Hgt, @Hj)
                (@l03)
                (@hash_ancestor).
Qed.

Lemma l5sub :
  forall s h1 v1 new now pre pre1,
  (forall n q2, q2 \in quorum_2 -> n \in q2 ->
   vote_msg s n new now pre /\ vote_msg s n h1 v1 pre1) ->
  now = v1 ->
  h1 <> new ->
  forall n q2, q2 \in quorum_2 -> n \in q2 ->
  slashed_dbl_vote s n.
Proof.
  hammer_hook "casper" "casper.l5sub".
by Reconstr.hobvious Reconstr.Empty
                Reconstr.Empty
                (@slashed_dbl_vote).
Qed.

Lemma l5'' : forall s q q1 parent1 pre1 h1 v1 parent pre new now,
  justified_link s q parent pre new now ->
  justified_link s q1 parent1 pre1 h1 v1 ->
  ~ quorum_slashed s ->
  now = v1 ->
  h1 = new.
Proof.
move => s q q1 parent1 pre1 h1 v1 parent pre new now Hj Hj1 Ho Hnv.
have Hq: q \in quorum_1 by Reconstr.scrush.
have Hq1: q1 \in quorum_1 by Reconstr.scrush.
have [q2 Hq2]: exists q2, q2 \in quorum_2 /\ forall n, n \in q2 -> n \in q /\ n \in q1.
  hammer_hook "casper" "casper.l5pp.subgoal_1".
  by Reconstr.reasy (@quorums_property) Reconstr.Empty.
have Hn: forall n, n \in q2 -> vote_msg s n new now pre /\ vote_msg s n h1 v1 pre1.
  hammer_hook "casper" "casper.l5pp.subgoal_2".
  by Reconstr.scrush.
case H1n: (h1 == new); first by move/eqP: H1n.
move/eqP: H1n => H1n.
have Hd: forall n, n \in q2 -> slashed_dbl_vote s n.
  hammer_hook "casper" "casper.l5pp.subgoal_3".
  by Reconstr.rcrush Reconstr.Empty (@Coq.Init.Datatypes.is_true, @slashed_dbl_vote).
by have Hs: quorum_slashed s by (hammer_hook "casper" "casper.l5pp.subgoal_4"; Reconstr.rcrush Reconstr.Empty (@slashed, @vote_msg, @quorum_slashed)).
Qed.

Lemma l5' :
  forall s h1 v1 h2 v2,
  justified s h2 v2 ->
  justified s h1 v1 ->
  ~ quorum_slashed s ->
  h1 <> h2 ->
  v2 <> v1.
Proof.
move => s h1 v1 h2 v2 Hj1 Hj2 Hs Hneq.
inversion Hj1.
- hammer_hook "casper" "casper.l5p.subgoal_1".
  inversion Hj2; first by rewrite -H3 -H0 in Hneq.
  by Reconstr.scrush.
- hammer_hook "casper" "casper.l5p.subgoal_2".
  inversion Hj2; first by Reconstr.scrush.
  by Reconstr.rcrush (@l5'') Reconstr.Empty.
Qed.

Lemma l5 : forall s q2 h2 v2 xa parent pre,
  finalized s q2 h2 v2 xa ->
  ~ quorum_slashed s ->
  justified s parent pre ->
  parent <> h2 ->
  v2 <> pre.
Proof.
hammer_hook "casper" "casper.l5".
by Reconstr.hcrush Reconstr.Empty
                (@l5')
                (@finalized).
Qed.

Lemma non_equal_case_ind : forall s h1 v1 q2 h2 v2 xa,
  justified s h1 v1 ->
  finalized s q2 h2 v2 xa ->
  h2 </~* h1 ->
  h1 <> h2 ->
  v1 > v2 ->
  quorum_slashed s.
Proof.
move => s h1 v1 q2 h2 v2 xa Hj Hf Hh Hh' Hv.
pose P (v1 : nat) (h1 : Hash) := justified s h1 v1 -> finalized s q2 h2 v2 xa -> h2 </~* h1 -> h1 <> h2 -> v2 < v1 -> quorum_slashed s.
suff Hsuff: forall v1 h1, P v1 h1 by apply: Hsuff; eauto.
apply (@strong_induction_sub v2).
clear v1 h1 Hj Hh Hh' Hv Hf.
move => v1 h1 IH Hj Hf Hh Hh' Hv.
have Hor: (h1 = genesis /\ v1 = 0) \/
          (exists q parent pre, justified s parent pre /\ justified_link s q parent pre h1 v1).
  hammer_hook "casper" "casper.non_equal_case_ind.subgoal_1".
  inversion Hj; first by left.
  right.
  by exists q, parent, pre.
case: Hor => Hor; first by move: Hor => [H1 H2]; rewrite H2 in Hv.
have Ho: quorum_slashed s \/ ~ quorum_slashed s by apply classic.
case: Ho => // Ho.
move: Hor => [q [parent [pre [Hj1 Hj2]]]].
have IH' := IH pre parent _ _ Hj1 Hf.
have Hp: h2 </~* parent.
  hammer_hook "casper" "casper.non_equal_case_ind.subgoal_2".
  have Hm := justified_means_ancestor Hj2.
  by apply: hash_ancestor_other; eauto.
have Hpe: parent <> h2.
  hammer_hook "casper" "casper.non_equal_case_ind.subgoal_3".
  move => He.
  case: Hp.
  rewrite He.
  by apply/connect0.
have Hplt: pre - v2 < v1 - v2.
  hammer_hook "casper" "casper.non_equal_case_ind.subgoal_4".
  apply l0 in Hj2.
  by apply ltn_sub2r.
case Hlt: (v2 < pre); last first.
  rewrite ltn_neqAle /= in Hlt.
  move/negP/negP: Hlt.
  rewrite negb_and.
  move/orP; case.
  * hammer_hook "casper" "casper.non_equal_case_ind.subgoal_5".
    move/negP/eqP => Hvv.
    case Hv2p: (v2 == pre); last by rewrite Hv2p /= in Hvv.
    move/eqP: Hv2p => Hv2p {Hvv}.
    by have Hl5 := l5 Hf Ho Hj1 Hpe.
  * hammer_hook "casper" "casper.non_equal_case_ind.subgoal_6".
    rewrite leq_eqVlt.
    rewrite negb_or.
    rewrite -leqNgt leq_eqVlt.
    move/andP => [Hnq Hpp].
    move/eqP: Hnq => Hnq.
    case/orP: Hpp.
      move/eqP => Hpp.
      by apply sym_eq in Hpp.
    move => Hlt.
    by have Hl00 := l00 Hj2 Hf Hv Hh Hlt.
by apply: IH'.
Qed.

Lemma non_equal_case : forall s q1 q2 h1 v1 x h2 v2 xa,
  finalized s q1 h1 v1 x ->
  finalized s q2 h2 v2 xa ->
  h2 </~* h1 ->
  h1 <> h2 ->
  v1 > v2 ->
  quorum_slashed s.
Proof.
hammer_hook "casper" "casper.non_equal_case".
by Reconstr.hexhaustive 0 Reconstr.Empty
                (@non_equal_case_ind)
                (@Coq.Init.Datatypes.is_true, @finalized).
Qed.

Lemma equal_case : forall s q1 h1 v1 x q2 h2 xa,
  finalized s q1 h1 v1 x ->
  finalized s q2 h2 v1 xa ->
  h1 <> h2 ->
  quorum_slashed s.
Proof.
move => s q1 h1 v1 x q2 h2 xa Hf Hf' Hh.
have Hq1: q1 \in quorum_1 by Reconstr.scrush.
have Hq2: q2 \in quorum_1 by Reconstr.scrush.
have Hn: forall n, n \in q1 -> vote_msg s n x v1.+1 v1 by Reconstr.scrush.
have Hn': forall n, n \in q2 -> vote_msg s n xa v1.+1 v1 by Reconstr.scrush.
have [q Hq]: exists q, q \in quorum_2 /\ forall n, n \in q -> n \in q1 /\ n \in q2.
  hammer_hook "casper" "casper.equal_case.subgoal_1".
  by Reconstr.rsimple (@quorums_property) Reconstr.Empty.
have Hq': forall n, n \in q -> vote_msg s n x v1.+1 v1 /\ vote_msg s n xa v1.+1 v1.
  hammer_hook "casper" "casper.equal_case.subgoal_2".
  by Reconstr.scrush.
have Hx: x <> xa.
  hammer_hook "casper" "casper.equal_case.subgoal_3".
  move => Hx.
  rewrite Hx in Hf.
  move: Hf => [Hf1 [Hf2 Hf3]].
  move: Hf' => [Hf'1 [Hf'2 Hf'3]].
  by have Hp := hash_at_most_one_parent Hf1 Hf'1.
have Hnn: forall n, vote_msg s n x v1.+1 v1 -> vote_msg s n xa v1.+1 v1 -> slashed_dbl_vote s n.
  hammer_hook "casper" "casper.equal_case.subgoal_4".
  move => n Hv1 Hv2.
  rewrite /slashed_dbl_vote.
  exists x,xa.
  split => //.
  by exists v1.+1, v1,v1.
hammer_hook "casper" "casper.equal_case.subgoal_5".
by Reconstr.ryelles6 (@l5) (@finalized).
Qed.

Lemma safety' : forall s q1 h1 v1 x q2 h2 v2 xa,
  finalized s q1 h1 v1 x ->
  finalized s q2 h2 v2 xa ->
  h2 </~* h1 ->
  h1 </~* h2 ->
  h1 <> h2 ->
  quorum_slashed s.
Proof.
move => s q1 h1 v1 x q2 h2 v2 xa Hf Hf' Hh Hh' Hn.
case Hv: (v1 == v2).
  hammer_hook "casper" "casper.safety.subgoal_1".
  move/eqP: Hv => Hv.
  subst.
  move: Hf Hf' Hn.
  exact: equal_case.
move/eqP: Hv => Hv.
case H1: (v1 > v2).
  hammer_hook "casper" "casper.safety.subgoal_2".
  Reconstr.rcrush (@CasperOneMessage.non_equal_case) (@Coq.Init.Datatypes.is_true).
have Hgt: v2 > v1.
  hammer_hook "casper" "casper.safety.subgoal_3".
  apply/ltP.
  move/ltP: H1.
  move => Hnn.
  by intuition.
move: Hgt.
hammer_hook "casper" "casper.safety.subgoal_4".
by apply: non_equal_case; eauto.
Qed.

Lemma accountable_safety : forall s, finalization_fork s -> quorum_slashed s.
Proof.
hammer_hook "casper" "casper.accountable_safety".
by Reconstr.hobvious Reconstr.Empty
                (@safety')
                (@finalization_fork).
Qed.

End CasperOneMessage.

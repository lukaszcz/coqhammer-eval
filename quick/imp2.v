From Hammer Require Import Hammer Reconstr.

Require Import List.
Require Import Bool.Bool.
Require Import ZArith.
Require String.

Definition vname := String.string.
Definition val := Z.

Local Open Scope Z_scope.

Inductive aexpr :=
| Anum : val -> aexpr
| Avar : vname -> aexpr
| Aplus : aexpr -> aexpr -> aexpr.

Definition state := vname -> val.

Fixpoint aval (s : state) (e : aexpr) :=
  match e with
  | Anum n => n
  | Avar x => s x
  | Aplus x y => aval s x + aval s y
  end.

Fixpoint asimp_const (e : aexpr) :=
  match e with
  | Anum n => Anum n
  | Avar x => Avar x
  | Aplus e1 e2 =>
    match asimp_const e1, asimp_const e2 with
    | Anum n1, Anum n2 => Anum (n1 + n2)
    | e1', e2' => Aplus e1' e2'
    end
  end.

Lemma lem_aval_asimp_const : forall s e, aval s (asimp_const e) = aval s e.
Proof.
  induction e; sauto.
Qed.

Fixpoint plus (e1 e2 : aexpr) :=
  match e1, e2 with
  | Anum n1, Anum n2 => Anum (n1 + n2)
  | Anum 0, _ => e2
  | _, Anum 0 => e1
  | _, _ => Aplus e1 e2
  end.

Lemma lem_aval_plus : forall s e1 e2, aval s (plus e1 e2) = aval s e1 + aval s e2.
Proof.
  hammer_hook "imp2" "imp2.lem_aval_plus".
  Reconstr.scrush (** hammer *).
Qed.

Fixpoint asimp (e : aexpr) :=
  match e with
  | Aplus x y => plus (asimp x) (asimp y)
  | _ => e
  end.

Lemma lem_aval_asimp : forall s e, aval s (asimp e) = aval s e.
Proof.
  induction e; sauto.
  hammer_hook "imp2" "imp2.lem_aval_asimp.subgoal_1".
  Reconstr.htrivial Reconstr.AllHyps
                    (@lem_aval_plus)
                    Reconstr.Empty.
Qed.

Inductive bexpr :=
| Bval : bool -> bexpr
| Bnot : bexpr -> bexpr
| Band : bexpr -> bexpr -> bexpr
| Bless : aexpr -> aexpr -> bexpr.

Fixpoint bval (s : state) (e : bexpr) :=
  match e with
  | Bval b => b
  | Bnot e1 => negb (bval s e1)
  | Band e1 e2 => bval s e1 && bval s e2
  | Bless a1 a2 => aval s a1 <? aval s a2
  end.

Fixpoint not (e : bexpr) :=
  match e with
  | Bval true => Bval false
  | Bval false => Bval true
  | _ => Bnot e
  end.

Fixpoint and (e1 e2 : bexpr) :=
  match e1, e2 with
  | Bval true, _ => e2
  | _, Bval true => e1
  | Bval false, _ => Bval false
  | _, Bval false => Bval false
  | _, _ => Band e1 e2
  end.

Definition less (a1 a2 : aexpr) :=
  match a1, a2 with
  | Anum n1, Anum n2 => Bval (n1 <? n2)
  | _, _ => Bless a1 a2
  end.

Fixpoint bsimp (e : bexpr) :=
  match e with
  | Bnot e1 => not (bsimp e1)
  | Band e1 e2 => and (bsimp e1) (bsimp e2)
  | Bless a1 a2 => less a1 a2
  | _ => e
  end.

Lemma lem_bval_not : forall s e, bval s (not e) = negb (bval s e).
Proof.
  induction e; sauto.
Qed.

Lemma lem_bval_and : forall s e1 e2, bval s (and e1 e2) = bval s e1 && bval s e2.
Proof.
  induction e1; sauto.
Qed.

Lemma lem_bval_less : forall s a1 a2, bval s (less a1 a2) = (aval s a1 <? aval s a2).
Proof.
  induction a1; sauto.
Qed.

Lemma lem_bval_bsimp : forall s e, bval s (bsimp e) = bval s e.
Proof.
  induction e; sauto.
  hammer_hook "imp2" "imp2.lem_bval_bsimp.subgoal_1".
  Reconstr.htrivial Reconstr.AllHyps
                    (@lem_bval_not)
                    Reconstr.Empty.
  hammer_hook "imp2" "imp2.lem_bval_bsimp.subgoal_2".
  Reconstr.htrivial Reconstr.AllHyps
                    (@lem_bval_and)
                    Reconstr.Empty.
  scrush.
Qed.

Inductive com :=
| Skip : com
| Assign : vname -> aexpr -> com
| Seq : com -> com -> com
| If : bexpr -> com -> com -> com
| While : bexpr -> com -> com.

Definition update (s : state) x v y := if String.string_dec x y then v else s y.

Inductive big_step : com * state -> state -> Prop :=
| SkipSem : forall s, big_step (Skip, s) s
| AssignSem : forall s x a, big_step (Assign x a, s) (update s x (aval s a))
| SeqSem : forall c1 c2 s1 s2 s3, big_step (c1, s1) s2 -> big_step (c2, s2) s3 ->
                                  big_step (Seq c1 c2, s1) s3
| IfTrue : forall b c1 c2 s s', bval s b = true -> big_step (c1, s) s' ->
                                big_step (If b c1 c2, s) s'
| IfFalse : forall b c1 c2 s s', bval s b = false -> big_step (c2, s) s' ->
                                 big_step (If b c1 c2, s) s'
| WhileFalse : forall b c s, bval s b = false ->
                             big_step (While b c, s) s
| WhileTrue : forall b c s1 s2 s3,
    bval s1 b = true -> big_step (c, s1) s2 -> big_step (While b c, s2) s3 ->
    big_step (While b c, s1) s3.

Notation "A ==> B" := (big_step A B) (at level 80, no associativity).

Lemma lem_test_if : forall b s s', (If b Skip Skip, s) ==> s' -> s = s'.
Proof.
  hammer_hook "imp2" "imp2.lem_test_if".
  scrush.
Qed.

Lemma lem_assign_simp :
  forall a x s s', (Assign x a, s) ==> s' <-> s' = update s x (aval s a).
Proof.
  hammer_hook "imp2" "imp2.lem_assign_simp".
  sauto.
Qed.

Lemma lem_seq_assoc : forall c1 c2 c3 s s', (Seq c1 (Seq c2 c3), s) ==> s' <->
                                            (Seq (Seq c1 c2) c3, s) ==> s'.
Proof.
  hammer_hook "imp2" "imp2.lem_seq_assoc".
  pose SeqSem; sauto; eauto.
Qed.

Definition equiv_com (c1 c2 : com) := forall s s', (c1, s) ==> s' <-> (c2, s) ==> s'.

Notation "A ~~ B" := (equiv_com A B) (at level 70, no associativity).

Lemma lem_while_unfold : forall b c, While b c ~~ If b (Seq c (While b c)) Skip.
Proof.
  unfold equiv_com.
  intros; split.
  - hammer_hook "imp2" "imp2.lem_while_unfold.subgoal_1". intro H; inversion H; pose SkipSem; pose SeqSem; pose IfFalse; pose IfTrue; eauto.
  - hammer_hook "imp2" "imp2.lem_while_unfold.subgoal_2". intro H; inversion H; pose WhileTrue; pose WhileFalse; sauto; eauto.
Qed.

Lemma lem_triv_if : forall b c, If b c c ~~ c.
Proof.
  hammer_hook "imp2" "imp2.lem_triv_if".
  unfold equiv_com; sauto.
  - hammer_hook "imp2" "imp2.lem_triv_if.subgoal_1". scrush.
  - hammer_hook "imp2" "imp2.lem_triv_if.subgoal_2".
    destruct (bval s b) eqn:?.
    + eauto using IfTrue.
    + eauto using IfFalse.
Qed.


Lemma lem_commute_if :
  forall b1 b2 c11 c12 c2,
    If b1 (If b2 c11 c12) c2 ~~ If b2 (If b1 c11 c2) (If b1 c12 c2).
Proof.
  unfold equiv_com; split; intro H.
  - hammer_hook "imp2" "imp2.lem_commute_if.subgoal_1". inversion H; subst.
    + pose IfFalse; pose IfTrue; scrush.
    + destruct (bval s b2) eqn:?; eauto using IfFalse, IfTrue.
  - hammer_hook "imp2" "imp2.lem_commute_if.subgoal_2". inversion H; pose IfFalse; pose IfTrue; scrush.
Qed.

Lemma lem_while_cong_aux : forall b c c' s s', (While b c, s) ==> s' -> c ~~ c' ->
                                               (While b c', s) ==> s'.
Proof.
  assert (forall p s', p ==> s' -> forall b c c' s,
              p = (While b c, s) -> c ~~ c' -> (While b c', s) ==> s'); [idtac | scrush].
  intros p s' H.
  induction H; sauto.
  - hammer_hook "imp2" "imp2.lem_while_cong_aux.subgoal_1".
    Reconstr.hobvious Reconstr.AllHyps
                      (@WhileFalse)
                      Reconstr.Empty.
  - hammer_hook "imp2" "imp2.lem_while_cong_aux.subgoal_2".
    Reconstr.hsimple (@IHbig_step2, @H0, @H3, @H)
                (@WhileTrue)
                (@equiv_com).
Qed.

Lemma lem_while_cong : forall b c c', c ~~ c' -> While b c ~~ While b c'.
Proof.
  hammer_hook "imp2" "imp2.lem_while_cong".
  Reconstr.hobvious Reconstr.Empty
                    (@lem_while_cong_aux)
                    (@equiv_com).
Qed.

Lemma lem_sim_refl : forall c, c ~~ c.
Proof.
  hammer_hook "imp2" "imp2.lem_sim_refl".
  scrush.
Qed.

Lemma lem_sim_sym : forall c c', c ~~ c' -> c' ~~ c.
Proof.
  hammer_hook "imp2" "imp2.lem_sim_sym".
  scrush.
Qed.

Lemma lem_sim_trans : forall c1 c2 c3, c1 ~~ c2 -> c2 ~~ c3 -> c1 ~~ c3.
Proof.
  hammer_hook "imp2" "imp2.lem_sim_trans".
  unfold equiv_com; scrush.
Qed.

Lemma lem_big_step_deterministic :
  forall c s s1 s2, (c, s) ==> s1 -> (c, s) ==> s2 -> s1 = s2.
Proof.
  hammer_hook "imp2" "imp2.lem_big_step_deterministic".
  intros c s s1 s2 H.
  revert s2.
  induction H; try yelles 1.
  - scrush.
  - scrush.
  - scrush.
  - scrush.
  - scrush.
  - scrush.
  - intros s0 H2; inversion H2; scrush.
Qed.

Inductive instr :=
| LOADI : Z -> instr
| LOAD : vname -> instr
| ADD : instr
| STORE : vname -> instr
| JMP : Z -> instr
| JMPLESS : Z -> instr
| JMPGE : Z -> instr.

Definition stack := list val.
Definition config : Set := Z * state * stack.

Definition iexec (ins : instr) (cfg : config) : config :=
  match cfg with
  | (i, s, stk) =>
    match ins with
    | LOADI n => (i + 1, s, n :: stk)
    | LOAD x => (i + 1, s, s x :: stk)
    | ADD => (i + 1, s, hd 0 (tl stk) + hd 0 stk :: tl (tl stk))
    | STORE x => (i + 1, update s x (hd 0 stk), tl stk)
    | JMP n => (i + 1 + n, s, stk)
    | JMPLESS n => (if (hd 0 (tl stk)) <? hd 0 stk then i + 1 + n else i + 1, s, tl (tl stk))
    | JMPGE n => (if (hd 0 (tl stk)) >=? hd 0 stk then i + 1 + n else i + 1, s, tl (tl stk))
    end
  end.

Definition size (P : list instr) := Z.of_nat (length P).
Definition znth {A} (n : Z) (l : list A) (x : A) := nth (Z.to_nat n) l x.

Definition exec1 (P : list instr) (c c' : config) : Prop :=
  exists i s stk, c = (i,s,stk) /\ c' = iexec (znth i P ADD) (i,s,stk)
                  /\ i >= 0 /\ i < size P.

Inductive star {A : Type} (r : A -> A -> Prop) : A -> A -> Prop :=
| star_refl : forall x, star r x x
| star_step : forall x y z, r x y -> star r y z -> star r x z.

Lemma lem_star_trans {A} (r : A -> A -> Prop) :
  forall x y z, star r x y -> star r y z -> star r x z.
Proof.
  intros x y z H; revert z.
  induction H; sauto.
  hammer_hook "imp2" "imp2.lem_star_trans.subgoal_1".
  Reconstr.hobvious Reconstr.AllHyps
                    (@star_step)
                    Reconstr.Empty.
Qed.

Lemma star_step1 {A} (r : A -> A -> Prop) :
  forall x y, r x y -> star r x y.
Proof.
  hammer_hook "imp2" "imp2.star_step1".
  Reconstr.hobvious Reconstr.Empty
                    (@star_step, @star_refl)
                    Reconstr.Empty.
Qed.

Definition exec P := star (exec1 P).
Hint Unfold exec : yhints.

Lemma lem_exec1I :
  forall P i s stk c', c' = iexec (znth i P ADD) (i,s,stk) ->
                       0 <= i -> i < size P ->
                       exec1 P (i,s,stk) c'.
Proof.
  hammer_hook "imp2" "imp2.lem_exec1I".
  Reconstr.hobvious Reconstr.Empty
                    (@Coq.ZArith.BinInt.Z.lt_nge)
                    (@Coq.ZArith.BinInt.Z.ge, @znth, @exec1, @Coq.ZArith.BinInt.Z.lt).
Qed.

(* Helper instruction list functions *)

Lemma lem_n_succ_znth :
  forall {A} n (a : A) xs x, 0 <= n -> znth (n + 1) (a :: xs) x = znth n xs x.
Proof.
  hammer_hook "imp2" "imp2.lem_n_succ_znth".
  induction n; sauto.
  - hammer_hook "imp2" "imp2.lem_n_succ_znth.subgoal_1".
    Reconstr.htrivial Reconstr.AllHyps
                      (@Coq.PArith.Pnat.Pos2Nat.inj_succ, @Coq.PArith.BinPos.Pos.add_1_r)
                      Reconstr.Empty.
  - hammer_hook "imp2" "imp2.lem_n_succ_znth.subgoal_2".
    Reconstr.htrivial Reconstr.AllHyps
                      (@Coq.PArith.BinPos.Pos.add_1_r, @Coq.PArith.Pnat.Pos2Nat.inj_succ,
                       @Coq.ZArith.Znat.Z2Nat.inj_pos, @Coq.Init.Peano.eq_add_S)
                      (@znth).
Qed.

Lemma lem_znth_app :
  forall xs ys i x, i >= 0 -> znth (size xs + i) (xs ++ ys) x = znth i ys x.
Proof.
  assert (forall n (xs ys : list instr) i x, i >= 0 -> n = length xs ->
                                             znth (Z.of_nat n + i) (xs ++ ys) x = znth i ys x);
    [idtac | scrush].
  induction n.
  - hammer_hook "imp2" "imp2.lem_znth_app.subgoal_1". scrush.
  - hammer_hook "imp2" "imp2.lem_znth_app.subgoal_2".
    assert (HH: Z.of_nat (S n) = Z.of_nat n + 1).
    hammer_hook "imp2" "imp2.lem_znth_app.subgoal_3".
    Reconstr.htrivial Reconstr.Empty
                      (@Coq.ZArith.Znat.Nat2Z.inj_succ)
                      (@Coq.ZArith.BinIntDef.Z.succ).
    rewrite HH; clear HH.
    intros xs ys i x H1 H2.
    assert (0 <= Z.of_nat n + i) by omega.
    assert (HH: Z.of_nat n + 1 + i = (Z.of_nat n + i) + 1) by omega.
    rewrite HH; clear HH.
    destruct xs; [ scrush | simpl ].
    rewrite lem_n_succ_znth by scrush.
    scrush.
Qed.

Lemma lem_size_succ :
  forall a xs, size (a :: xs) = size xs + 1.
Proof.
  assert (forall n a xs, n = size xs -> size (a :: xs) = n + 1); [idtac | scrush].
  induction n; sauto.
  - hammer_hook "imp2" "imp2.lem_size_succ.subgoal_1". scrush.
  - hammer_hook "imp2" "imp2.lem_size_succ.subgoal_2".
    Reconstr.htrivial Reconstr.AllHyps
                      (@Coq.PArith.BinPos.Pplus_one_succ_r, @Coq.ZArith.Znat.Zpos_P_of_succ_nat,
                       @Coq.ZArith.BinInt.Pos2Z.inj_succ)
                      (@Coq.ZArith.BinIntDef.Z.succ, @size).
  - hammer_hook "imp2" "imp2.lem_size_succ.subgoal_3". scrush.
Qed.

Lemma lem_nth_append :
  forall xs ys i x, 0 <= i ->
                    znth i (xs ++ ys) x =
                    (if i <? size xs then znth i xs x else znth (i - size xs) ys x).
Proof.
  induction xs.
  - hammer_hook "imp2" "imp2.lem_nth_append.subgoal_1".
    sauto.
    + Reconstr.hcrush Reconstr.AllHyps
                  (@Coq.ZArith.BinInt.Z.ltb_ge)
                  Reconstr.Empty.
    + scrush.
  - intros.
    assert (HH: i = 0 \/ exists i', i = i' + 1 /\ 0 <= i').
    hammer_hook "imp2" "imp2.lem_nth_append.subgoal_2".
    Reconstr.hcrush Reconstr.AllHyps
                    (@Coq.ZArith.BinInt.Z.lt_le_pred, @Coq.ZArith.BinInt.Z.lt_eq_cases,
                     @Coq.ZArith.BinInt.Z.succ_pred)
                    (@Coq.ZArith.BinIntDef.Z.succ).
    destruct HH as [ ? | HH ].
    scrush.
    destruct HH as [ i' HH ].
    destruct HH.
    subst; simpl.
    repeat rewrite lem_n_succ_znth by scrush.
    repeat rewrite lem_size_succ.
    sauto.
    hammer_hook "imp2" "imp2.lem_nth_append.subgoal_3".
    + assert ((i' <? size xs) = true).
      hammer_hook "imp2" "imp2.lem_nth_append.subgoal_4".
      Reconstr.hcrush Reconstr.AllHyps
                      (@Coq.ZArith.BinInt.Z.le_gt_cases, @Coq.Bool.Bool.diff_true_false,
                       @Coq.ZArith.BinInt.Z.ltb_ge, @Coq.ZArith.Zbool.Zlt_is_lt_bool,
                       @Coq.ZArith.BinInt.Z.add_le_mono_r)
                      (@size).
      scrush.
    + assert ((i' <? size xs) = false).
      hammer_hook "imp2" "imp2.lem_nth_append.subgoal_5".
      Reconstr.heasy Reconstr.AllHyps
                     (@Coq.ZArith.BinInt.Z.ltb_nlt, @Coq.ZArith.BinInt.Z.add_lt_mono_r)
                     (@size).
      assert (i' + 1 - (size xs + 1) = i' - size xs) by auto with zarith.
      scrush.
Qed.

Lemma lem_size_app : forall xs ys, size (xs ++ ys) = size xs + size ys.
Proof.
  hammer_hook "imp2" "imp2.lem_size_app".
  Reconstr.htrivial Reconstr.Empty
                    (@Coq.ZArith.Znat.Nat2Z.inj_add, @Coq.Lists.List.app_length)
                    (@size).
Qed.

Lemma lem_size_app_le : forall xs ys, size xs <= size (xs ++ ys).
Proof.
  hammer_hook "imp2" "imp2.lem_size_app_le".
  Reconstr.hobvious Reconstr.Empty
                    (@Coq.Arith.Plus.le_plus_l, @Coq.ZArith.Znat.Nat2Z.inj_le, @Coq.Lists.List.app_length)
                    (@size).
Qed.

(* Verification infrastructure *)

Lemma lem_iexec_shift :
  forall x n i i' s s' stk stk',
    (n+i',s',stk') = iexec x (n+i,s,stk) <->
    (i',s',stk') = iexec x (i,s,stk).
Proof.
  split; intro H.
  - assert (forall n i i' k, n + i' = n + i + k -> i' = i + k) by auto with zarith.
    assert (forall n i i' k, n + i' = n + i + 1 + k -> i' = i + 1 + k) by auto with zarith.
    scrush.
  - assert (forall n i i' k, i' = i + k -> n + i' = n + i + k) by auto with zarith.
    assert (forall n i, n + (i + 1) = n + i + 1) by auto with zarith.
    hammer_hook "imp2" "imp2.lem_iexec_shift.subgoal_1".
    scrush. (* takes 5s *)
Qed.

Lemma lem_exec1_hlp1 :
  forall n P P', 0 <= n -> n < size P ->
                 znth n P ADD = znth n (P ++ P') ADD.
Proof.
  induction n.
  - hammer_hook "imp2" "imp2.lem_exec1_hlp1.subgoal_1". scrush.
  - hammer_hook "imp2" "imp2.lem_exec1_hlp1.subgoal_2".
    Reconstr.hcrush Reconstr.Empty
                    (@lem_size_succ, @lem_nth_append, @Coq.ZArith.Zbool.Zlt_is_lt_bool)
                    Reconstr.Empty.
  - scrush.
Qed.

Lemma lem_exec1_appendR :
  forall P P' c c', exec1 P c c' -> exec1 (P ++ P') c c'.
Proof.
  unfold exec1.
  intros; simp_hyps.
  hammer_hook "imp2" "imp2.lem_exec1_appendR".
  exists i.
  exists s.
  exists stk.
  rewrite <- lem_exec1_hlp1 by auto with zarith.
  hammer_hook "imp2" "imp2.lem_exec1_appendR.subgoal_1".
  assert (i < size (P ++ P')).
  hammer_hook "imp2" "imp2.lem_exec1_appendR.subgoal_2".
  Reconstr.heasy Reconstr.AllHyps
                 (@lem_size_app_le, @Coq.ZArith.BinInt.Z.le_lt_trans,
                  @Coq.ZArith.BinInt.Z.nle_gt, @Coq.ZArith.BinInt.Z.lt_ge_cases)
                 (@size).
  scrush.
Qed.

Lemma lem_exec_appendR : forall P P' c c', exec P c c' -> exec (P ++ P') c c'.
Proof.
  unfold exec.
  intros P P' c c' H.
  induction H.
  - scrush.
  - hammer_hook "imp2" "imp2.lem_exec_appendR.subgoal_1". pose @star_step; pose lem_exec1_appendR; scrush.
Qed.

Lemma lem_exec1_appendL :
  forall i i' P P' s s' stk stk', exec1 P (i,s,stk) (i',s',stk') ->
                                  exec1 (P' ++ P) (size P' + i,s,stk) (size P' + i',s',stk').
Proof.
  unfold exec1.
  intros; simp_hyps.
  exists (size P' + i0).
  exists s0.
  exists stk0.
  rewrite lem_znth_app by scrush.
  hammer_hook "imp2" "imp2.lem_exec1_appendL.subgoal_1".
  split; [ scrush | split ].
  - hammer_hook "imp2" "imp2.lem_exec1_appendL.subgoal_2".
    Reconstr.htrivial Reconstr.AllHyps
                      (@lem_iexec_shift)
                      Reconstr.Empty.
  - split.
    + hammer_hook "imp2" "imp2.lem_exec1_appendL.subgoal_3".
      Reconstr.hobvious Reconstr.AllHyps
                        (@Coq.ZArith.Zorder.Zle_0_nat, @Coq.ZArith.BinInt.Z.nle_gt,
                         @Coq.ZArith.BinInt.Z.add_neg_cases)
                        (@size, @Coq.ZArith.BinInt.Z.ge, @Coq.ZArith.BinInt.Z.lt).
    + hammer_hook "imp2" "imp2.lem_exec1_appendL.subgoal_4".
      Reconstr.hobvious Reconstr.AllHyps
                        (@lem_size_app, @Coq.ZArith.BinInt.Z.add_lt_mono_l)
                        (@size).
Qed.

Lemma lem_exec_appendL :
  forall i i' P P' s s' stk stk', exec P (i,s,stk) (i',s',stk') ->
                                  exec (P' ++ P) (size P' + i,s,stk) (size P' + i',s',stk').
Proof.
  assert (forall c c' P, exec P c c' ->
                       forall i i' P' s s' stk stk',
                         c = (i,s,stk) -> c' = (i',s',stk') ->
                         exec (P' ++ P) (size P' + i,s,stk) (size P' + i',s',stk')); [idtac|scrush].
  unfold exec.
  intros c c' P H.
  induction H.
  - scrush.
  - hammer_hook "imp2" "imp2.lem_exec_appendL.subgoal_1".
    intros; simp_hyps; subst.
    destruct y as [ p stk0 ].
    destruct p as [ i0 s0 ].
    hammer_hook "imp2" "imp2.lem_exec_appendL.subgoal_2".
    pose @star_step; pose lem_exec1_appendL; scrush.
Qed.

Lemma lem_exec_Cons_1 :
  forall ins P j s t stk stk',
    exec P (0,s,stk) (j,t,stk') ->
    exec (ins :: P) (1,s,stk) (1+j,t,stk').
Proof.
  hammer_hook "imp2" "imp2.lem_exec_Cons_1".
  intros ins P j.
  assert (HH: ins :: P = (ins :: nil) ++ P) by auto with datatypes.
  rewrite HH; clear HH.
  assert (HH: 1 + j = size (ins :: nil) + j) by scrush.
  rewrite HH; clear HH.
  assert (HH: 1 = size (ins :: nil) + 0) by scrush.
  rewrite HH; clear HH.
    hammer_hook "imp2" "imp2.lem_exec_Cons_1.subgoal_1".
  pose lem_exec_appendL; scrush.
Qed.

Lemma lem_exec_appendL_if :
  forall i i' j P P' s s' stk stk',
    size P' <= i -> exec P (i - size P',s,stk) (j,s',stk') -> i' = size P' + j ->
    exec (P' ++ P) (i,s,stk) (i',s',stk').
Proof.
  intros.
  pose (k := i - size P').
  assert (HH: i = size P' + k).
  hammer_hook "imp2" "imp2.lem_exec_appendL_if.subgoal_1".
  Reconstr.htrivial Reconstr.Empty
                    (@Coq.ZArith.BinInt.Zplus_minus)
                    (@k).
  rewrite HH; clear HH.
  hammer_hook "imp2" "imp2.lem_exec_appendL_if.subgoal_2".
  pose lem_exec_appendL; scrush.
Qed.

Lemma lem_exec_append_trans :
  forall i' i'' j'' P P' s s' s'' stk stk' stk'',
    exec P (0,s,stk) (i',s',stk') -> size P <= i' ->
    exec P' (i' - size P,s',stk') (i'',s'',stk'') ->
    j'' = size P + i'' ->
    exec (P ++ P') (0,s,stk) (j'',s'',stk'').
Proof.
  hammer_hook "imp2" "imp2.lem_exec_append_trans".
  intros.
  assert (exec (P ++ P') (i',s',stk') (j'',s'',stk'')) by
      (apply lem_exec_appendL_if with (j := i''); sauto).
  assert (exec (P ++ P') (0,s,stk) (i',s',stk')) by
      (apply lem_exec_appendR; sauto).
  hammer_hook "imp2" "imp2.lem_exec_append_trans.subgoal_1".
  pose @lem_star_trans; scrush.
Qed.

Ltac escrush := unfold exec; pose @star_step; pose @star_refl; scrush.

Ltac exec_tac :=
  match goal with
  | [ |- exec ?A (?i, ?s, ?stk) ?B ] =>
    assert (exec1 A (i, s, stk) B) by
        (unfold exec1; exists i; exists s; exists stk; sauto);
    escrush
  end.

Ltac exec_append_tac :=
  intros; assert (H_exec_append_tac: forall l, size l - size l = 0) by (intro; omega);
  match goal with
  | [ |- exec (?l1 ++ ?l2) (0,?s,?stk) (size(?l1 ++ ?l2), ?s, ?a :: ?b :: ?stk) ] =>
    rewrite lem_size_app;
    apply lem_exec_append_trans with
    (i' := size(l1)) (i'' := size(l2)) (s' := s) (stk' := b :: stk);
    solve [ omega | ycrush | scrush ]
  | [ H1 : exec ?l1 (0,?s,?stk) (size(?l1), ?s1, ?stk1),
      H2 : exec ?l2 (0,?s1,?stk1) (size(?l2), ?s2, ?stk2)
      |- exec (?l1 ++ ?l2) (0,?s,?stk) (size(?l1 ++ ?l2), ?s2, ?stk2) ] =>
    rewrite lem_size_app;
    apply lem_exec_append_trans with
    (i' := size(l1)) (i'' := size(l2)) (s' := s1) (stk' := stk1);
    solve [ omega | ycrush | scrush ]
  | [ H1 : exec ?l1 (0,?s,?stk) (size(?l1), ?s1, ?stk1),
      H2 : exec ?l2 (0,?s1,?stk1) (size(?l2) + ?i, ?s2, ?stk2)
      |- exec (?l1 ++ ?l2) (0,?s,?stk) (size(?l1 ++ ?l2) + ?i, ?s2, ?stk2) ] =>
    rewrite lem_size_app;
    apply lem_exec_append_trans with
    (i' := size(l1)) (i'' := size(l2) + i) (s' := s1) (stk' := stk1);
    solve [ omega | ycrush | scrush ]
  end;
  clear H_exec_append_tac.

Ltac exec_append3_tac :=
  intros;
  match goal with
  | [ H2: exec ?l2 (0,?s1,?stk1) (size(?l2),?s2,?stk2),
      H3: exec ?l3 (0,?s2,?stk2) (size(?l3),?s3,?stk3)
      |- exec (?l1 ++ ?l2 ++ ?l3) (0,?s,?stk) (size(?l1 ++ ?l2 ++ ?l3), ?s3, ?stk3) ] =>
    assert (exec (l2 ++ l3) (0,s1,stk1) (size(l2 ++ l3),s3,stk3)) by exec_append_tac;
    exec_append_tac
  | [ H2: exec ?l2 (0,?s1,?stk1) (size(?l2),?s2,?stk2),
      H3: exec ?l3 (0,?s2,?stk2) (size(?l3) + ?i,?s3,?stk3)
      |- exec (?l1 ++ ?l2 ++ ?l3) (0,?s,?stk) (size(?l1 ++ ?l2 ++ ?l3) + ?i, ?s3, ?stk3) ] =>
    assert (exec (l2 ++ l3) (0,s1,stk1) (size(l2 ++ l3) + i,s3,stk3)) by exec_append_tac;
    exec_append_tac
  end.

(* Compilation *)

Fixpoint acomp (a : aexpr) : list instr :=
  match a with
  | Anum n => LOADI n :: nil
  | Avar x => LOAD x :: nil
  | Aplus a1 a2 => acomp a1 ++ acomp a2 ++ (ADD :: nil)
  end.

Lemma lem_acomp_correct :
  forall a s stk, exec (acomp a) (0, s, stk) (size(acomp a), s, aval s a :: stk).
Proof.
  induction a; sauto.
  - exec_tac.
  - exec_tac.
  - assert (exec (acomp a1 ++ acomp a2) (0,s,stk)
                 (size(acomp a1 ++ acomp a2),s,aval s a2 :: aval s a1 :: stk)) by exec_append_tac.
    assert (exec (ADD :: nil) (0,s,aval s a2 :: aval s a1 :: stk) (1,s,(aval s a1 + aval s a2) :: stk)) by
        exec_tac.
    assert (forall l, size l - size l = 0) by (intro; omega);
    assert (HH: exec ((acomp a1 ++ acomp a2) ++ ADD :: nil) (0, s, stk)
                     (size ((acomp a1 ++ acomp a2) ++ ADD :: nil), s, aval s a1 + aval s a2 :: stk)) by
        (apply lem_exec_append_trans with
         (i' := size(acomp a1 ++ acomp a2)) (s' := s) (stk' := aval s a2 :: aval s a1 :: stk) (i'' := 1);
         solve [ sauto | ycrush | rewrite lem_size_app; scrush ]).
    clear -HH; scrush.
Qed.

Lemma lem_acomp_append :
   forall a1 a2 s stk, exec (acomp a1 ++ acomp a2) (0, s, stk)
                            (size (acomp a1 ++ acomp a2), s, aval s a2 :: aval s a1 :: stk).
Proof.
  hammer_hook "imp2" "imp2.lem_acomp_append".
  pose lem_acomp_correct; exec_append_tac.
Qed.

Fixpoint bcomp (b : bexpr) (f : bool) (n : Z) : list instr :=
  match b with
  | Bval v => if eqb v f then JMP n :: nil else nil
  | Bnot b' => bcomp b' (negb f) n
  | Band b1 b2 =>
    let cb2 := bcomp b2 f n in
    let m := if f then size cb2 else size cb2 + n in
    let cb1 := bcomp b1 false m in
    cb1 ++ cb2
  | Bless a1 a2 =>
    acomp a1 ++ acomp a2 ++ (if f then JMPLESS n :: nil else JMPGE n :: nil)
  end.

Lemma lem_bcomp_correct :
  forall b f n s stk, 0 <= n ->
                      exec (bcomp b f n) (0,s,stk)
                           (size(bcomp b f n) + (if eqb f (bval s b) then n else 0),s,stk).
Proof.
  induction b; simpl; intros f n s stk H.
  - sauto; try exec_tac;
      Reconstr.hsimple Reconstr.AllHyps
                       (@Coq.Bool.Bool.eqb_false_iff, @Coq.Bool.Bool.eqb_prop)
                       Reconstr.Empty.
  - assert (HH: (if eqb f (negb (bval s b)) then n else 0) =
                (if eqb (negb f) (bval s b) then n else 0)).
    hammer_hook "imp2" "imp2.lem_bcomp_correct.subgoal_1".
    Reconstr.hsimple Reconstr.Empty
                     (@Coq.Bool.Bool.eqb_negb2, @Coq.Bool.Bool.negb_false_iff,
                      @Coq.Bool.Bool.negb_true_iff, @Coq.Bool.Bool.no_fixpoint_negb,
                      @Coq.Bool.Bool.negb_involutive, @Coq.Bool.Bool.diff_true_false,
                      @Coq.Bool.Bool.eqb_false_iff, @Coq.Bool.Bool.eqb_prop)
                     (@Coq.Bool.Bool.eqb, @Coq.Init.Datatypes.negb).
    rewrite HH; clear HH.
    scrush.
  - pose (m := if f then size (bcomp b2 f n) else size (bcomp b2 f n) + n); fold m.
    assert (H0: 0 <= m) by
        (unfold m; clear -H; sauto; unfold size; omega).
    destruct (bval s b1) eqn:H1; simpl.
    + apply lem_exec_append_trans with
      (i' := size (bcomp b1 false m))
        (s' := s) (stk' := stk)
        (i'' := size (bcomp b2 f n) + (if eqb f (bval s b2) then n else 0)).
      * generalize (IHb1 false m s stk); scrush.
      * auto with zarith.
      * assert (HH: size (bcomp b1 false m) - size (bcomp b1 false m) = 0) by omega.
        rewrite HH; clear HH.
        auto.
      * rewrite lem_size_app; auto with zarith.
    + rewrite lem_size_app.
      assert (HH: size (bcomp b2 f n) + (if eqb f false then n else 0) = m) by
          (unfold m; destruct f; simpl; omega).
      rewrite <- ZArith.BinInt.Z.add_assoc; rewrite HH; clear HH.
      apply lem_exec_appendR.
      assert (HH: size (bcomp b1 false m) + m =
                  size (bcomp b1 false m) + if eqb false (bval s b1) then m else 0) by scrush.
      rewrite HH; clear HH.
      auto.
  - assert (HH: aval s a >=? aval s a0 = negb (aval s a <? aval s a0)).
    hammer_hook "imp2" "imp2.lem_bcomp_correct.subgoal_2".
    Reconstr.htrivial Reconstr.Empty
                      (@Coq.ZArith.BinInt.Z.geb_leb, @Coq.Bool.Bool.negb_true_iff,
                       @Coq.ZArith.BinInt.Z.leb_antisym)
                      Reconstr.Empty.
    assert (exec (if f then JMPLESS n :: nil else JMPGE n :: nil) (0, s, aval s a0 :: aval s a :: stk)
                 (size (if f then JMPLESS n :: nil else JMPGE n :: nil) +
                  (if eqb f (aval s a <? aval s a0) then n else 0), s, stk)) by
        (sauto; exec_tac).
    clear HH.
    assert (HH: forall (l1 l2 l3 : list instr), l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3) by scrush.
    repeat rewrite HH; clear HH.
    pose proof (lem_acomp_append a a0 s stk).
    exec_append_tac.
Qed.

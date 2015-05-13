Require Export Imp.

(* First we define syntax of the language *)

(* We could reuse aexp and bexp defined for Imp. *)

(* Redefine commands here. To distinguish them
   from Imp commands, we call them scom *)
(* You need to change it into an inductive definition *)
Inductive scom : Type :=
  | SCSkip : scom
  | SCAss : id -> aexp -> scom
  | SCSeq : scom -> scom -> scom
  | SCIf : bexp -> scom -> scom -> scom
  | SCWhile : bexp -> scom -> scom
  | SCCons : id -> aexp -> aexp -> scom
  | SCLookup : id -> aexp -> scom
  | SCMutation : aexp -> aexp -> scom
  | SCDispose : aexp -> scom.

(* Program states, which is called sstate *)
Definition store := id -> nat.

(* if heap maps a natural number (address) to
   None, we say the address is not a valid address,
   or it is not in the domain of the heap *)
Definition heap := nat -> option nat.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

(* Define an empty heap, which contains no memory cells *)
Definition emp_heap : heap :=
  fun (l: nat) => None.

Definition in_dom (l: nat) (h: heap) : Prop :=
  exists n, h l = Some n.

Definition not_in_dom (l: nat) (h: heap) : Prop :=
  h l = None.

Theorem in_not_in_dec :
  forall l h, {in_dom l h} + {not_in_dom l h}.
Proof.
  intros l h. unfold in_dom. unfold not_in_dom.
  destruct (h l).
  left. exists n. auto.
  right. auto.
Defined.

(* h1 and h2 have disjoint domain *)
Definition disjoint (h1 h2: heap) : Prop :=
  forall l, not_in_dom l h1 \/ not_in_dom l h2.

(* union of two heaps *)
Definition h_union (h1 h2: heap) : heap :=
  fun l =>
    if (in_not_in_dec l h1) then h1 l else h2 l.

(* h1 is a subset of h2 *)
Definition h_subset (h1 h2: heap) : Prop :=
  forall l n, h1 l = Some n -> h2 l = Some n.

(* store update *)
Definition st_update (s: store) (x: id) (n: nat) : store :=
  fun x' => if eq_id_dec x x' then n else s x'.

(* heap update *)
Definition h_update (h: heap) (l: nat) (n: nat) : heap :=
  fun l' => if eq_nat_dec l l' then Some n else h l'.

Definition sstate := (store * heap) %type.

(* since program may abort, we extend our state
   definition to add a special state Abt *)
Inductive ext_state : Type :=
  St:  sstate -> ext_state    (* normal state *)
| Abt: ext_state.             (* abort *)


(* Next we define the operational semantics *)

(* big-step semantics. You should change it into
   an inductive definition *)
Inductive big_step:
  scom * sstate -> ext_state -> Prop :=
| SE_Skip : forall sst,
              big_step (SCSkip, sst) (St sst)
| SE_Ass  : forall st h a1 n x,
             aeval st a1 = n ->
             big_step (SCAss x a1, (st, h)) (St (st_update st x n, h))
| SE_Seq : forall c1 c2 sst sst' est,
            big_step (c1, sst) (St sst') ->
            big_step (c2, sst') est ->
            big_step (SCSeq c1 c2, sst) est
| SE_Seq_Ab : forall c1 c2 sst,
                big_step (c1, sst) Abt ->
                big_step (SCSeq c1 c2, sst) Abt
| SE_IfTrue : forall st h b c1 c2 est,
               beval st b = true ->
               big_step (c1, (st, h)) est ->
               big_step (SCIf b c1 c2, (st, h)) est
| SE_IfFalse : forall st h b c1 c2 est,
               beval st b = false ->
               big_step (c2, (st, h)) est ->
               big_step (SCIf b c1 c2, (st, h)) est
| SE_WhileEnd : forall b st h c,
                 beval st b = false ->
                 big_step (SCWhile b c, (st, h)) (St (st, h))
| SE_WhileLoop : forall st h est b c,
                  beval st b = true ->
                  big_step (SCSeq c (SCWhile b c), (st, h)) est ->
                  big_step (SCWhile b c, (st, h)) est
| SE_Cons : forall st h a1 a2 n1 n2 x l,
              aeval st a1 = n1 ->
              aeval st a2 = n2 ->
              h l = None ->
              h (l + 1) = None ->
              big_step (SCCons x a1 a2, (st, h))
                       (St (st_update st x l,
                            h_update (h_update h (l + 1) n2) l n1))
| SE_Lookup : forall st h x a1 n1 n2,
                aeval st a1 = n1 ->
                h n1 = Some n2 ->
                big_step (SCLookup x a1, (st, h)) (St (st_update st x n2, h))
| SE_Lookup_Ab : forall st a1 n1 h x,
                   aeval st a1 = n1 ->
                   h n1 = None ->
                   big_step (SCLookup x a1, (st, h)) Abt
| SE_Mutation : forall st h a1 a2 n1 n2,
                  aeval st a1 = n1 ->
                  aeval st a2 = n2 ->
                  in_dom n1 h ->
                  big_step (SCMutation a1 a2, (st, h)) (St (st, h_update h n1 n2))
| SE_Mutation_Ab : forall st h a1 a2 n1,
                     aeval st a1 = n1 ->
                     h n1 = None ->
                     big_step (SCMutation a1 a2, (st, h)) Abt
| SE_Dispose : forall st h a1 n1,
                 aeval st a1 = n1 ->
                 in_dom n1 h ->
                 big_step
                   (SCDispose a1, (st, h))
                   (St (st, fun x => if eq_nat_dec x n1 then None else h x))
| SE_Dispose_Ab : forall st h a1 n1,
                    aeval st a1 = n1 ->
                    h n1 = None ->
                    big_step (SCDispose a1, (st, h)) Abt.

(* small-step semantics. Should be inductive too *)
Inductive small_step:
   scom * ext_state -> scom * ext_state -> Prop :=
| S_Ass : forall st h a n x,
            aeval st a = n ->
            small_step (SCAss x a, St (st, h))
                       (SCSkip, St (st_update st x n, h))
| S_SeqStep : forall c1 c1' est est' c2,
                small_step (c1, est) (c1', est') ->
                small_step (SCSeq c1 c2, est) (SCSeq c1' c2, est')
| S_SeqFinish : forall c2 est,
                  small_step (SCSeq SCSkip c2, est) (c2, est)
| S_IfTrue : forall st h b c1 c2,
               beval st b = true ->
               small_step (SCIf b c1 c2, St (st, h)) (c1, St (st, h))
| S_IfFalse : forall st h b c1 c2,
                beval st b = false ->
                small_step (SCIf b c1 c2, St (st, h)) (c2, St (st, h))
| S_WhileEnd : forall st h b c,
                 beval st b = false ->
                 small_step (SCWhile b c, St (st, h)) (SCSkip, St (st, h))
| S_WhileLoop : forall st h b c,
                  beval st b = true ->
                  small_step (SCWhile b c, St (st, h))
                             (SCSeq c (SCWhile b c), St (st, h))
| S_Cons : forall st h x a1 a2 n1 n2 l,
             aeval st a1 = n1 ->
             aeval st a2 = n2 ->
             h l = None ->
             h (l + 1) = None ->
             small_step (SCCons x a1 a2, St (st, h))
                        (SCSkip, St (st_update st x l,
                                     h_update (h_update h l n1)
                                              (l + 1) n2))
| S_Lookup : forall st h x a1 n1 n2,
               aeval st a1 = n1 ->
               h n1 = Some n2 ->
               small_step (SCLookup x a1, St (st, h))
                          (SCSkip, St (st_update st x n2, h))
| S_Lookup_Ab : forall st h x a1 n1,
                  aeval st a1 = n1 ->
                  h n1 = None ->
                  small_step (SCLookup x a1, St (st, h))
                             (SCSkip, Abt)
| S_Mutation : forall st h a1 a2 n1 n2,
                  aeval st a1 = n1 ->
                  aeval st a2 = n2 ->
                  in_dom n1 h ->
                  small_step (SCMutation a1 a2, St (st, h))
                             (SCSkip, St (st, h_update h n1 n2))
| S_Mutation_Ab : forall st h a1 a2 n1,
                    aeval st a1 = n1 ->
                    h n1 = None ->
                    small_step (SCMutation a1 a2, St (st, h))
                               (SCSkip, Abt)
| S_Dispose : forall st h a1 n1,
                aeval st a1 = n1 ->
                in_dom n1 h ->
                small_step
                  (SCDispose a1, St (st, h))
                  (SCSkip, St
                   (st, fun x => if eq_nat_dec x n1 then None else h x))
| S_Dispose_Ab : forall st h a1 n1,
                   aeval st a1 = n1 ->
                   h n1 = None ->
                   small_step (SCDispose a1, St (st, h))
                              (SCSkip, Abt).

Hint Constructors small_step.

(** Assertions **)
Definition sass := sstate -> Prop.

(* define semantics of assertion emp *)
Definition emp : sass :=
    fun st: sstate =>
      snd st = emp_heap.

(* assertion e1 |-> e2 *)
Definition pto (e1 e2: aexp) : sass :=
    fun st: sstate =>
      match st with
      | (s, h) => h = h_update emp_heap (aeval s e1) (aeval s e2)
      end.
Notation "e1 '|->' e2" := (pto e1 e2) (at level 60).

(* p * q *)
Definition star (p q : sass) : sass :=
    fun st: sstate =>
      match st with
      | (s, h) =>
        exists h1, exists h2,
          disjoint h1 h2 /\ h_union h1 h2 = h /\ p (s, h1) /\ q (s, h2)
      end.
Notation "p '**' q" := (star p q) (at level 70).

(* p --* q *)
Definition simp (p q: sass) : sass :=
  fun (st : sstate) =>
    match st with
    | (s, h) =>
      forall h', disjoint h' h -> p (s, h') -> q (s, h_union h h')
    end.
Notation "p '--*' q" := (simp p q) (at level 80).


Definition pure (p: sass) : Prop :=
  forall s h1 h2, p (s, h1) -> p (s, h2).

Definition precise (p: sass) : Prop :=
  forall h h1 h2 s,
     h_subset h1 h
     -> h_subset h2 h
     -> p (s, h1)
     -> p (s, h2)
     -> h1 = h2.

Definition intuitionistic (p: sass) : Prop :=
  forall s h h', p (s, h) -> disjoint h h' -> p (s, h_union h h').


(* continue here *)

Definition s_conj (p q: sass) : sass :=
  fun (s: sstate) => p s /\ q s.
Notation "p '//\\' q" := (s_conj p q) (at level 75).

Definition s_disj (p q: sass) : sass :=
  fun (s: sstate) => p s \/ q s.
Notation "p '\\//' q" := (s_disj p q) (at level 78).

Definition s_imp (p q: sass) : sass :=
  fun (s: sstate) => p s -> q s.
Notation "p '~~>' q" := (s_imp p q) (at level 85).

Definition strongerThan (p q: sass) : Prop :=
  forall s: sstate, s_imp p q s.
Notation "p '==>' q" := (strongerThan p q) (at level 90).

Definition spEquiv (p q: sass) : Prop :=
  (p ==> q) /\ (q ==> p).
Notation "p '<==>' q" := (spEquiv p q) (at level 90).

(* Prove the following lemmas *)
Lemma disj_star_distr: forall (p q r: sass),
  (p \\// q) ** r <==> (p ** r) \\// (q ** r).
Proof.
  split; unfold strongerThan, s_imp; intros; destruct s.
  destruct H as [h1 [h2 [H1 [H2 [H3 H4]]]]].
  destruct H3. left. exists h1. eauto. right. exists h1. eauto.
  destruct H; destruct H as [h1 [h2 [H1 [H2 [H3 H4]]]]];
  exists h1; exists h2; repeat split; eauto.
  left. auto. right. auto.
Qed.

Lemma conj_star_distr: forall (p q r: sass),
  (p //\\ q) ** r ==> (p ** r) //\\ (q ** r).
Proof.
  unfold strongerThan, s_imp. intros. destruct s.
  destruct H as [h1 [h2 [H1 [H2 [H3 H4]]]]]. destruct H3.
  split; exists h1; exists h2; eauto.
Qed.

Lemma h_union_subst:
  forall h1 h2 h, h_union h1 h2 = h ->
             disjoint h1 h2 ->
              h_subset h2 h.
Proof.
  unfold h_subset, h_union. intros;
  subst; destruct (in_not_in_dec l h1); auto.
  destruct (H0 l); destruct i; unfold not_in_dom in H;
  congruence.
Qed.

Lemma h_union_determ:
  forall h1 h1' h2, h_union h1 h2 = h_union h1' h2 ->
               disjoint h1 h2 ->
               disjoint h1' h2 ->
               h1 = h1'.
Proof.
  intros.
  apply functional_extensionality. intros.
  assert ((h_union h1 h2) x = (h_union h1' h2) x). rewrite H. reflexivity.
  unfold h_union in H2.
  destruct (in_not_in_dec x h1);
  destruct (in_not_in_dec x h1'); eauto.
  destruct i. destruct (H0 x). congruence. rewrite H3 in H2. congruence.
  destruct i. destruct (H1 x). congruence. rewrite H3 in H2. congruence.
  unfold not_in_dom in *. rewrite n. rewrite n0. reflexivity.
Qed.

Hint Resolve h_union_subst.
Hint Resolve h_union_determ.

Lemma precise_conj_distr: forall (p q r: sass),
  precise r -> (p ** r) //\\ (q ** r) ==> (p //\\ q) ** r.
Proof.
  unfold strongerThan, s_imp. intros. destruct s.
  destruct H0.
  destruct H0 as [h1 [h2 [H2 [H3 [H4 H5]]]]].
  destruct H1 as [h1' [h2' [H2' [H3' [H4' H5']]]]].
  unfold precise in H.
  assert (h2 = h2'). eapply H; eauto. subst.
  assert (h1 = h1'). eauto. subst.
  exists h1'. exists h2'. repeat split; eauto.
Qed.

Inductive multiStep :
    scom * ext_state -> scom * ext_state -> Prop :=
| step0: forall c s, multiStep (c, s) (c, s)
| stepn: forall c s c' s' c'' s'',
           small_step (c, s) (c', s')
           -> multiStep (c', s') (c'', s'')
           -> multiStep (c, s) (c'', s'').

(* c is safe at state s *)
Definition safeAt (c: scom) (s: sstate) : Prop :=
(* ~ multiStep (c, St s) Abt *)

forall c' s',
  multiStep (c, St s) (c', St s')
  -> c' = SCSkip \/ exists c'', exists s'', small_step (c', St s') (c'', St s'').

Definition safeMono (c: scom) : Prop :=

  forall s h h',
    safeAt c (s, h) -> disjoint h h' -> safeAt c (s, h_union h h').

Definition frame (c: scom) : Prop :=
  forall s h1 h2 c' s' h',
    safeAt c (s, h1)
    -> disjoint h1 h2
    -> small_step (c, St (s, h_union h1 h2)) (c', St (s', h'))
    -> exists h1',
         small_step (c, St (s, h1)) (c', St (s', h1'))
         /\ disjoint h1' h2
         /\ h_union h1' h2 = h'.

(* Lemma small_step_mono: *)
(*   forall c c' s s' h1 h2 h', *)
(*     small_step (c, St (s, h1)) (c', St (s', h')) -> *)
(*     disjoint h1 h2 -> *)
(*     exists s'', exists h'', small_step (c, St (s, h_union h1 h2)) (c', St (s'', h'')). *)
(* Proof. *)
(*   induction c; intros; inversion H; subst; eauto. *)
(*   destruct (IHc1 c1' s s' h1 h2 h' H2 H0) as [s'' [h'' H_s]]. *)
(*   exists s''. eauto.  *)

Lemma not_safe : ~ safeMono (SCCons X (ANum 1) (ANum 1)).
Proof.
  intro H. unfold safeMono in H.
  assert (safeAt (SCCons X (ANum 1) (ANum 1)) (fun id => 0, emp_heap)).
  unfold safeAt. intros. inversion H0; subst. right.
  exists SCSkip.
  exists (st_update (fun id => 0) X 1, h_update (h_update emp_heap 1 1) 2 1).
  econstructor; eauto. inversion H4; subst. inversion H6; subst; auto.
  inversion H5.
  assert (disjoint emp_heap (fun n => Some 1)).
  unfold disjoint, not_in_dom. intros. left. reflexivity.
  assert (h_union emp_heap (fun n => Some 1) = fun n => Some 1). reflexivity.
  eapply H in H0; eauto. rewrite H2 in *.
  unfold safeAt in H0.
  assert (multiStep (SCCons X (ANum 1) (ANum 1), St (fun _ => 0, fun _ => Some 1))
                    (SCCons X (ANum 1) (ANum 1), St (fun _ => 0, fun _ => Some 1))). constructor.
  apply H0 in H3. destruct H3. inversion H3.
  destruct H3 as [c'' [s'' H_s]].
  inversion H_s. inversion H12.
Qed.


Theorem locality: forall c : scom, safeMono c /\ frame c.
Proof.
  intros. split.
  Case "safeMono".
  induction c;
  unfold safeMono, safeAt; intros.
  SCase "skip".
  inversion H1; subst. auto. inversion H5.
  SCase "ass".
  inversion H1; subst. right.
  exists SCSkip. exists (st_update s i (aeval s a), h_union h h'). eauto.
  inversion H5; subst. inversion H7; subst; eauto. inversion H6.
  SCase "seq".
  inversion H1; subst. right. clear H1.
  assert (SCSeq c1 c2 = SCSkip \/
           (exists c'' s'', small_step (SCSeq c1 c2, St (s, h)) (c'', St s''))).
  apply H. constructor. destruct H1. inversion H1. destruct H1 as [c'' [s'' H_s]].
  inversion H_s; subst.
  Abort.
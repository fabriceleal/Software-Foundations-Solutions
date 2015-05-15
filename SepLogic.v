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

Axiom finite_heap : forall h: heap, exists n: nat,
  forall n' v: nat, h n' = Some v -> n' < n.

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
| S_Lookup : forall st h x a1 n,
               h (aeval st a1) = Some n ->
               small_step (SCLookup x a1, St (st, h))
                          (SCSkip, St (st_update st x n, h))
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

Hint Constructors multiStep.

(* c is safe at state s *)
Definition safeAt (c: scom) (s: sstate) : Prop :=
(* ~ multiStep (c, St s) Abt *)

forall c' s',
  multiStep (c, St s) (c', St s')
  -> c' = SCSkip \/ exists c'', exists s'', small_step (c', St s') (c'', St s'').

Lemma small_abt: forall c c' s, small_step (c, Abt) (c', s) ->
                      s = Abt.
Proof.
  induction c; intros; inversion H; subst; eauto.
Qed.

Lemma multi_abt: forall cs cs', multiStep cs cs' ->
                           snd cs = Abt ->
                           snd cs' = Abt.
Proof.
  intros. induction H. auto.
  destruct s.  simpl in H0. inversion H0. inversion H; subst; auto.
  apply small_abt in H3. subst. auto.
Qed.

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

Lemma multistep_seq: forall cs c2 cs', multiStep cs cs' ->
                        multiStep (SCSeq (fst cs) c2, (snd cs)) (SCSeq (fst cs') c2, (snd cs')).
Proof.
  intros.
  induction H. constructor.
  econstructor; eauto.
Qed.

Lemma safeAt_seq: forall c1 c2 s h, safeAt (SCSeq c1 c2) (s, h) ->
                      safeAt c1 (s, h).
Proof.
  unfold safeAt. intros.
  assert (multiStep (SCSeq c1 c2, St (s, h)) (SCSeq c' c2, St s')).
  remember (c1, St (s, h)) as cs. remember (c', St s') as cs'.
  apply multistep_seq with (c2 := c2) in H0. subst. auto.
  apply H in H1. destruct H1. inversion H1. destruct H1 as [c'' [s'' H_s]].
  inversion H_s; subst. right. eauto. left. auto.
Qed.

Lemma union_none: forall h1 h2 x,
                    h_union h1 h2 x = None ->
                    h1 x = None /\ h2 x = None.
Proof.
  intros. unfold h_union in *. destruct (in_not_in_dec x h1).
  split; auto. destruct i. congruence.
  split; auto.
Qed.

Lemma disjoint_update: forall h1 h2 x n,
                         disjoint h1 h2 ->
                         h2 x = None ->
                         disjoint (h_update h1 x n) h2.
Proof.
  unfold disjoint, not_in_dom. intros.
  unfold h_update. destruct (eq_nat_dec x l). subst.
  auto. auto.
Qed.

Hint Resolve disjoint_update.

Lemma union_update: forall h1 h2 x n,
                      h_union (h_update h1 x n) h2 =
                      h_update (h_union h1 h2) x n.
Proof.
  intros. apply functional_extensionality. intros.
  unfold h_union, h_update.
  destruct (in_not_in_dec x0). destruct i.
  destruct (eq_nat_dec x x0). auto.
  destruct (in_not_in_dec x0 h1). reflexivity. congruence.
  unfold not_in_dom in n0. destruct (eq_nat_dec x x0). congruence.
  destruct (in_not_in_dec x0 h1). destruct i. congruence. reflexivity.
Qed.

Lemma update_disjoint: forall h1 h2 x n,
                         disjoint h1 h2 ->
                         in_dom x h1 ->
                         disjoint (h_update h1 x n) h2.
Proof.
  unfold in_dom, h_update, disjoint, not_in_dom. intros.
  destruct (eq_nat_dec x l). subst. destruct H0. destruct (H l).
  congruence. auto. auto.
Qed.

Hint Resolve update_disjoint.

Lemma locality_frame: forall c : scom, frame c.
Proof with eauto.
  unfold frame. induction c; intros; inversion H1; subst; try solve [exists h1; eauto].
  Case "Seq".
  apply safeAt_seq in H.
  eapply IHc1 in H... destruct H as [h'' [H5 [H6 H7]]].
  exists h''. eauto.
  Case "Cons".
  exists (h_update (h_update h1 l (aeval s a)) (l + 1) (aeval s a0)).
  destruct (union_none h1 h2 l H12).
  destruct (union_none h1 h2 (l+1) H13).
  repeat split. constructor... eapply disjoint_update...
  rewrite union_update. rewrite union_update. reflexivity.
  Case "Lookup".
  assert (multiStep (SCLookup i a, St (s, h1)) (SCLookup i a, St (s, h1))).
  constructor. apply H in H2. destruct H2. inversion H2.
  destruct H2 as [c'' [s'' H_s]]. inversion H_s; subst.
  exists h1. repeat split... unfold h_union in H3.
  destruct (in_not_in_dec (aeval s a) h1). rewrite H3 in H4.
  inversion H4; subst... congruence.
  Case "Mutation".
  assert (multiStep (SCMutation a a0, St (s', h1)) (SCMutation a a0, St (s', h1))).
  constructor. apply H in H2. destruct H2. inversion H2.
  destruct H2 as [c'' [s'' H_s]]. inversion H_s; subst.
  exists (h_update h1 (aeval s' a) (aeval s' a0)).
  repeat split... rewrite union_update...
  Case "Dispose".
  assert (multiStep (SCDispose a, St (s', h1)) (SCDispose a, St (s', h1))).
  constructor. apply H in H2. destruct H2. inversion H2.
  destruct H2 as [c'' [s'' H_s]]. inversion H_s; subst.
  exists (fun x => if eq_nat_dec x (aeval s' a) then None else h1 x).
  repeat split... unfold disjoint, not_in_dom. intros.
  destruct (eq_nat_dec l (aeval s' a))...
  apply functional_extensionality. intros.
  unfold h_union. destruct (in_not_in_dec x)...
  destruct i. destruct (eq_nat_dec x (aeval s' a))...
  destruct (in_not_in_dec x h1)... congruence.
  unfold not_in_dom in n. destruct (eq_nat_dec x (aeval s' a)).
  subst. destruct (H0 (aeval s' a))... destruct H8. congruence.
  destruct (in_not_in_dec x h1)... destruct i. congruence.
Qed.

Lemma small_union: forall c s h c' s' h' h1,
                     small_step (c, St (s, h)) (c', St (s', h')) ->
                     disjoint h h1 ->
                     exists c'', exists sh',
                     small_step (c, St (s, h_union h h1)) (c'', St sh').
Proof with eauto.
  induction c; intros; inversion H; subst;
  try solve [exists c'; eauto]; try solve [exists SCSkip; eauto].
  exists SCSkip. exists (st_update s i (aeval s a), h_union h' h1)...
  destruct (IHc1 s h c1' s' h' h1 H2 H0) as [c'' [sh' H_s]].
  exists (SCSeq c'' c2)...
  exists (SCSeq c (SCWhile b c))...
  Case "Cons".
  destruct (finite_heap (h_union h h1)) as [l'  H_h].
  assert (h_union h h1 l' = None). destruct (in_not_in_dec l' (h_union h h1))...
  destruct i0. apply H_h in H1. omega.
  assert (h_union h h1 (l'+1)= None). destruct (in_not_in_dec (l'+1) (h_union h h1))...
  destruct i0. apply H_h in H2. omega.
  exists SCSkip. exists (st_update s i l',
              h_update (h_update (h_union h h1) l' (aeval s a))
                       (l'+1) (aeval s a0))...
  Case "Lookup".
  exists SCSkip. exists (st_update s i n, h_union h' h1).
  constructor. unfold h_union. destruct (in_not_in_dec (aeval s a) h')...
  congruence.
  Case "Mutation".
  exists SCSkip. exists (s', h_update (h_union h h1) (aeval s' a) (aeval s' a0)).
  constructor... destruct H10. exists x... unfold h_union.
  destruct (in_not_in_dec (aeval s' a) h)... congruence.
  Case "Dispose".
  exists SCSkip. exists (s', fun x =>
                     if eq_nat_dec x (aeval s' a) then None else (h_union h h1 x)).
  constructor... destruct H8. exists x. unfold h_union.
  destruct (in_not_in_dec (aeval s' a) h)... congruence.
Qed.

Lemma safeAt_continues:
  forall c c' s s' h h',
    safeAt c (s, h) -> small_step (c, St (s, h)) (c', St (s', h')) ->
    safeAt c' (s', h').
Proof.
  intros. unfold safeAt. intros.
  assert (multiStep (c, St (s, h)) (c'0, St s'0)). econstructor; eauto.
  apply H in H2. auto.
Qed.

Lemma locality_safeMono: forall c : scom, safeMono c.
Proof with eauto.
  unfold safeMono. intros.
  unfold safeAt. intros.
  remember (c, St (s, h_union h h')) as cs.
  remember (c', St s') as cs'.
  generalize dependent c.
  generalize dependent s.
  generalize dependent h.
  induction H1; intros; inversion Heqcs; subst; inversion Heqcs'; subst;
  clear Heqcs; clear Heqcs'.
  assert (multiStep (c', St (s0, h)) (c', St (s0, h)))...
  apply H in H1. destruct H1... destruct H1 as [c'' [s'' H_s]].
  destruct s''. eapply small_union in H_s...
  assert (frame c0). apply locality_frame.
  destruct s'0. destruct s.
  destruct (H3 s0 h h' c'0 s h0)... destruct H4 as [H41 [H42 H43]].
  assert ((c', St s') = (c', St s'))...
  eapply IHmultiStep in H4...
  eapply safeAt_continues in H2... rewrite H43...
  apply multi_abt in H1... inversion H1.
Qed.

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
  split. apply locality_safeMono. apply locality_frame.
Qed.
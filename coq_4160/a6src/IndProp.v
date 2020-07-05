(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.  In this chapter, we bring yet another new tool
    into the mix: _inductive definitions_.

    _Note_: For the sake of simplicity, most of this chapter uses an
    inductive definition of "evenness" as a running example.  You may
    find this confusing, since we already have a perfectly good way of
    defining evenness as a proposition ([n] is even if it is equal to
    the result of doubling some number); if so, rest assured that we
    will see many more compelling examples of inductively defined
    propositions toward the end of this chapter and in future
    chapters. *)

(** In past chapters, we have seen two ways of stating that a number
    [n] is even: We can say

      (1) [evenb n = true], or

      (2) [exists k, n = double k].

    Yet another possibility is to say that [n] is even if we can
    establish its evenness from the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** To illustrate how this new definition of evenness works,
    let's imagine using it to show that [4] is even. By rule [ev_SS],
    it suffices to show that [2] is even. This, in turn, is again
    guaranteed by rule [ev_SS], as long as we can show that [0] is
    even. But this last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation.  (We'll
    use [ev] for the name of this property, since [even] is already
    used.)

                              ------------             (ev_0)
                                 ev 0

                                 ev n
                            ----------------          (ev_SS)
                             ev (S (S n))
*)

(** Each of the textual rules that we started with is
    reformatted here as an inference rule; the intended reading is
    that, if the _premises_ above the line all hold, then the
    _conclusion_ below the line follows.  For example, the rule
    [ev_SS] says that, if [n] satisfies [ev], then [S (S n)] also
    does.  If a rule has no premises above the line, then its
    conclusion holds unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even:

                             --------  (ev_0)
                              ev 0
                             -------- (ev_SS)
                              ev 2
                             -------- (ev_SS)
                              ev 4
*)

(** (Why call this a "tree", rather than a "stack", for example?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this shortly. *)

(* ================================================================= *)
(** ** Inductive Definition of Evenness *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** This definition is interestingly different from previous uses of
    [Inductive].  For one thing, we are defining not a [Type] (like
    [nat]) or a function yielding a [Type] (like [list]), but rather a
    function from [nat] to [Prop] -- that is, a property of numbers.
    But what is really new is that, because the [nat] argument of
    [ev] appears to the _right_ of the colon on the first line, it
    is allowed to take different values in the types of different
    constructors: [0] in the type of [ev_0] and [S (S n)] in the type
    of [ev_SS].  Accordingly, the type of each constructor must be
    specified explicitly (after a colon), and each constructor's type
    must have the form [ev n] for some natural number [n].

    In contrast, recall the definition of [list]:

    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).

   This definition introduces the [X] parameter _globally_, to the
   _left_ of the colon, forcing the result of [nil] and [cons] to be
   the same (i.e., [list X]).  Had we tried to bring [nat] to the left
   of the colon in defining [ev], we would have seen an error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]"
        as 1st argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in [Inductive list (X : Type) := ...], the [X] is a
    parameter; in [Inductive ev : nat -> Prop := ...], the unnamed
    [nat] argument is an index. *)

(** We can think of the definition of [ev] as defining a Coq
    property [ev : nat -> Prop], together with "evidence constructors"
    [ev_0 : ev 0] and [ev_SS : forall n, ev n -> ev (S (S n))]. *)

(** Such "evidence constructors" have the same status as proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    rule names to prove [ev] for particular numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  (* SOLUTION: *)
  intros n. induction n as [| n'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'. Qed.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, which amounts to reasoning about how it
    could have been built.

    Introducing [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is [ev], but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are [ev]. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must be one of two things:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [ev n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence that [ev n] _directly_. As
    a tool, we can prove our characterization of evidence for
    [ev n], using [destruct]. *)

Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** The following theorem can easily be proved using [destruct] on
    evidence. *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** However, this variation cannot easily be handled with just
    [destruct]. *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
(** Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2] because that argument [n] is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)

(** If we [remember] that term [S (S n)], the proof goes
    through.  (We'll discuss [remember] in more detail below.) *)

Theorem evSS_ev_remember : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. remember (S (S n)) as k eqn:Hk. destruct E as [|n' E'] eqn:EE.
  - (* E = ev_0 *)
    (* Now we do have an assumption, in which [k = S (S n)] has been
       rewritten as [0 = S (S n)] by [destruct]. That assumption
       gives us a contradiction. *)
    discriminate Hk.
  - (* E = ev_S n' E' *)
    (* This time [k = S (S n)] has been rewritten as [S (S n') = S (S n)]. *)
    injection Hk as Heq. rewrite <- Heq. apply E'.
Qed.

(** Alternatively, the proof is straightforward using our inversion
    lemma. *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hn Hev]]. injection Hn as Heq.
   rewrite Heq. apply Hev.
Qed.

(** Note how both proofs produce two subgoals, which correspond
    to the two ways of proving [ev].  The first subgoal is a
    contradiction that is discharged with [discriminate].  The second
    subgoal makes use of [injection] and [rewrite].  Coq provides a
    handy tactic called [inversion] that factors out that common
    pattern.

    The [inversion] tactic can detect (1) that the first case ([n =
    0]) does not apply and (2) that the [n'] that appears in the
    [ev_SS] case must be the same as [n].  It has an "[as]" variant
    similar to [destruct], allowing us to assign names rather than
    have Coq choose them. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E' Heq].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice) 

    Prove the following result using [inversion].  (For extra practice,
    you can also prove it using the inversion lemma.) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* SOLUTION: *)
  intros n E.
  inversion E as [| n' E' EQ'].
  inversion E' as [| n'' E'' EQ''].
  apply E''.  Qed.
(** [] *)

(** **** Exercise: 1 star, standard (ev5_nonsense) 

    Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  (* SOLUTION: *)
  intros E. inversion E as [| n' E' EQ'].
  inversion E' as [| n'' E'' EQ''].
  inversion E''.
  (* Contradiction, as neither constructor can possibly apply... *)  Qed.
(** [] *)

(** The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied, more generally,
    to analyze evidence for inductively defined propositions.  As
    examples, we'll use it to reprove some theorems from chapter
    [Tactics].  (Here we are being a bit lazy by omitting the [as]
    clause from [inversion], thereby asking Coq to choose names for
    the variables and hypotheses that it introduces.) *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.  Suppose the name
    [H] refers to an assumption [P] in the current context, where [P]
    has been defined by an [Inductive] declaration.  Then, for each of
    the constructors of [P], [inversion H] generates a subgoal in which
    [H] has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove [P].  Some of
    these subgoals will be self-contradictory; [inversion] throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, [inversion]
    adds all equations into the proof context that must hold of the
    arguments given to [P] (e.g., [S (S n') = n] in the proof of
    [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in chapter [Logic], we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma. *)

Lemma ev_even_firsttry : forall n,
  ev n -> even n.
Proof.
  (* WORKED IN CLASS *)

(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy would
    probably lead to a dead end, because (as we've noted before) the
    induction hypothesis will talk about n-1 (which is _not_ even!).
    Thus, it seems better to first try [inversion] on the evidence for
    [ev].  Indeed, the first case can be solved trivially. And we can
    seemingly make progress on the second case with a helper lemma. *)

  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *)
    unfold even. exists 0. simpl. reflexivity.
  - (* E = ev_SS n' E' *)
    assert (lemma_evenSS : even n' -> even (S (S n'))).
    { unfold even. intros [k Hk]. rewrite Hk. exists (S k). simpl. reflexivity. }
    apply lemma_evenSS.

    (** Unforunately, now we are stuck. To make that apparent, let's move
        [E'] back into the goal from the hypotheses. *)

    generalize dependent E'.

    (** Now it is clear we are trying to prove another instance of the
        same theorem we set out to prove.  This instance is with [n'],
        instead of [n], where [n'] is a smaller natural number than [n]. *)
Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this looks familiar, it is no coincidence: We've encountered
    similar problems in the [Induction] chapter, when trying to
    use case analysis to prove results that required induction.  And
    once again the solution is... induction! *)

(** The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove a property of [n] holds for all numbers for which [ev
    n] holds, we can use induction on [ev n]. This requires us to
    prove two things, corresponding to the two ways in which [ev n]
    could have been constructed. If it was constructed by [ev_0], then
    [n=0], and the property must hold of [0]. If it was constructed by
    [ev_SS], then the evidence of [ev n] is of the form [ev_SS n'
    E'], where [n = S (S n')] and [E'] is evidence for [ev n']. In
    this case, the inductive hypothesis says that the property we are
    trying to prove holds for [n']. *)

(** Let's try our current lemma again: *)

Lemma ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : even E' *)
    unfold even in IH.
    destruct IH as [k Hk].
    rewrite Hk. exists (S k). simpl. reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_even_iff : forall n,
  ev n <-> even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) unfold even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas, and in particular when
    formalizing the semantics of programming languages, where many
    properties of interest are defined inductively. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  (* SOLUTION: *)
  intros n m Hn Hm. induction Hn as [|n' Hn IH].
  - (* ev_0 *) simpl. apply Hm.
  - (* ev_SS *) simpl. apply ev_SS. apply IH.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ev'_ev) 

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from [Logic]) of
    applying theorems to arguments, and note that the same technique
    works with constructors of inductively defined propositions. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
 (* SOLUTION: *)
  intros n. split.
  - (* -> *)
    intros E. induction E as [| |n m En IHn Em IHm].
    + (* ev'_0 *) apply ev_0.
    + (* ev'_2 *) apply ev_SS. apply ev_0.
    + (* ev'_sum *) apply (ev_sum _ _ IHn IHm).
  - (* <- *)
    intros E. induction E as [|n E IH].
    + apply ev'_0.
    + apply (ev'_sum 2 n).
      * apply ev'_2.
      * apply IH.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, recommended (ev_ev__ev) 

    There are two pieces of evidence you could attempt to induct upon
    here. If one doesn't work, try the other. *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* SOLUTION: *)
  intros n m Enm En.
  induction En as [| n' En'].
  - (* En = ev_0 *) simpl in Enm. apply Enm.
  - (* En = ev_SS *) simpl in Enm. inversion Enm. apply IHEn'. apply H0.  Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus) 

    This exercise can be completed without induction or case analysis.
    But, you will need a clever assertion and some tedious rewriting.
    Hint:  is [(n+m) + (n+p)] even? *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* SOLUTION: *)
  intros n m p Enm Enp.
  apply (ev_ev__ev (n+n)).
  assert (n + n + (m + p) = n + m + (n + p)) as H.
  { (* Proof of assertion *)
    rewrite <- plus_assoc. rewrite <- plus_assoc. apply f_equal.
    rewrite plus_assoc. rewrite plus_assoc.
    assert (n + m = m + n) as H1.
    { (* Proof of subassertion *)
      apply plus_comm. }
    rewrite  H1.
    reflexivity. }
  rewrite H.
  apply ev_sum.
  apply Enm.
  apply Enp.
  rewrite <- double_plus. apply ev_double.
Qed.
(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** Just like properties, relations can be defined inductively.  One
    useful example is the "less than or equal to" relation on
    numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

End Playground.

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_ev : nat -> nat -> Prop :=
  | ne_1 n (H: ev (S n))     : next_ev n (S n)
  | ne_2 n (H: ev (S (S n))) : next_ev n (S (S n)).

(** **** Exercise: 2 stars, standard, optional (total_relation) 

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

(* SOLUTION: *)
Inductive total_relation : nat -> nat -> Prop :=
  | tot n m : total_relation n m.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (empty_relation) 

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

(* SOLUTION: *)
Inductive empty_relation : nat -> nat -> Prop := .
(** [] *)

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** **** Exercise: 3 stars, standard, optional (le_exercises) 

    Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* SOLUTION: *)
  intros m n o H1 H2. induction H2.
  - (* le_n *)
    apply H1.
  - (* le_S *)
    apply le_S. apply IHle. Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* SOLUTION: *)
  induction n as [| n'].
  - (* n = 0 *)
    apply le_n.
  - (* n = S n' *)
    apply le_S. apply IHn'.  Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  (* SOLUTION: *)
  intros n m H. induction H.
  - (* le_n *)
    apply le_n.
  - (* le_S *)
    apply le_S. apply IHle.  Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  (* SOLUTION: *)
  intros n m H.
  inversion H.
  - (* le_n *)
    apply le_n.
  - (* le_S *)
    apply (le_trans _ (S n) _).
    apply le_S. apply le_n.
    apply H1. Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  (* SOLUTION: *)
  intros a b. induction a as [| a'].
  - (* a = 0 *)
    apply O_le_n.
  - (* a = S a' *)
    apply n_le_m__Sn_le_Sm in IHa'. apply IHa'. Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
 (* SOLUTION: *)
  intros n1 n2 m H. induction H.
  - (* le_n *)
    split.
    + apply le_plus_l.
    + rewrite plus_comm. apply le_plus_l.
  - (* le_S *)
    destruct IHle as [Hn1m Hn2m].
    split.
    + apply le_S. apply Hn1m.
    + apply le_S. apply Hn2m. Qed.

(** Hint: the next one may be easiest to prove by induction on [n]. *)

Theorem add_le_cases : forall n m p q,
    n + m <= p + q -> n <= p \/ m <= q.
Proof.
(* SOLUTION: *)
  intros n. induction n.
  - intros m p q H.
    left.
    apply O_le_n.
  - intros m p q H.
    destruct p.
    + right.
      apply plus_le in H. destruct H as [_ H]. apply H.
    + simpl in H.
      apply Sn_le_Sm__n_le_m in H.
      apply IHn in H.
      destruct H as [ H1 | H2].
      * left. apply n_le_m__Sn_le_Sm. apply H1.
      * right. apply H2. Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* SOLUTION: *)
  unfold lt. intros. apply le_S. apply H. Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
(* SOLUTION: *)
  unfold lt. intros n1 n2 m H. split.
  - apply le_trans with (n := S (n1 + n2)).
    + simpl. rewrite <- plus_Sn_m. apply le_plus_l.
    + apply H.
  - apply le_trans with (n := S (n1 + n2)).
    + rewrite plus_comm. rewrite <- plus_Sn_m. apply le_plus_l.
    + apply H.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  (* SOLUTION: *)
  intros n.
  induction n as [| n'].
  - (* n = 0 *) intros m H.
    apply O_le_n.
  - (* n = S n' *) intros m H.
    simpl in H. destruct m as [| m'].
    + (* m = 0 *)
      discriminate.
    + (* m = S m' *)
      apply IHn' in H.
      apply n_le_m__Sn_le_Sm.
      apply H. Qed.

(** Hint: The next one may be easiest to prove by induction on [m]. *)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  (* SOLUTION: *)
  intros n m. generalize dependent n. induction m as [|m'].
  - (* m = 0 *)
    intros n H.
    inversion H. reflexivity.
  - (* m = Sm' *)
    intros n H.
    inversion H.
    + rewrite H0 in H.
      symmetry. apply leb_refl.
    + destruct n as [|n'].
      * reflexivity.
      * simpl.
        apply IHm'.
        apply Sn_le_Sm__n_le_m. apply H. Qed.

(** Hint: The next one can easily be proved without using [induction]. *)

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  (* SOLUTION: *)
  intros n m o P Q.
  apply leb_complete in P. apply leb_complete in Q.
  apply leb_correct.
  apply le_trans with m.  apply P. apply Q. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  (* SOLUTION: *)
  intros n m. split.
  - apply leb_complete.
  - apply leb_correct.
Qed.
(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, recommended (R_provability) 

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. *)

(* SOLUTION:
   - The first proposition is provable and the second is not.
     The proof term for the first is:

       (c3 _ _ _ (c2 _ _ _ c1)).

   - Dropping [c5] would not change the set of provable
     propositions.  [c4] and [c1] don't interact with [c5], since
     they're already symmetric in [m] and [n]; [c2] followed by
     [c5] is equivalent to [c3], and vice versa.

   - Dropping [c4] would not change the set of provable
     propositions. This constructor just "undoes" one application
     of [c2] and one application of [c3]. More precisely, the
     only way we can construct evidence for [R (S m) (S n) (S (S o))]
     is by applying [c2] and [c3] (in either order) to evidence for
     [R m n o], so the latter must already hold. (This can be proved
     by induction, although the proof is surprisingly tedious.) *)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact) 

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq? *)

Definition fR : nat -> nat -> nat
  (* SOLUTION: *) :=
  plus.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
(* SOLUTION: *)
  intros m n o.
  split.
  - intros H. induction H.
    + (* c1 *) reflexivity.
    + (* c2 *) simpl. rewrite IHR. reflexivity.
    + (* c3 *) rewrite <- plus_n_Sm. unfold fR in IHR. rewrite IHR. reflexivity.
    + (* c4 *) simpl in IHR. rewrite <- plus_n_Sm in IHR.
      injection IHR as Hmno. rewrite <- Hmno. reflexivity.
    + (* c5 *) rewrite plus_comm. apply IHR.
  - generalize dependent n. generalize dependent m.
    induction o as [|o'].
    + (* o = 0 *)
      intros m n H.
      destruct m as [|m'].
      * (* m = 0 *)
        simpl in H. rewrite -> H. apply c1.
      * (* m = S m' *)
        inversion H.
    + (* o = S o' *)
      intros m n H. destruct m as [|m'].
      * (* m = 0 *)
        simpl in H. rewrite -> H. apply c3. apply IHo'.
        reflexivity.
      * (* m = S m' *)
        apply c2. apply IHo'. inversion H. reflexivity.
Qed.

(** [] *)

End R.

(** **** Exercise: 2 stars, advanced (subsequence) 

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully! *)

Inductive subseq : list nat -> list nat -> Prop :=
(* SOLUTION: *)
  | sub_nil  l : subseq [] l
  | sub_take x l1 l2 (H : subseq l1 l2) : subseq (x :: l1) (x :: l2)
  | sub_skip x l1 l2 (H : subseq l1 l2) : subseq l1 (x :: l2)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  (* SOLUTION: *)
  induction l as [|x l'].
  - (* l = [] *) apply sub_nil.
  - (* l = x :: l' *) apply sub_take. apply IHl'.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  (* SOLUTION: *)
  intros l1 l2 l3 H.
  induction H.
    - (* sub_nil *) apply sub_nil.
    - (* sub_take *) simpl. apply sub_take. apply IHsubseq.
    - (* sub_skip *) simpl. apply sub_skip. apply IHsubseq.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  (* SOLUTION: *)
  intros l1 l2 l3 S12 S23. generalize dependent l1.
  induction S23 as [|x l2 l3 |x l2 l3].
   - (* sub_nil *)
    intros l1 S12. inversion S12. apply sub_nil.
   - (* sub_take *)
    intros l1 S12.  inversion S12.
        apply sub_nil.
        apply sub_take. apply IHS23. apply H1.
        apply sub_skip. apply IHS23. apply H1.
   - (* sub_skip *)
    intros l1 S12. apply sub_skip. apply IHS23. apply S12.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2) 

    Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 n l (H: R n l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(* SOLUTION:

    The first two are provable; the third is not.

    In case this question puzzled you, one good way to understand
    definitions like this is to explore their implications with
    concrete examples, e.g.

      R 0 []        by c1
      R 1 [0]       by c2 using R 0 []
      R 2 [1;0]     by c2 using R 1 [0]
      R 3 [2;1;0]   by c2 using R 2 [1;0]
      R 2 [2;1;0]   by c3 using R 3 [2;1;0]
      R 1 [2;1;0]   by c3 using R 2 [2;1;0]
      R 2 [1;2;1;0] by c2 using R 1 [2;1;0]
      R 1 [1;2;1;0] by c3 using R 2 [1;2;1;0]
      etc.

    If you do a few more of these yourself, you should see the pattern
    emerging.

    [] *)

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** The [ev] property provides a simple example for
    illustrating inductive definitions and the basic techniques for
    reasoning about them, but it is not terribly exciting -- after
    all, it is equivalent to the two non-inductive definitions of
    evenness that we had already seen, and does not seem to offer any
    concrete benefit over them.

    To give a better sense of the power of inductive definitions, we
    now show how to use them to model a classic concept in computer
    science: _regular expressions_. *)

(** Regular expressions are a simple language for describing sets of
    strings.  Their syntax is defined as follows: *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- that is, lists of elements of [T].

    (We depart slightly from standard practice in that we do not
    require the type [T] to be finite.  This results in a somewhat
    different theory of regular expressions, but the difference is not
    significant for our purposes.) *)

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        In particular, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows.  We use the notation [s =~ re] in
    place of [exp_match s re]; by "reserving" the notation before
    defining the [Inductive], we can use it in the definition! *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Lemma quiz : forall T (s:list T), ~(s =~ EmptySet).
Proof. intros T s Hc. inversion Hc. Qed.
(** Again, for readability, we can also display this definition using
    inference-rule notation. *)

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

(** Notice that these rules are not _quite_ the same as the
    informal ones that we gave at the beginning of the section.
    First, we don't need to include a rule explicitly stating that no
    string matches [EmptySet]; we just don't happen to include any
    rule that would have the effect of some string matching
    [EmptySet].  (Indeed, the syntax of inductive definitions doesn't
    even _allow_ us to give such a "negative rule.")

    Second, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the strings
    [[1]] and [[2]] directly.  Since the goal mentions [[1; 2]]
    instead of [[1] ++ [2]], Coq wouldn't be able to figure out how to
    split the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars, standard (exp_match_ex1) 

    The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  (* SOLUTION: *)
  intros T s H. inversion H. Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  (* SOLUTION: *)
  intros T s re1 re2 [H | H].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  (* SOLUTION: *)
  intros T ss re H.
  induction ss as [|s ss' IH].
  - (* ss = [] *)
    simpl. apply MStar0.
  - (* ss = s :: ss' *)
    simpl. apply MStarApp.
    + apply H. left. reflexivity.
    + apply IH.
      intros s' H'. apply H. right. apply H'.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (reg_exp_of_list_spec) 

    Prove that [reg_exp_of_list] satisfies the following
    specification: *)

Lemma reg_exp_of_list_spec1 : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 -> s1 = s2.
Proof.
  intros T s1 s2.
  generalize dependent s1.
  induction s2 as [|x s2' IH].
  - (* s2 = [] *)
    intros s1. simpl. intros H.
    inversion H. reflexivity.
  - (* s2 = x :: s2' *)
    intros s1. simpl. intros H.
    inversion H as [| | s11 re1 s12 re2 M1 M2 | | | | ].
    inversion M1 as [|x'| | | | |].
    simpl. rewrite (IH _ M2).
    reflexivity.
Qed.

Lemma reg_exp_of_list_spec2 : forall T (s : list T),
  s =~ reg_exp_of_list s.
Proof.
  intros T s.
  induction s as [|x s' IH].
  - (* s = [] *)
    simpl. apply MEmpty.
  - (* s = x :: s' *)
    simpl.
    apply (MApp [x]).
    + apply MChar.
    + apply IH.
Qed.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  (* SOLUTION: *)
  intros T s1 s2. split.
  - (* -> *)
    apply reg_exp_of_list_spec1.
  - (* <- *)
    intros H. rewrite H.
    apply reg_exp_of_list_spec2.
Qed.
(** [] *)

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)

(** For example, suppose that we wanted to prove the following
    intuitive result: If a regular expression [re] matches some string
    [s], then all elements of [s] must occur as character literals
    somewhere in [re].

    To state this theorem, we first define a function [re_chars] that
    lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** We can then phrase our theorem as follows: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.

(** Something interesting happens in the [MApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re1]), and a second one that applies when [x]
    occurs in [s2] (which matches [re2]). *)

    simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.

(** Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for [exp_match], rather than
    induction on the regular expression [re]: The latter would only
    provide an induction hypothesis for strings that match [re], which
    would not allow us to reason about the case [In x s2]. *)

    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars, standard (re_not_empty) 

    Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool
  (* SOLUTION: *) :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App re1 re2 => (re_not_empty re1) && (re_not_empty re2)
  | Union re1 re2 => (re_not_empty re1) || (re_not_empty re2)
  | Star re => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  (* SOLUTION: *)
  intros T re.
  induction re as [| |x|re1 IH1 re2 IH2
                   |re1 IH1 re2 IH2|re IH].
  - (* EmptySet *)
    simpl. split.
    + intros [s contra]. inversion contra.
    + intros H. discriminate.
  - (* EmptyStr *)
    simpl. split.
    + intros _. reflexivity.
    + exists []. apply MEmpty.
  - (* Char *)
    simpl. split.
    + intros _. reflexivity.
    + exists [x].
      apply MChar.
  - (* App *)
    simpl.
    rewrite andb_true_iff.
    split.
    + intros [s H].
      inversion H. split.
      * apply IH1. exists s1. apply H3.
      * apply IH2. exists s2. apply H4.
    + intros [H1 H2].
      apply IH1 in H1. destruct H1 as [s1 Hs1].
      apply IH2 in H2. destruct H2 as [s2 Hs2].
      exists (s1 ++ s2). apply (MApp _ _ _ _ Hs1 Hs2).
  - (* Union *)
    simpl.
    rewrite orb_true_iff.
    split.
    + intros [s H]. inversion H.
      * left. apply IH1. exists s. apply H2.
      * right. apply IH2. exists s. apply H1.
    + intros [H | H].
      * apply IH1 in H. destruct H as [s H].
        exists s. apply (MUnionL _ _ _ H).
      * apply IH2 in H. destruct H as [s H].
        exists s. apply (MUnionR _ _ _ H).
  - (* Star *)
    simpl. split.
    + intros _. reflexivity.
    + exists []. apply MStar0.
Qed.
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it will let you try to perform an induction over a term that
    isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] without an [eqn:] clause can do),
    and leave you unable to complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence!). Here is a naive first attempt: *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect from the
    definition of [exp_match]), we have lost a very important bit of
    information from [H1]: the fact that [s1] matched something of the
    form [Star re].  This means that we have to give proofs for _all_
    seven constructors of this definition, even though all but two of
    them ([MStar0] and [MStarApp]) are contradictory.  We can still
    get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros s2 H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show that

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    which is clearly impossible. *)

  - (* MChar. *) intros s2 H. simpl. (* Stuck... *)
Abort.

(** The problem is that [induction] over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct]-without-[eqn:] than like [inversion].)

    An awkward way to solve this problem is "manually generalizing"
    over the problematic expressions by adding explicit equality
    hypotheses to the lemma: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence directly,
    because the argument to the first hypothesis is sufficiently
    general, which means that we can discharge most cases by inverting
    the [re' = Star re] equality in the context.

    This idiom is so common that Coq provides a tactic to
    automatically generate such equations for us, avoiding thus the
    need for changing the statements of our theorems. *)

Abort.

(** The tactic [remember e as x] causes Coq to (1) replace all
    occurrences of the expression [e] by the variable [x], and (2) add
    an equation [x = e] to the context.  Here's how we can use it to
    show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.

  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars, standard, optional (exp_match_ex2)  *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  (* SOLUTION: *)
  intros T s re H.
  remember (Star re) as re'.
  induction H
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)  inversion Heqre'.
  - (* MChar *)   inversion Heqre'.
  - (* MApp *)    inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.
  - (* MStar0 *)
    exists []. split.
    + reflexivity.
    + intros _ [].
  - (* MStarApp *)
    inversion Heqre'. rewrite H0 in IH2.
    assert (H : Star re = Star re). { reflexivity. }
    destruct (IH2 H) as [ss [H1 H2]].
    exists (s1 :: ss). simpl.
    rewrite H1. split.
    + reflexivity.
    + intros s' [H3 | H3].
      * rewrite <- H3, <- H0. apply Hmatch1.
      * apply H2. apply H3.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced (weak_pumping) 

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].  (For the sake of simplicity in this
    exercise, we consider a slightly weaker theorem than is usually
    stated in courses on automata theory.)

    To get started, we need to define "sufficiently long."  Since we
    are working in a constructive logic, we actually need to be able
    to calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

(** You may find these lemmas about the pumping constant useful when
    proving the pumping lemma below. *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - (* Emptyset *)
    apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  inversion Hp1 as [Hp1'| p Hp1' Hp1''].
  - rewrite H in Hp1'. discriminate Hp1'.
  - rewrite H in Hp1''. discriminate Hp1''.
Qed.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

(** This auxiliary lemma might also be useful in your proof of the
    pumping lemma. *)

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

(** The (weak) pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You are to fill in the proof. Several of the lemmas about
    [le] that were in an optional exercise earlier in this chapter
    may be useful. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  (* SOLUTION: *)
  - (* MChar *)
    simpl. intros contra. inversion contra. inversion H0.
  - (* MApp *)
    simpl. intros Hlen.
    assert (H : pumping_constant re1 <= length s1 \/
                pumping_constant re2 <= length s2).
    { rewrite app_length in Hlen.
      apply add_le_cases. apply Hlen. }
    destruct H as [H | H].
    + destruct (IH1 H) as [s11 [s12 [s13 [H1 [H2 H3]]]]].
      rewrite H1.
      exists s11. exists s12. exists (s13 ++ s2).
      rewrite <- app_assoc, <- app_assoc.
      split. { reflexivity. }
      split. { apply H2. }
      intros m.
      rewrite app_assoc, app_assoc. apply MApp.
      * rewrite <- app_assoc. apply H3.
      * apply Hmatch2.
    + destruct (IH2 H) as [s21 [s22 [s23 [H1 [H2 Hnapp]]]]].
      rewrite H1.
      exists (s1 ++ s21). exists s22. exists s23.
        rewrite <- app_assoc.
        split. { reflexivity. }
        split. { apply H2. }
        intros m.
        rewrite <- app_assoc. apply MApp.
        * apply Hmatch1.
        * apply Hnapp.
  - (* MUnionL *)
    simpl. intros Hlen.
    assert (H : pumping_constant re1 <= length s1).
    { apply (plus_le _ _ _ Hlen). }
    destruct (IH H) as [s11 [s12 [s13 [H1 [H2 Hnapp]]]]].
    exists s11. exists s12. exists s13. split. { apply H1. }
    split. { apply H2. }
    intros m. apply MUnionL. apply Hnapp.
  - (* MUnionR *)
    simpl. intros Hlen.
    assert (H : pumping_constant re2 <= length s2).
    { rewrite plus_comm in Hlen. apply (plus_le _ _ _ Hlen). }
    destruct (IH H) as [s21 [s22 [s23 [H1 [H2 Hnapp]]]]].
    exists s21. exists s22. exists s23. split. { apply H1. }
    split. { apply H2. }
    intros m. apply MUnionR. apply Hnapp.
  - (* MStar0 *)
    simpl. intro Hp. inversion Hp as [|Hp0].
    apply pumping_constant_0_false in H. inversion H.
  - (* MStarApp *)
    simpl. intros Hlen.
    rewrite app_length in *.
    assert (Hs1re1 : length s1 = 0 \/ (length s1 <> 0 /\ length s1 < pumping_constant re) \/ pumping_constant re <= length s1).
    { induction s1 as [| h s1' IHs1].
      - left. reflexivity.
      - right.
        assert (Hcases : length (h :: s1') < pumping_constant re \/ pumping_constant re <= length (h :: s1')).
        { apply PeanoNat.Nat.lt_ge_cases. }
        destruct Hcases as [Hlenlt | Hlengt].
        + left.
          split.
          * unfold not. intros contra. inversion contra.
          * apply Hlenlt.
        + right. apply Hlengt.
    }
    destruct Hs1re1 as [Hs1len0 | [[Hs1len Hs1re1] | Hs1re1]].
    + assert (Hs1nil : s1 = []).
      { destruct s1. reflexivity. inversion Hs1len0. }
      subst. simpl in *. apply IH2. apply Hlen.
    + exists [], s1, s2. simpl in *.
      split. reflexivity.
      split.
      { unfold not. intros Hs1nil. subst.
        unfold not in Hs1len. apply Hs1len.
        reflexivity.
      }

      intros m. apply napp_star.
      * apply Hmatch1.
      * apply Hmatch2.
    + destruct (IH1 Hs1re1) as [s11 [s12 [s13 [H1 [H2 Hnapp]]]]].
      exists s11, s12, (s13 ++ s2).
      split.
      { subst. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
      split.
      { apply H2. }

      intros m.
      rewrite -> app_assoc.
      rewrite -> app_assoc.
      apply MStarApp.
      * rewrite <- app_assoc. apply Hnapp.
      * apply Hmatch2.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (pumping) 

    Now here is the usual version of the pumping lemma. In addition to
    requiring that [s2 <> []], it also requires that [length s1 +
    length s2 <= pumping_constant re]. *)

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  (* SOLUTION: *)
  - (* MChar *)
    simpl. intros contra. inversion contra. inversion H0.
  - (* MApp *)
    simpl. intros Hlen.
    assert (H : pumping_constant re1 <= length s1 \/
                pumping_constant re2 <= length s2).
    { rewrite app_length in Hlen.
      apply add_le_cases. apply Hlen. }
    destruct H as [H | H].
    + destruct (IH1 H) as [s11 [s12 [s13 [H1 [H2 H3]]]]].
      rewrite H1.
      exists s11. exists s12. exists (s13 ++ s2).
      rewrite <- app_assoc, <- app_assoc.
      split. { reflexivity. }
      split. { apply H2. }
      split. { destruct H3 as [Hlenp Hnapp]. apply Plus.le_plus_trans. apply Hlenp. }
      intros m.
      rewrite app_assoc, app_assoc. apply MApp.
      * rewrite <- app_assoc. apply H3.
      * apply Hmatch2.
    + (* now, either...  length s1 < pumping_constant re, or pumping_constant <= length s1 *)
      assert (Hs1re1 : length s1 < pumping_constant re1 \/ pumping_constant re1 <= length s1).
      { apply PeanoNat.Nat.lt_ge_cases. }

      destruct Hs1re1 as [Hs1re1 | Hs1re1].
      * destruct (IH2 H) as [s21 [s22 [s23 [H1 [H2 [Hlenp Hnapp]]]]]].
        rewrite H1.
        exists (s1 ++ s21). exists s22. exists s23.
        rewrite <- app_assoc.
        split. { reflexivity. }
        split. { apply H2. }
        split. 
        { rewrite app_length in *.
          rewrite <- plus_assoc. apply le_trans with (n:=length s1 + pumping_constant re2).
          + apply Plus.plus_le_compat_l. apply Hlenp.
          + apply Plus.plus_le_compat_r. apply PeanoNat.Nat.lt_le_incl. apply Hs1re1.
        }

        intros m.
        rewrite <- app_assoc. apply MApp.
        -- apply Hmatch1.
        -- apply Hnapp.

      * destruct (IH1 Hs1re1) as [s11 [s12 [s13 [H1 [H2 H3]]]]].
        rewrite H1.
        exists s11. exists s12. exists (s13 ++ s2).
        rewrite <- app_assoc, <- app_assoc.
        split. { reflexivity. }
        split. { apply H2. }
        split. { destruct H3 as [Hlenp Hnapp]. apply Plus.le_plus_trans. apply Hlenp. }

        intros m.
        rewrite app_assoc, app_assoc. apply MApp.
        -- rewrite <- app_assoc. apply H3.
        -- apply Hmatch2.
  - (* MUnionL *)
    simpl. intros Hlen.
    assert (H : pumping_constant re1 <= length s1).
    { apply (plus_le _ _ _ Hlen). }
    destruct (IH H) as [s11 [s12 [s13 [H1 [H2 [Hlenp Hnapp]]]]]].
    exists s11. exists s12. exists s13. split. { apply H1. }
    split. { apply H2. }
    split. { apply Plus.le_plus_trans. apply Hlenp. }
    intros m. apply MUnionL. apply Hnapp.
  - (* MUnionR *)
    simpl. intros Hlen.
    assert (H : pumping_constant re2 <= length s2).
    { rewrite plus_comm in Hlen. apply (plus_le _ _ _ Hlen). }
    destruct (IH H) as [s21 [s22 [s23 [H1 [H2 [Hlenp Hnapp]]]]]].
    exists s21. exists s22. exists s23. split. { apply H1. }
    split. { apply H2. }
    split. { rewrite (plus_comm (pumping_constant re1)). apply Plus.le_plus_trans. apply Hlenp. }
    intros m. apply MUnionR. apply Hnapp.
  - (* MStar0 *)
    simpl. intro Hp. inversion Hp as [|Hp0].
    apply pumping_constant_0_false in H. inversion H.
  - (* MStarApp *)
    simpl. intros Hlen.
    rewrite app_length in *.
    assert (Hs1re1 : length s1 = 0 \/ (length s1 <> 0 /\ length s1 < pumping_constant re) \/ pumping_constant re <= length s1).
    { induction s1 as [| h s1' IHs1].
      - left. reflexivity.
      - right.
        assert (Hcases : length (h :: s1') < pumping_constant re \/ pumping_constant re <= length (h :: s1')).
        { apply PeanoNat.Nat.lt_ge_cases. }
        destruct Hcases as [Hlenlt | Hlengt].
        + left.
          split.
          * unfold not. intros contra. inversion contra.
          * apply Hlenlt.
        + right. apply Hlengt.
    }
    destruct Hs1re1 as [Hs1len0 | [[Hs1len Hs1re1] | Hs1re1]].
    + assert (Hs1nil : s1 = []).
      { destruct s1. reflexivity. inversion Hs1len0. }
      subst. simpl in *. apply IH2. apply Hlen.
    + exists [], s1, s2. simpl in *.
      split. reflexivity.
      split.
      { unfold not. intros Hs1nil. subst.
        unfold not in Hs1len. apply Hs1len.
        reflexivity.
      }
      split.
      { apply PeanoNat.Nat.lt_le_incl. apply Hs1re1. }
      intros m. apply napp_star.
      * apply Hmatch1.
      * apply Hmatch2.
    + destruct (IH1 Hs1re1) as [s11 [s12 [s13 [H1 [H2 [Hlenp Hnapp]]]]]].
      exists s11, s12, (s13 ++ s2).
      split.
      { subst. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
      split.
      { apply H2. }
      split.
      { apply Hlenp. }

      intros m.
      rewrite -> app_assoc.
      rewrite -> app_assoc.
      apply MStarApp.
      * rewrite <- app_assoc. apply Hnapp.
      * apply Hmatch2.
Qed.

End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we often need to
    relate boolean computations to statements in [Prop].  But
    performing this conversion as we did it there can result in
    tedious proof scripts.  Consider the proof of the following
    theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [eqb_eq] lemma to the equation generated by
    destructing [n =? m], to convert the assumption [n =? m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this by defining an inductive proposition that
    yields a better case-analysis principle for [n =? m].
    Instead of generating an equation such as [(n =? m) = true],
    which is generally not directly useful, this principle gives us
    right away the assumption we really need: [n = m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  Intuitively, it states that the property
    [P] is _reflected_ in (i.e., equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].  To see this, notice
    that, by definition, the only way we can produce evidence for
    [reflect P true] is by showing [P] and then using the [ReflectT]
    constructor.  If we invert this statement, this means that it
    should be possible to extract evidence for [P] from a proof of
    [reflect P true].  Similarly, the only way to show [reflect P
    false] is by combining evidence for [~ P] with the [ReflectF]
    constructor.

    It is easy to formalize this intuition and show that the
    statements [P <-> b = true] and [reflect P b] are indeed
    equivalent.  First, the left-to-right implication: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** Now you prove the right-to-left implication: *)

(** **** Exercise: 2 stars, standard, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  (* SOLUTION: *)
  intros P b H.
  destruct H as [H | H].
  - split.
    + intros _. reflexivity.
    + intros _. apply H.
  - split.
    + intros contra. exfalso. apply H. apply contra.
    + intros contra. discriminate. Qed.
(** [] *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second). *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** A smoother proof of [filter_not_empty_In] now goes as follows.
    Notice how the calls to [destruct] and [rewrite] are combined into a
    single call to [destruct]. *)

(** (To see this clearly, look at the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, standard, recommended (eqbP_practice) 

    Use [eqbP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  (* SOLUTION: *)
  intros n l Hcount. induction l as [| m l' IHl'].
  - intros contra. inversion contra.
  - simpl in Hcount. destruct (eqbP n m) as [H | H].
    + discriminate Hcount.
    + apply IHl' in Hcount. intros contra. inversion contra.
      * symmetry in H0. apply H in H0. apply H0.
      * apply Hcount in H0. apply H0.
Qed.
(** [] *)

(** This small example shows how reflection gives us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters and in _Programming
    Language Foundations_.

    The use of the [reflect] property has been popularized by
    _SSReflect_, a Coq library that has been used to formalize
    important results in mathematics, including as the 4-color theorem
    and the Feit-Thompson theorem.  The name SSReflect stands for
    _small-scale reflection_, i.e., the pervasive use of reflection to
    simplify small proof steps with boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, recommended (nostutter_defn) 

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] repeats the element [1] but does not
    stutter.)  The property "[nostutter mylist]" means that [mylist]
    does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
 (* SOLUTION: *)
 | nostutter0: nostutter nil
 | nostutter1 n : nostutter (n::nil)
 | nostutter2 a b r (Hneq : a<>b) (H : nostutter(b::r)) : nostutter (a::b::r)
 .
(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
(* SOLUTION: *)
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.

Example test_nostutter_2:  nostutter (@nil nat).
(* SOLUTION: *)
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.

Example test_nostutter_3:  nostutter [5].
(* SOLUTION: *)
  Proof. repeat constructor; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* SOLUTION: *)
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) 

    Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)

(* SOLUTION: *)
Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | merge_empty :
      merge [] [] []
  | merge_left : forall l1 l2 l3 x,
      merge l1 l2 l3 ->
      merge (x::l1) l2 (x::l3)
  | merge_right : forall l1 l2 l3 x,
      merge l1 l2 l3 ->
      merge l1 (x::l2) (x::l3).

Theorem filter_good : forall (X : Type),
                      forall (test : X->bool),
                      forall (l1 l2 l3 : list X),
  forallb test l1 = true ->
  forallb (fun x => negb (test x)) l2 = true ->
  merge l1 l2 l3 ->
  filter test l3 = l1.
Proof.
  intros X test l1 l2 l3 HT HF HM.
  induction HM.
  - (* merge_empty *) reflexivity.
  - (* merge_left *) unfold filter.
    destruct (test x) eqn: Heqtestx.
    + (* test x = true *) unfold filter in IHHM. rewrite -> IHHM. reflexivity.
      unfold forallb in HT. rewrite -> Heqtestx in HT. apply HT. apply HF.
    + (* test x = false *) unfold forallb in HT. rewrite -> Heqtestx in HT.
      discriminate HT.
  - (* merge_right *) unfold filter.
    destruct (test x) eqn: Heqtestx.
    + (* test x = true *) unfold forallb in HF. rewrite -> Heqtestx in HF.
      discriminate HF.
    + (* test x = false *)
      unfold filter in IHHM. rewrite -> IHHM. reflexivity.
      apply HT. unfold forallb in HF. rewrite -> Heqtestx in HF. apply HF.
Qed.

(* An alternative solution: *)

Lemma negb_true : forall b, negb b = true -> b = false.
Proof.
  intros b eq. destruct b.
  - (* b = true *)
    discriminate eq.
  - (* b = false *)
    reflexivity. Qed.

Theorem filter_spec : forall (X:Type) (test:X->bool) (l l1 l2:list X),
 merge l1 l2 l ->
 forallb test l1 = true ->
 forallb (fun x => negb (test x)) l2 = true ->
 l1 = filter test l.
Proof.
 intros X test l1 l2 l3 HM. induction HM.
 - (* merge_empty *) intros HT HF. simpl. reflexivity.
 - (* merge_left *) intros HT HF. simpl. simpl in HT.
   apply andb_true_iff in HT.  destruct HT as [HX HL1].
   rewrite -> HX. apply f_equal.  apply IHHM. apply HL1. apply HF.
 - (* merge_right *) intros HT HF. simpl. simpl in HF.
   apply andb_true_iff in HF. destruct HF as [HX HL2].
   apply negb_true in HX. rewrite -> HX. apply IHHM. apply HT. apply HL2.
Qed.

(* A nicer alternative solution: *)

Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 HM. induction HM as [|l1'|l2']; intros Hl1 Hl2.
  - (* merge_empty *) reflexivity.
  - (* merge_left *) simpl. destruct Hl1 as [HX Hl1']. rewrite -> HX.
    rewrite -> (IHHM Hl1' Hl2). reflexivity.
  - (* merge right *) simpl. destruct Hl2 as [HX Hl2']. rewrite -> HX.
    apply (IHHM Hl1 Hl2').
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_filter_challenge : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) 

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

(* SOLUTION: *)
Module Sol.
(** We reproduce the definition of subseq here, in a module
    so it doesn't conflict. *)

Inductive subseq {X:Type} : list X -> list X -> Prop :=
  | sub_nil  : forall l, subseq [] l
  | sub_take : forall x l1 l2, subseq l1 l2 -> subseq (x :: l1) (x :: l2)
  | sub_skip : forall x l1 l2, subseq l1 l2 -> subseq l1 (x :: l2)
.

(** A few lemmas about subseq. *)
Lemma subseq_drop_l : forall (X:Type) (x:X) (l1 l2 : list X),
  subseq (x :: l1) l2 -> subseq l1 l2.
Proof.
  intros X x l1 l2 Hsub.
  induction l2 as [|x' l2'].
  - (* l2 = [] *) inversion Hsub.
  - (* l2 = x' :: l2' *)
    inversion Hsub.
    + (* sub_take *) apply sub_skip. apply H0.
    + (* sub_skip *) apply sub_skip. apply IHl2'. apply H1.
Qed.

Lemma subseq_drop : forall (X:Type) (x:X) (l1 l2 : list X),
  subseq (x :: l1) (x :: l2) -> subseq l1 l2.
Proof.
  intros X x l1 l2 Hsub.
  inversion Hsub.
    apply H0.
    apply (subseq_drop_l _ x). apply H1.
Qed.

(** Now for some silly lemmas about [<=], which we need since we
    redefined [<=] ourselves. Of course, these are all in the Coq
    standard library. *)

Lemma le_0_n : forall n, 0 <= n.
Proof.
  induction n as [|n'].
    apply le_n.
    apply le_S. apply IHn'.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. induction H2.
    apply H1.
    apply le_S. apply IHle.
Qed.

Lemma le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply (le_trans _ (S n)).
    apply le_S. apply le_n.
    apply H.
Qed.

Lemma le_S_n : forall n m, S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - (* m = n *) apply le_n.
  - (* S n <= m *) apply le_Sn_le. apply H1.
Qed.

Lemma le_n_S : forall n m, n <= m -> S n <= S m.
Proof.
  intros n m H. induction H.
    apply le_n.
    apply le_S. apply IHle.
Qed.

Lemma Sn_le_n : forall n, ~ (S n <= n).
Proof.
  unfold not. induction n as [|n'].
  - (* n = 0 *) intros contra. inversion contra.
  - (* n = S n' *) intros H. apply IHn'.
  apply le_S_n. apply H.
Qed.

(** A list is _maximal_ with property [P] if it has the property, and
    every other list with the property is at most as long as it is. *)

Definition maximal {X:Type} (lmax : list X) (P : list X -> Prop) :=
  P lmax /\ forall l', P l' -> length l' <= length lmax.

(** A "good subsequence" for a given list [l] and a [test] is a
    subsequence of [l] all of whose members evaluate to [true] under
    the [test]. *)

Definition good_subseq {X:Type} (test : X -> bool) (l lsub : list X) :=
  subseq lsub l /\ forallb test lsub = true.

(** Good subsequences can be extended with good elements. *)

Lemma good_subseq_extend : forall (X:Type) (test : X -> bool)
                                  (l lsub : list X) (x : X),
  good_subseq test l lsub ->
  test x = true ->
  good_subseq test (x::l) (x::lsub).
Proof.
  intros X test l lsub x [Hsub Hall] Hx. split.
  - (* subseq *) apply sub_take. apply Hsub.
  - (* all *) simpl. rewrite Hx. apply Hall.
Qed.

(** If [lmax] is a maximal good subsequence of [x :: l] and [x] is not good,
    then [lmax] is also a maximal good subsequence of [l]. *)
Lemma maximal_strengthening : forall (X:Type) (x:X)
                                     (lmax l : list X)
                                     (test : X -> bool),
  maximal lmax (good_subseq test (x::l)) ->
  test x = false ->
  maximal lmax (good_subseq test l).
Proof.
  intros X x lmax l test [[Hsub Hall] Hlen] Hx.
  split. split.
  - (* subseq *)
    inversion Hsub.
    + (* sub_nil *) apply sub_nil.
    + (* sub_take *) rewrite H in H0.
      rewrite <- H0 in Hall. simpl in Hall. rewrite Hx in Hall. discriminate Hall.
    + (* sub_skip *) apply H1.
  - (* all *) apply Hall.
  - (* len *) intros l' [Hsub' Hall']. apply Hlen. split.
    + (* subseq *) apply sub_skip. apply Hsub'.
    + (* all *) apply Hall'.
Qed.

(** Some easy lemmas about filter: its result is a good subsequence of
    the original list. *)

Lemma filter_subseq : forall (X:Type) (l : list X) (test : X -> bool),
  subseq (filter test l) l.
Proof.
  intros X l test. induction l as [|x l'].
  - (* l = [] *) apply sub_nil.
  - (* l = x :: l' *) simpl. destruct (test x) eqn:E.
    + (* test x = true *) apply sub_take. apply IHl'.
    + (* test x = false *) apply sub_skip. apply IHl'.
Qed.

Lemma filter_all : forall (X:Type) (l : list X) (test : X -> bool),
  forallb test (filter test l) = true.
Proof.
  intros X l test. induction l as [|x l'].
  - (* l = [] *) reflexivity.
  - (* l = x :: l' *) simpl.
    destruct (test x) eqn: Heqtx.
    + (* test x = true *) simpl. rewrite -> Heqtx. apply IHl'.
    + (* test x = false *) apply IHl'.
Qed.

(** And now for the main theorem: [lsub] is a maximal good subsequence
    of [l] if and only if [filter test l = lsub]. *)

Theorem filter_spec2 : forall (X:Type) (l lsub:list X) (test : X -> bool),
  maximal lsub (good_subseq test l) <-> filter test l = lsub.
Proof.
  split.
  - (* -> *)
    generalize dependent lsub.
    induction l as [|x l'].
    + (* l = [] *)
      (* lsub = [] since lsub is a subseq of l. *)
      intros lsub [[Hsub _] _].
      inversion Hsub. reflexivity.
    + (* l = x :: l' *)
      intros lsub H. simpl.
      destruct (test x) eqn: Heqtx.
      * (* test x = true *)
        destruct H as [[Hsub Hall] Hlen].
        (* in this case, lsub must begin with x, since otherwise it
           wouldn't be maximal. *)
        destruct lsub as [|x' lsub'].
        { (* lsub = [] (impossible: contradicts maximality of lsub) *)
          assert (length [x] <= length ([] : list X)) as contra.
          { apply Hlen. split.
            - apply sub_take. apply sub_nil.
            - simpl. rewrite -> Heqtx. reflexivity. }
          inversion contra. }
        { (* lsub = x' :: lsub' *)
          assert (x = x'). (* because of maximality again *)
          { (* proof of assertion *)
            inversion Hsub.
            - (* sub_take *) reflexivity.
            - (* sub_skip *) (* contradiction, since x :: x' :: lsub'
                                would be longer *)
              assert (length (x :: x' :: lsub') <= length (x' :: lsub')).
              { (* proof of assertion *)
                apply Hlen. split.
                - apply sub_take. apply H1.
                - simpl. rewrite -> Heqtx. simpl. simpl in Hall.
                  apply Hall. }
              simpl in H3. apply Sn_le_n in H3. destruct H3. }
          rewrite H.
          rewrite -> (IHl' lsub'). reflexivity.
          split. split. rewrite H in Hsub. apply subseq_drop with x'. apply Hsub.
            simpl in Hall. apply andb_true_elim2 in Hall. apply Hall.
            intros l0 Hgood0. rewrite <- H in Hlen. simpl in Hlen.
            apply le_S_n.
            apply (Hlen (x :: l0)). apply good_subseq_extend. apply Hgood0.
            symmetry. rewrite  Heqtx. reflexivity. }
      * (* test x = false *)
        apply IHl'.
        apply (maximal_strengthening _ x). apply H.
        symmetry. rewrite Heqtx. reflexivity.
  - (* <- *) intros Hfilter.
    split. split.
    + (* subseq *) rewrite <- Hfilter. apply filter_subseq.
    + (* all *) rewrite <- Hfilter. apply filter_all.
    + (* len *) generalize dependent lsub. induction l as [|x l2].
      * (* l = [] *) intros lsub _ l' [Hsub _]. inversion Hsub. apply le_0_n.
      * (* l = x :: l2 *) intros lsub Hfilter l' [Hsub Hall].
        simpl in Hfilter.
        destruct (test x) eqn: Heqtx.
        { (* test x = true *)
          rewrite <- Hfilter. inversion Hsub.
          - (* sub_nil *) apply le_0_n.
          - (* sub_take *) simpl. apply le_n_S.
            apply IHl2. reflexivity. split. apply H1. rewrite <- H0 in Hall.
            simpl in Hall. apply andb_true_elim2 in Hall. apply Hall.
          - (* sub_skip *) simpl. apply le_S.
            apply IHl2. reflexivity. split. apply H1. apply Hall. }
        { (* test x = false *)
          apply IHl2. apply Hfilter. split.
          inversion Hsub. apply sub_nil. rewrite <- H0 in Hall. rewrite H in Hall.
            simpl in Hall. rewrite -> Heqtx in Hall. discriminate Hall.
            apply H1. apply Hall. }
Qed.
End Sol.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (palindromes) 

    A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

(* SOLUTION: *)
Inductive pal {X:Type} : list X -> Prop :=
  | pal_nil : pal []
  | pal_one : forall x, pal [x]
  | pal_consnoc : forall x l, pal l -> pal (x::(l++[x])).

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  induction l as [| n' l'].
  - (* l = nil *)
    simpl. apply pal_nil.
  - (* l = n' :: l' *)
    simpl. rewrite app_assoc. apply pal_consnoc. apply IHl'.  Qed.

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  intros X l P. induction P.
  - (* P = pal_nil *) reflexivity.
  - (* P = pal_one *) reflexivity.
  - (* P = pal_consnoc *)
    simpl. rewrite rev_app_distr. rewrite <- IHP.
    simpl. reflexivity.  Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_pal_pal_app_rev_pal_rev : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse) 

    Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

(* SOLUTION:

    Proving the converse theorem is much harder, because a standard
    induction over the list [l] doesn't work.  The trick to the
    following proof, due to Nathan Collins, is to induct over _half
    the length_ of [l].  We make heavy use of destruct and inversion
    to clear away the impossible cases. *)

Fixpoint div2 n := match n with
  | O => O
  | S O => O
  | S (S n') => S (div2 n')
end.

Lemma rev_pal': forall {X: Type} (n:nat) (l:list X ),
  div2 (length l) = n -> l = rev l -> pal l.
Proof.
  intros X n.
  induction n as [| n'].
    - (* n = O *)
     (* (length l) div 2 = 0 || l has length 0 or 1 *)
    intros l Hlen Hrev.
      destruct l as [| x l'].
        (* l = [] *)
        apply pal_nil.
        destruct l' as [| x' l''].
          (* l = [x] *)
          apply pal_one.
          (* impossible : l has length > 1 *)
          discriminate Hlen.
    - (* n = S n' *)
    (* (length l) div 2 >= 1  || l has length at least 2 *)
    intros l Hlen Hrev.
      destruct l as [| x l'].
        + (* l = [] *)
        (* impossible : l has length 0 *)
        discriminate Hlen.
        + (* l = x :: l' *)
          simpl in Hrev.
          destruct (rev l') as [| x' l''] eqn: Heqrevl'.
            * (* rev l' = [] *)
            (* impossible : l has length 1 *)
             inversion Hrev. rewrite H0 in Hlen. discriminate Hlen.
            * (* rev l' = x'::l'' *)
              inversion Hrev.
              (* l = x' :: l'' ++ [x'] *)
              apply pal_consnoc.
              apply IHn'.
              rewrite H1 in Hlen. simpl in Hlen.
              replace (length (l'' ++ [x'])) with (S (length l'')) in Hlen.
              { injection Hlen as H2. apply H2. }
              symmetry. rewrite app_length. rewrite plus_comm. reflexivity.
              rewrite H1 in Heqrevl'. rewrite rev_app_distr in Heqrevl'.
              injection Heqrevl'. intro H2. rewrite H2. reflexivity.
Qed.

(* And here's another solution due (modulo some fixes by BCP/AAA to
   replace snoc with app) to Michael Schulman. It uses a few tactics
   that we haven't seen yet. *)

Theorem eqrev_pal_gen (X : Type) : forall (l:list X) (p t:list X),
   l = p ++ t -> p = rev p -> pal p.
Proof.
 induction l as [| x l'].
 - (* l = nil *)
   destruct p.
   + (* p = nil *)
     destruct t as [| x t'].
        * (* t = nil *)
          intros; constructor.
        * (* t = cons *)
          intros H; inversion H.
   + (* p = cons *)
     intros t H.
     inversion H.
 - (* l = cons *)
   destruct p as [| y p'].
   + (* p = nil *)
     intros. constructor.
   + (* p = cons *)
     intros t H K.
     inversion H.
     simpl in K.
     destruct (rev p') as [| z p''] eqn:Heqrevp'.
     * (* rev p' = nil *)
       destruct p' as [| w q].
       { (* p' = nil *) constructor. }
       { (* p' = cons *)
         assert (L : [] = w :: q).
         { rewrite <- rev_involutive. rewrite  Heqrevp'. reflexivity. }
         inversion L. }
     * (* rev p' = cons *)
       assert (M : rev (rev p') = (rev p'') ++ [z]).
       { rewrite Heqrevp'. reflexivity. }
       rewrite rev_involutive in M.
       rewrite M.
       inversion K.
       (* Now we finally get to do *)
       constructor.
       apply (IHl' _ (z :: t)).
       { (* l' = rev p'' ++ z :: t *)
         rewrite H2. rewrite M. rewrite <- app_assoc. reflexivity. }
       { (* rev p'' = rev (rev p'') *)
         rewrite H4 in Heqrevp'. rewrite rev_app_distr in Heqrevp'.
         inversion Heqrevp'.
         rewrite rev_involutive.
         symmetry. apply H5. } Qed.

Theorem eqrev_pal (X : Type) (l:list X) : (l = rev l) -> pal l.
Proof.
  intros H.
  apply (eqrev_pal_gen _ l l []).
  rewrite app_nil_r. reflexivity.
  apply H.
Qed.

(* A final possibility is adding a natural number n and a hypothesis
   "length l <= n" and inducting on n.  The following solution by
   Mihir Mehta follows this strategy... *)

Lemma palindrome_converse_lemma_1:
 forall {X: Type} (l: list X), length (rev l) = length l.
Proof. {
   intros X. induction l.
   { reflexivity. }
   { simpl. rewrite -> app_length. rewrite -> IHl. simpl.
     rewrite -> plus_comm. reflexivity. }
 } Qed.

Lemma palindrome_converse_lemma_2:
 forall {X: Type} (n: nat) (l: list X), (length l <= n) -> l = rev l -> pal l.
Proof. {
   intros X. induction n as [| n'].
   { (* n = 0 *)
     intros [| x l'] H1 H2.
     { (* l = [] *) apply pal_nil. }
     { (* l = x :: l' *) inversion H1. }
   }
   { (* n = S n'*)
     intros [| x l'] H3 H4.
     { (* l = [] *) apply pal_nil. }
     { (* l = x :: l' *)
       simpl in H4.
       destruct (rev l') as [| x' l''] eqn:H5.
       { (* rev l = [] *)
         rewrite <- (rev_involutive X l'). rewrite -> H5. simpl.
         apply pal_one. }
       { (* rev l = x' :: l'' *)
         inversion H4 as [[H6 H7]]. apply pal_consnoc. apply (IHn' l'').
         { (* proving: length l'' <= n' *)
           rewrite -> H7 in H3. simpl in H3.
           rewrite -> app_length in H3. simpl in H3.
           rewrite -> plus_comm in H3. simpl in H3.
           apply Sn_le_Sm__n_le_m,  Sn_le_Sm__n_le_m.
           apply le_S. apply H3.
         }
         { (* proving l'' = rev l'' *)
           rewrite -> H7 in H5. rewrite -> rev_app_distr in H5. simpl in H5.
           inversion H5 as [H8]. rewrite -> H8, -> H8. reflexivity.
         }
       }
     }
   }
 } Qed.

Theorem palindrome_converse: forall {X: Type} (l: list X), l = rev l -> pal l.
Proof. {
   intros X l. apply (palindrome_converse_lemma_2 (length l)), le_n.
 } Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup) 

    Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

(* SOLUTION: *)
Definition disjoint {X:Type} (l1 l2: list X) :=
  forall (x:X), In x l1 -> ~ In x l2.

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

(* SOLUTION: *)
Inductive NoDup {X:Type} : list X -> Prop :=
  | NoDup_nil : NoDup nil
  | NoDup_cons : forall a l,
              ~ In a l ->
              NoDup l ->
              NoDup (a::l).

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* SOLUTION: *)
(* Here are some possible answers: *)

Lemma NoDup_append : forall (X:Type) (l1 l2: list X),
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  intros X l1. induction l1 as [| x l1'].
  - (* l1 = nil *)
    intros l2 NR1 NR2 D. simpl. apply NR2.
  - (* l1 = x:l1' *)
    intros l2 NR1 NR2 D. simpl.
    apply NoDup_cons.
    + intros contra. apply In_app_iff in contra. destruct contra.
      * inversion NR1 as [| ? ? NA NRl1']. apply NA. apply H.
      * unfold disjoint in D.  apply (D x).
        { left. reflexivity. }
        apply H.
    + apply IHl1'.
      * inversion NR1 as [| ? ? NA NRl1']. apply NRl1'.
      * apply NR2.
      * unfold disjoint. intros x0 AI. apply D. right. apply AI.
Qed.

Lemma NoDup_disjoint : forall (X:Type) (l1 l2: list X),
  NoDup (l1++l2) -> disjoint l1 l2.
Proof.
  unfold disjoint.
  induction l1 as [|x l1'].
  - intros l2 NR x AI. inversion AI.
  - intros l2 NR x0 AI. simpl in NR. inversion NR. inversion AI.
    + intros contra. apply H1.
      apply In_app_iff. right. rewrite H3. apply contra.
    + apply IHl1'.
      * apply H2.
      * apply H3.
Qed.

(* We can also show the following results about [NoDup] and [++]
   by themselves *)
Lemma NoDup_left : forall (X:Type) (l1 l2: list X),
  NoDup (l1++l2) -> NoDup l1.
Proof.
  induction l1 as [|x l1'].
  - intros l2 NR. apply NoDup_nil.
  - intros l2 NR. inversion NR. apply NoDup_cons.
    + intro contra. apply H1. apply In_app_iff. left. apply contra.
    + apply (IHl1' l2). apply H2.
Qed.

Lemma NoDup_right: forall (X:Type) (l1 l2: list X),
  NoDup (l1++l2) -> NoDup l2.
Proof.
  induction l1 as [|x l1'].
  - intros l2 NR. simpl in NR. apply NR.
  - intros l2 NR. inversion NR. apply IHl1'. apply H2.
Qed.

(* This theorem combines the various lemmas to give a complete
   characterization *)
Theorem NoDup_disjoint_app : forall {X:Type} (l1 l2: list X),
  NoDup (l1++l2) <->
  (NoDup l1 /\ NoDup l2 /\ disjoint l1 l2).
Proof.
  intros X l1 l2.
  split.
  - (* -> *)
    intro NR. split.
    + apply (NoDup_left _ _ l2). apply NR.
    + split.
      * apply (NoDup_right _ l1). apply NR.
      * apply NoDup_disjoint. apply NR.
  - (* <- *)
    intros [NR1 [NR2 DISJ]].
    apply NoDup_append.
    + apply NR1.
    + apply NR2.
    + apply DISJ.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle) 

    The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  (* SOLUTION: *)
  induction l as [|x' l' IHl'].
  - (* l = nil *)
    intros [].
  - (* l = x' :: l' *)
    simpl. intros [AI | AI].
    + (* x' = x *)
      exists []. exists l'. rewrite AI. reflexivity.
    + (* In x l' *)
      destruct (IHl' AI) as [l1' [l2' EQ]].
      exists (x'::l1'). exists l2'. rewrite -> EQ. reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* SOLUTION: *)
  | rep_here : forall a l, In a l -> repeats (a::l)
  | rep_later : forall a l, repeats l -> repeats (a::l)
.

(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
  (* SOLUTION: *)
    intros l2 EM INC NR.  simpl in NR. inversion NR.
    intros l2 EM INC NR.
    assert (In x l1' \/ ~ In x l1') as EO.  apply EM.
    destruct EO.
    - (* In x l1' *)
      left. assumption.
    - (* ~ In x l1' *)
      right.
        assert (exists l2a l2b, l2 = l2a ++ (x::l2b)) as EI.
        { (* proof of assertion *)
           apply in_split.
           apply INC. left. reflexivity. }
        destruct EI as [l2a [l2b EQ]].
        apply (IHl1' (l2a ++ l2b) EM).
        + intros x0 AI.
          assert (x0 <> x).
          { intros Heq. apply H. rewrite <- Heq. apply AI. }
          assert (In x0 l2).
          { apply INC. simpl. right. apply AI. }
          rewrite EQ in H1. apply In_app_iff in H1. apply In_app_iff.
          simpl in H1. destruct H1 as [H1 | [H1 | H1]].
          * left. apply H1.
          * exfalso. apply H0. rewrite H1. reflexivity.
          * right. apply H1.
        + assert (length l2 = S(length (l2a ++ l2b))).
          { (* proof of assertion *)
            rewrite EQ.
            rewrite app_length. rewrite app_length. rewrite plus_comm.
            simpl. rewrite plus_comm. reflexivity. }
          rewrite H0 in NR. simpl in NR.
          apply Sn_le_Sm__n_le_m.  apply NR.  Qed.

(** [] *)

(** Here's a clever alternative proof, based heavily on one by Daniel
    Schepler (<dschepler@gmail.com> Coq club mailing list on Wed, 02 Oct
    2013 02:02:12 -0700), that doesn't use decidability of [In], and hence
    doesn't need [excluded_middle]. *)

(** First, some more auxiliary lemmas, some of which are a bit ad hoc. *)

Lemma in_repeats: forall {X:Type} (l1 l2:list X) (x:X),
    In x (l1++l2) ->
    repeats (l1++x::l2).
Proof.
  intros X l1. induction l1 as [|y l1' IHl1'].
  - (* l1 = [] *)
    intros l2 x AI. simpl in AI. simpl. apply rep_here. apply AI.
  - (* l1 = y::l1' *)
    intros l2 x AI. simpl in AI. simpl. destruct AI as [AI | AI].
    + apply rep_here. apply In_app_iff. right. left.
      rewrite AI. reflexivity.
    + apply rep_later. apply IHl1'. apply AI.
Qed.

Lemma rep_insert: forall {X:Type} (l1 l2:list X) (x: X),
  repeats (l1 ++ l2) -> repeats (l1 ++ x::l2).
Proof.
  intros X l1. induction l1 as [| y l1' IHl1'].
  - (* l1 = [] *)
   intros l2 x H. simpl. simpl in H. apply rep_later.  apply H.
  - (* l1 = y::l1' *)
   intros l2 x H. simpl. simpl in H. inversion H.
   + (* rep_here *)
     apply rep_here. apply In_app_iff. apply In_app_iff in H1.
     destruct H1 as [H1 | H1].
     * left. apply H1.
     * right. right. apply H1.
   + (* rep_later *)
     apply rep_later. apply IHl1'. apply H1.
Qed.

Lemma repeats_app_comm : forall {X:Type} (l1 l2:list X),
   repeats (l1++l2) -> repeats(l2++l1).
Proof.
 intros X l1. induction l1 as [|x l1'].
 - (* l1 = [] *)
  intros l2 H.  rewrite app_nil_r. simpl in H. apply H.
 - (* l1 = x::l1' *)
  intros l2 H. simpl in H. inversion H.
  + (* rep_here *)
    apply in_repeats. apply In_app_iff.
    apply In_app_iff in H1.
    destruct H1 as [H1 | H1].
    * right. apply H1.
    * left. apply H1.
  + (* rep_later *)
    apply IHl1' in H1. apply rep_insert. apply H1.
Qed.

(** Now the main lemma: *)

Lemma pigeonhole_principle_aux: forall {X:Type} (l1 l2 ls: list X),
 (forall x:X, In x l1 -> In x (ls++l2)) ->
 length l2 < length l1 -> repeats (ls++l1).
Proof.
  intros X l1. induction l1 as [|x l1' IHl1'].
  - (* l1 = [] *)
   intros l2 ls AI LT. inversion LT.
  - (* l1 = x::l1' *)
   intros l2 ls AI LT.
   assert (In x (ls++l2)).
   { (* Proof of assertion *)
     apply AI. left. reflexivity. }
   assert (In x ls \/ In x l2).
   { (* Proof of assertion *)
     apply In_app_iff. apply H. }
   destruct H0.
   + (* In x ls *)
     apply repeats_app_comm. simpl. apply rep_here.
     apply In_app_iff. right. exact H0.
   + (* In x l2 *)
     apply in_split in H0.
     destruct H0 as [l2a [l2b P]]. rewrite P in *.
     assert (repeats ((x::ls) ++ l1')).
     * (* Proof of assertion *)
       apply (IHl1' (l2a++l2b) (x::ls)).
       { (* re-establish inclusion relation *)
         intros x0 AI'.
         assert (In x0 (ls ++ l2a ++ x::l2b)).
         { (* Proof of assertion *)
            apply AI. right. apply AI'. }
         apply In_app_iff in H0. inversion H0.
           apply In_app_iff.  left. right. apply H1.
           apply In_app_iff in H1. inversion H1.
             apply In_app_iff. right.
                apply In_app_iff. left. apply H2.
             inversion H2.
               simpl. left. apply H3.
               apply In_app_iff. right.
                 apply In_app_iff. right. apply H3. }
       rewrite app_length in LT.  rewrite app_length.
       simpl in LT. rewrite <- plus_n_Sm in LT.
       unfold lt. unfold lt in LT. apply le_S_n. apply LT.
     * simpl in H0. apply repeats_app_comm. simpl. inversion H0.
       { apply rep_here. apply In_app_iff.
         apply In_app_iff in H2. inversion H2.
         - right. apply H4.
         - left. apply H4. }
       apply rep_later. apply repeats_app_comm. apply H2.
Qed.

Theorem stronger_pigeonhole_principle: forall {X:Type} (l1 l2 : list X),
   (forall x : X, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
  intros X l1 l2 AI LT.
  assert (H: l1 = nil ++ l1). { reflexivity. }
  rewrite H. apply (pigeonhole_principle_aux l1 l2 nil).
  simpl. apply AI. apply LT.
Qed.

(** One key to how this proof works is that at the inductive step,
when we re-establish the inclusion relation, the contents on the list
on the right-hand side of the inclusion have not changed at all---they
are merely re-arranged, so validity of the inclusion is trivial
(modulo some messy book-keeping). Compare this to the equivalent step
in the original proof, where we remove [x] from the list on the right-hand
side of the inclusion; this is only valid when we know that [x] is
not in the left-hand list [l1'] either---exactly the knowledge that we
get from decidability of [In], and cannnot get any other way. *)

(* ------------------------ *)

(** Finally, here is a much more elegant proof due to N. Raghavendra
    <raghu@hri.res.in>, based on Daniel's.  It uses the following
    sequence of observations:

      Lemma app_ass :
       forall (X : Type) (l1 l2 l3 : list X),
         (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.

      Lemma app_length :
       forall (X : Type) (l1 l2 : list X),
         length (l1 ++ l2) = length l1 + length l2.

      Lemma In_app_iff_split :
       forall (X : Type) (x : X) (l : list X),
         In x l ->
         exists (l1 l2 : list X), l = l1 ++ x :: l2.

      Lemma In_both_impl_repeats_app :
       forall (X : Type) (x : X) (l1 l2 : list X),
         In x l1 -> In x l2 -> repeats (l1 ++ l2).

      Lemma In_app_iff_midswap :
       forall (X : Type) (x : X) (l1 l2 l3 l4 : list X),
         In x (l1 ++ l2 ++ l3 ++ l4) ->
         In x (l1 ++ l3 ++ l2 ++ l4).

      Lemma pigeonhole_principle_aux :
       forall (X : Type) (l1 l2 u : list X),
         (forall x : X, In x l1 -> In x (u ++ l2)) ->
         length l2 < length l1 -> repeats (u ++ l1).

      Theorem pigeonhole_principle :
       forall (X : Type) (l1 l2 : list X),
         (forall x : X, In x l1 -> In x l2) ->
         length l2 < length l1 -> repeats l1.
*)

Module Pigeon.

Inductive repeats {X : Type} : list X -> Prop :=
| repeats_1 (x : X) (l : list X)
                (H : In x l) : repeats (x :: l)
| repeats_2 (x : X) (l : list X)
                (H : repeats l) : repeats (x :: l).

Definition pigeonhole_principle_prop (X : Type) : Prop :=
  forall l1 l2 : list X,
    (forall x : X, In x l1 -> In x l2) ->
    length l2 < length l1 -> repeats l1.

Lemma app_ass :
  forall (X : Type) (l1 l2 l3 : list X),
    (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.

Proof.
  intros X l1 l2 l3.
  induction l1 as [ | h t IH].
  {
    - (* l1 = nil *)
    reflexivity.
  }
  {
    - (* l1 = h :: t *)
    simpl.
    rewrite -> IH.
    reflexivity.
  }
Qed.

Lemma app_length :
  forall (X : Type) (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.

Proof.
  intros X l1 l2.
  induction l1 as [ | h t IH].
  {
    - (* l1 = nil *)
    reflexivity.
  }
  {
    - (* l1 = h :: t *)
    simpl.
    rewrite -> IH.
    reflexivity.
  }
Qed.

Lemma In_both_impl_repeats_app :
  forall (X : Type) (x : X) (l1 l2 : list X),
    In x l1 -> In x l2 -> repeats (l1 ++ l2).

Proof.
  intros X x l1.
  induction l1 as [ | h1 t1 IH].
  {
    - (* l1 = nil *)
    intros l2 H1 H2.
    inversion H1.
  }
  {
    - (* l1 = h1 :: t1 *)
    intros l2 H1 H2. simpl in H1.
    destruct H1 as [H3 | H3].
    {
      +
      simpl.
      apply repeats_1.
      apply In_app_iff.
      right.
      rewrite H3.
      apply H2.
    }
    {
      + (* H1 = ai_later z u H3 *)
      simpl.
      apply repeats_2.
      apply IH.
      {
        apply H3.
      }
      {
        apply H2.
      }
    }
  }
Qed.

Lemma In_app_iff_midswap :
  forall (X : Type) (x : X) (l1 l2 l3 l4 : list X),
    In x (l1 ++ l2 ++ l3 ++ l4) -> In x (l1 ++ l3 ++ l2 ++ l4).

Proof.
  intros X x l1 l2 l3 l4 H.
  apply In_app_iff in H.
  destruct H as [H1 | H1r].
  {
    - (* In x l1 *)
    apply In_app_iff.
    left.
    apply H1.
  }
  {
    - (* In x (l2 ++ l3 ++ l4) *)
    apply In_app_iff in H1r.
    destruct H1r as [H2 | H2r].
    {
      + (* In x l1 *)
      apply In_app_iff.
      right.
      apply In_app_iff.
      right.
      apply In_app_iff.
      left.
      apply H2.
    }
    {
      + (* In x (l3 ++ l4) *)
      apply In_app_iff in H2r.
      destruct H2r as [H3 | H3r].
      {
        * (* In x l3 *)
        apply In_app_iff.
        right.
        apply In_app_iff.
        left.
        apply H3.
      }
      {
        * (* In x l4 *)
        apply In_app_iff.
        right.
        apply In_app_iff.
        right.
        apply In_app_iff.
        right.
        apply H3r.
      }
    }
  }
Qed.

Lemma pigeonhole_principle_aux :
  forall (X : Type) (l1 l2 u : list X),
    (forall x : X, In x l1 -> In x (u ++ l2)) ->
    length l2 < length l1 -> repeats (u ++ l1).

Proof.
  intros X l1.
  induction l1 as [ | h1 t1 IH].
  {
    - (* l1 = nil *)
    intros l2 u H1 H2.
    inversion H2.
  }
  {
    - (* l1 = h1 :: t1 *)
    intros l2 u H1 H2.
    assert (H3 : In h1 (u ++ l2)).
    {
      + (* Proof of H3 *)
      apply H1.
      left. reflexivity.
    }
    apply In_app_iff in H3.
    destruct H3 as [H3l | H3r].
    {
      + (* In h1 u *)
      apply (In_both_impl_repeats_app _ h1).
      {
        apply H3l.
      }
      {
        left. reflexivity.
      }
    }
    {
      + (* In h1 l2 *)
      apply in_split in H3r.
      destruct H3r as [v2 H4].
      destruct H4 as [w2 H5].
      assert (H6 : u ++ h1 :: t1 = (u ++ [h1]) ++ t1).
      {
        * (* Proof of H6 *)
        rewrite -> app_ass.
        reflexivity.
      }
      rewrite -> H6.
      apply (IH (v2 ++ w2)).
      {
        * (* Proof of first condition of IH *)
        intros x H7.
        rewrite -> app_ass.
        apply In_app_iff_midswap.
        simpl.
        rewrite <- H5.
        apply H1.
        right.
        apply H7.
      }
      {
        * (* Proof of second condition of IH *)
        unfold lt.
        assert (H8 : length l2 = S (length (v2 ++ w2))).
        {
          rewrite -> H5.
          rewrite -> app_length.
          rewrite -> app_length.
          simpl.
          rewrite <- plus_n_Sm.
          reflexivity.
        }
        rewrite <- H8.
        apply Sn_le_Sm__n_le_m.
        unfold lt in H2.
        simpl in H2.
        apply H2.
      }
    }
  }
Qed.

Theorem pigeonhole_principle :
  forall X : Type,
    pigeonhole_principle_prop X.

Proof.
  intros X.
  unfold pigeonhole_principle_prop.
  intros l1 l2 H1 H2.
  assert (H: l1 = nil ++ l1). { reflexivity. }
  rewrite H.
  apply (pigeonhole_principle_aux _ _ l2).
  {
    intros x H3.
    simpl.
    apply H1.
    apply H3.
  }
  {
    apply H2.
  }
Qed.

End Pigeon.

(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match autmatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function that reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implemement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
Require Import Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne) 

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  (* SOLUTION: *)
  intros.
  rewrite app_exists.
  split.
  - (* matches App implies prop *)
    intros [ [ | b s0 ] [ s1 [ Happ [ Hre0 Hre1 ] ] ] ].
    + left. split.
      * apply Hre0.
      * rewrite Happ. apply Hre1.
    + right. exists s0, s1. injection Happ. intros H1. split.
      * apply H1.
      * split. rewrite H. apply Hre0. apply Hre1.
  - intros [ [ Heps0 Hne1 ] | [ s0 [ s1 [ Happ [ Hre0 Hre1 ] ] ] ] ].
    + exists [ ], (a :: s). split.
      * reflexivity.
      * split.
        ** apply Heps0.
        ** apply Hne1.
    + exists (a :: s0), s1. split.
      * rewrite Happ. reflexivity.
      * split.
        ** apply Hre0.
        ** apply Hre1.
Qed.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne) 

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  (* SOLUTION: *)
  split.
  - intros.
    remember (a :: s) as s'.
    remember (Star re) as re'.
    induction H.
   + discriminate Heqre'.
   + discriminate Heqre'.
   + discriminate Heqre'.
   + discriminate Heqre'.
   + discriminate Heqre'.
   + discriminate Heqs'.
   + destruct s1.
     * apply (IHexp_match2 Heqs' Heqre').
     * exists s1, s2. injection Heqs'. intros H2 H3.
       injection Heqre'. intros H4. split. (* inversion Heqs'. inversion Heqre'. split. *)
       ** rewrite H2. reflexivity.
       ** split.
          *** rewrite <- H3, <- H4. apply H.
          *** apply H0.
  - intros [ s0 [ s1 [ H0 [ H1 H2 ] ] ] ].
    rewrite H0.
    apply (MStarApp (a :: s0) s1). apply H1. apply H2.
Qed.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps) 

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: reg_exp ascii) : bool
  (* SOLUTION: *) :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => false
  | App re0 re1 => (match_eps re0) && (match_eps re1)
  | Union re0 re1 => (match_eps re0) || (match_eps re1)
  | Star re => true
  end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl) 

    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  (* SOLUTION: *)
  unfold refl_matches_eps.
  induction re.
  -(* empty set *)
    apply ReflectF. unfold not. intros. inversion H.
  -(* empty string *)
    apply ReflectT. apply MEmpty.
  -(* char *)
    apply ReflectF. unfold not. intros. inversion H.
  -(* app *)
    simpl. destruct IHre1.
    + destruct IHre2.
      * apply ReflectT. apply (MApp [ ] _ [ ]). apply H. apply H0.
      * apply ReflectF. unfold not. intros. apply H0. inversion H1; subst.
        destruct s1.
        ** apply H6.
        ** discriminate H2.
    + apply ReflectF. unfold not. intros. inversion H0. apply H. destruct s1.
      * apply H4.
      * discriminate H1.
  -(* union *)
    simpl. destruct IHre1.
    + apply ReflectT. apply MUnionL. apply H.
    + destruct IHre2.
      * apply ReflectT. apply MUnionR. apply H0.
      * apply ReflectF. unfold not. intros. inversion H1.
        ** apply H. apply H4.
        ** apply H0. apply H4.
  - apply ReflectT. apply MStar0.
Qed.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive) 

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii
  (* SOLUTION: *) :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char x => if ascii_dec a x then EmptyStr else EmptySet
  | App re0 re1 =>
    Union (App (derive a re0) re1)
          (if match_eps re0 then derive a re1 else EmptySet)
  | Union re0 re1 => Union (derive a re0) (derive a re1)
  | Star re => App (derive a re) (Star re)
  end.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  (* SOLUTION: *)
  reflexivity. Qed.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  (* SOLUTION: *)
  reflexivity. Qed.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  (* SOLUTION: *)
  reflexivity. Qed.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  (* SOLUTION: *)
  reflexivity. Qed.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  (* SOLUTION: *)
  reflexivity. Qed.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  (* SOLUTION: *)
  reflexivity. Qed.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  (* SOLUTION: *)
  reflexivity. Qed.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  (* SOLUTION: *)
  reflexivity. Qed.

(** **** Exercise: 4 stars, standard, optional (derive_corr) 

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
  (* SOLUTION: *)
  unfold derives, is_der.
  induction re.
  - (* EmptySet *)
    simpl. intros. rewrite null_matches_none, null_matches_none.
    reflexivity.
  - (* EmptyStr *)
    simpl. intros. rewrite empty_nomatch_ne, null_matches_none.
    reflexivity.
  - (* Char *)
    simpl. intros. destruct (ascii_dec a t).
    + (* a is character in regex *)
      rewrite e, char_eps_suffix, empty_matches_eps. reflexivity.
    + (* a is not characater in regex. *)
      rewrite null_matches_none.
      apply char_nomatch_char. apply n.
  - (* App *)
    intros. simpl. rewrite app_ne, union_disj, app_exists. split.
    + (* full match implies suffix matches derivation *)
      intros [ [ Hepsmat Hrem ] | [ s0 [ s1 [ H1 [ H2 H3 ] ] ] ] ].
      * right. destruct (match_eps_refl re1).
        ** apply IHre2. apply Hrem.
        ** exfalso. apply H. apply Hepsmat.
      * left. exists s0, s1. split.
        ** apply H1.
        ** split.
           *** apply IHre1. apply H2.
           *** apply H3.
    + (* suffix matches derivation implies full match. *)
      intros [ [ s0 [ s1 [ Happ [ Hre1 Hre2 ] ] ] ] | Hre2 ].
      * right. exists s0, s1. split.
        ** apply Happ.
        ** split.
           *** apply IHre1. apply Hre1.
           *** apply Hre2.
      * destruct (match_eps_refl re1).
        ** left. split.
           *** apply H.
           *** apply IHre2. apply Hre2.
        ** inversion Hre2.
  - (* Union *)
    simpl. intros. rewrite union_disj, union_disj. split.
    + intros [ H0 | H1 ].
      * left. apply IHre1. apply H0.
      * right. apply IHre2. apply H1.
    + intros [ H0 | H1 ].
      * (* matches left union term *)
        left. apply IHre1. apply H0.
      * right. apply IHre2. apply H1.
  - (* Star *)
    simpl. intros. rewrite star_ne, app_exists. split.
    + intros [ s0 [ s1 [ Heq [ Hmat Hmatstar] ] ] ].
      exists s0, s1. split.
      * apply Heq.
      * split.
        ** apply IHre. apply Hmat.
        ** apply Hmatstar.
    + intros [ s0 [ s1 [ Happ [ Hre Hstar ] ] ] ].
      exists s0, s1. split.
      * apply Happ.
      * split.
        ** apply IHre. apply Hre.
        ** apply Hstar.
Qed.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] matches regexes if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match) 

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool
  (* SOLUTION: *) :=
  match s with
  | [ ] => match_eps re
  | a :: s' => regex_match s' (derive a re)
  end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_refl) 

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_refl : matches_regex regex_match.
Proof.
  (* SOLUTION: *)
  unfold matches_regex.
  induction s.
  - apply match_eps_refl.
  - simpl. intros. destruct (IHs (derive x re)).
    + apply ReflectT.
      apply (derive_corr x re).
      apply H.
    + apply ReflectF. unfold not. intros.
      apply H.
      apply (derive_corr x re).
      apply H0.
Qed.
(** [] *)

(* 04 Mar 2020 *)

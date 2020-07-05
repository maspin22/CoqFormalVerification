Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Hoare.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From PLF Require Import Hoare.
Import Check.

Goal True.

idtac "-------------------  hoare_post_true  --------------------".
idtac " ".

idtac "#> hoare_post_true".
idtac "Possible points: 1".
check_type @hoare_post_true (
(forall (P Q : Assertion) (c : Imp.com),
 (forall st : Imp.state, Q st) -> {{P}} c {{Q}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_post_true.
Goal True.
idtac " ".

idtac "-------------------  hoare_pre_false  --------------------".
idtac " ".

idtac "#> hoare_pre_false".
idtac "Possible points: 1".
check_type @hoare_pre_false (
(forall (P Q : Assertion) (c : Imp.com),
 (forall st : Imp.state, ~ P st) -> {{P}} c {{Q}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_pre_false.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_wrong  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_asgn_wrong".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_hoare_asgn_wrong.
idtac " ".

idtac "-------------------  hoare_asgn_fwd  --------------------".
idtac " ".

idtac "#> hoare_asgn_fwd".
idtac "Advanced".
idtac "Possible points: 3".
check_type @hoare_asgn_fwd (
(forall (m : nat) (a : Imp.aexp) (P : Imp.state -> Prop),
 {{fun st : Imp.state => P st /\ st Imp.X = m}} Imp.CAss Imp.X a
 {{fun st : Imp.state =>
   P (@Maps.t_update nat st Imp.X m) /\
   st Imp.X = Imp.aeval (@Maps.t_update nat st Imp.X m) a}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_fwd.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_examples_2  --------------------".
idtac " ".

idtac "#> assn_sub_ex1'".
idtac "Possible points: 1".
check_type @assn_sub_ex1' (
({{fun st : Imp.state => Aexp_of_aexp (Imp.AId Imp.X) st <= Aexp_of_nat 5 st}}
 Imp.CAss Imp.X (Imp.AMult (Imp.ANum 2) (Imp.AId Imp.X))
 {{fun st : Imp.state => Aexp_of_aexp (Imp.AId Imp.X) st <= Aexp_of_nat 10 st}})).
idtac "Assumptions:".
Abort.
Print Assumptions assn_sub_ex1'.
Goal True.
idtac " ".

idtac "#> assn_sub_ex2'".
idtac "Possible points: 1".
check_type @assn_sub_ex2' (
({{(fun st0 : Imp.state => (Aexp_of_nat 0 st0 <= Aexp_of_nat 3 st0)%nat) /\
   (fun st0 : Imp.state => (Aexp_of_nat 3 st0 <= Aexp_of_nat 5 st0)%nat)}}
 Imp.CAss Imp.X (Imp.ANum 3)
 {{(fun st0 : Imp.state =>
    (Aexp_of_nat 0 st0 <= Aexp_of_aexp (Imp.AId Imp.X) st0)%nat) /\
   (fun st0 : Imp.state =>
    (Aexp_of_aexp (Imp.AId Imp.X) st0 <= Aexp_of_nat 5 st0)%nat)}})).
idtac "Assumptions:".
Abort.
Print Assumptions assn_sub_ex2'.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_example4  --------------------".
idtac " ".

idtac "#> hoare_asgn_example4".
idtac "Possible points: 2".
check_type @hoare_asgn_example4 (
({{assert_of_Prop True}}
 Imp.CSeq (Imp.CAss Imp.X (Imp.ANum 1)) (Imp.CAss Imp.Y (Imp.ANum 2))
 {{(fun st0 : Imp.state =>
    (Aexp_of_aexp (Imp.AId Imp.X) st0 = Aexp_of_nat 1 st0)%type) /\
   (fun st0 : Imp.state =>
    (Aexp_of_aexp (Imp.AId Imp.Y) st0 = Aexp_of_nat 2 st0)%type)}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_example4.
Goal True.
idtac " ".

idtac "-------------------  swap_exercise  --------------------".
idtac " ".

idtac "#> swap_exercise".
idtac "Possible points: 3".
check_type @swap_exercise (
({{fun st : Imp.state =>
   Aexp_of_aexp (Imp.AId Imp.X) st <= Aexp_of_aexp (Imp.AId Imp.Y) st}}
 swap_program
 {{fun st : Imp.state =>
   Aexp_of_aexp (Imp.AId Imp.Y) st <= Aexp_of_aexp (Imp.AId Imp.X) st}})).
idtac "Assumptions:".
Abort.
Print Assumptions swap_exercise.
Goal True.
idtac " ".

idtac "-------------------  invalid_triple  --------------------".
idtac " ".

idtac "#> invalid_triple".
idtac "Possible points: 6".
check_type @invalid_triple (
(~
 (forall (a : Imp.aexp) (n : nat),
  {{fun st : Imp.state => Aexp_of_aexp a st = Aexp_of_nat n st}}
  Imp.CSeq (Imp.CAss Imp.X (Imp.ANum 3)) (Imp.CAss Imp.Y a)
  {{fun st : Imp.state => Aexp_of_aexp (Imp.AId Imp.Y) st = Aexp_of_nat n st}}))).
idtac "Assumptions:".
Abort.
Print Assumptions invalid_triple.
Goal True.
idtac " ".

idtac "-------------------  if_minus_plus  --------------------".
idtac " ".

idtac "#> if_minus_plus".
idtac "Possible points: 2".
check_type @if_minus_plus (
({{assert_of_Prop True}}
 Imp.CIf (Imp.BLe (Imp.AId Imp.X) (Imp.AId Imp.Y))
   (Imp.CAss Imp.Z (Imp.AMinus (Imp.AId Imp.Y) (Imp.AId Imp.X)))
   (Imp.CAss Imp.Y (Imp.APlus (Imp.AId Imp.X) (Imp.AId Imp.Z)))
 {{fun st : Imp.state =>
   Aexp_of_aexp (Imp.AId Imp.Y) st =
   (mkAexp
      (fun st0 : Imp.state =>
       (Aexp_of_aexp (Imp.AId Imp.X) st0 + Aexp_of_aexp (Imp.AId Imp.Z) st0)%nat))
     st}})).
idtac "Assumptions:".
Abort.
Print Assumptions if_minus_plus.
Goal True.
idtac " ".

idtac "-------------------  if1_ceval  --------------------".
idtac " ".

idtac "#> If1.if1true_test".
idtac "Possible points: 1".
check_type @If1.if1true_test (
(If1.ceval
   (If1.CIf1 (Imp.BEq (Imp.AId Imp.X) (Imp.ANum 0))
      (If1.CAss Imp.X (Imp.ANum 1))) Imp.empty_st
   (@Maps.t_update nat Imp.empty_st Imp.X 1))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.if1true_test.
Goal True.
idtac " ".

idtac "#> If1.if1false_test".
idtac "Possible points: 1".
check_type @If1.if1false_test (
(If1.ceval
   (If1.CIf1 (Imp.BEq (Imp.AId Imp.X) (Imp.ANum 0))
      (If1.CAss Imp.X (Imp.ANum 1)))
   (@Maps.t_update nat Imp.empty_st Imp.X 2)
   (@Maps.t_update nat Imp.empty_st Imp.X 2))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.if1false_test.
Goal True.
idtac " ".

idtac "-------------------  hoare_if1  --------------------".
idtac " ".

idtac "#> Manually graded: If1.hoare_if1".
idtac "Possible points: 2".
print_manual_grade If1.manual_grade_for_hoare_if1.
idtac " ".

idtac "-------------------  hoare_if1_good  --------------------".
idtac " ".

idtac "#> If1.hoare_if1_good".
idtac "Possible points: 2".
check_type @If1.hoare_if1_good (
(If1.hoare_triple
   (fun st : Imp.state =>
    (mkAexp
       (fun st0 : Imp.state =>
        (Aexp_of_aexp (Imp.AId Imp.X) st0 + Aexp_of_aexp (Imp.AId Imp.Y) st0)%nat))
      st = Aexp_of_aexp (Imp.AId Imp.Z) st)
   (If1.CIf1 (Imp.BNot (Imp.BEq (Imp.AId Imp.Y) (Imp.ANum 0)))
      (If1.CAss Imp.X (Imp.APlus (Imp.AId Imp.X) (Imp.AId Imp.Y))))
   (fun st : Imp.state =>
    Aexp_of_aexp (Imp.AId Imp.X) st = Aexp_of_aexp (Imp.AId Imp.Z) st))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.hoare_if1_good.
Goal True.
idtac " ".

idtac "-------------------  hoare_repeat  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_repeat".
idtac "Advanced".
idtac "Possible points: 6".
print_manual_grade manual_grade_for_hoare_repeat.
idtac " ".

idtac "-------------------  hoare_havoc  --------------------".
idtac " ".

idtac "#> Himp.hoare_havoc".
idtac "Possible points: 3".
check_type @Himp.hoare_havoc (
(forall (Q : Assertion) (X : String.string),
 Himp.hoare_triple (Himp.havoc_pre X Q) (Himp.CHavoc X) Q)).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.hoare_havoc.
Goal True.
idtac " ".

idtac "-------------------  havoc_post  --------------------".
idtac " ".

idtac "#> Himp.havoc_post".
idtac "Possible points: 3".
check_type @Himp.havoc_post (
(forall (P : Assertion) (X : String.string),
 Himp.hoare_triple P (Himp.CHavoc X)
   (fun st : Imp.state => exists n : nat, (P [X |-> Imp.ANum n]) st))).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.havoc_post.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 31".
idtac "Max points - advanced: 40".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- hoare_post_true ---------".
Print Assumptions hoare_post_true.
idtac "---------- hoare_pre_false ---------".
Print Assumptions hoare_pre_false.
idtac "---------- hoare_asgn_wrong ---------".
idtac "MANUAL".
idtac "---------- assn_sub_ex1' ---------".
Print Assumptions assn_sub_ex1'.
idtac "---------- assn_sub_ex2' ---------".
Print Assumptions assn_sub_ex2'.
idtac "---------- hoare_asgn_example4 ---------".
Print Assumptions hoare_asgn_example4.
idtac "---------- swap_exercise ---------".
Print Assumptions swap_exercise.
idtac "---------- invalid_triple ---------".
Print Assumptions invalid_triple.
idtac "---------- if_minus_plus ---------".
Print Assumptions if_minus_plus.
idtac "---------- If1.if1true_test ---------".
Print Assumptions If1.if1true_test.
idtac "---------- If1.if1false_test ---------".
Print Assumptions If1.if1false_test.
idtac "---------- hoare_if1 ---------".
idtac "MANUAL".
idtac "---------- If1.hoare_if1_good ---------".
Print Assumptions If1.hoare_if1_good.
idtac "---------- Himp.hoare_havoc ---------".
Print Assumptions Himp.hoare_havoc.
idtac "---------- Himp.havoc_post ---------".
Print Assumptions Himp.havoc_post.
idtac "".
idtac "********** Advanced **********".
idtac "---------- hoare_asgn_fwd ---------".
Print Assumptions hoare_asgn_fwd.
idtac "---------- hoare_repeat ---------".
idtac "MANUAL".
Abort.

(* 09 Apr 2020 *)

(* 09 Apr 2020 *)

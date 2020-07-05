Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PRELIM Require Import Prelim.

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

From PRELIM Require Import Prelim.
Import Check.

Goal True.

idtac "-------------------  incr  --------------------".
idtac " ".

idtac "#> test_incr_tern1".
idtac "Possible points: 0.5".
check_type @test_incr_tern1 ((incr z__zero = z__one)).
idtac "Assumptions:".
Abort.
Print Assumptions test_incr_tern1.
Goal True.
idtac " ".

idtac "#> test_incr_tern2".
idtac "Possible points: 0.5".
check_type @test_incr_tern2 ((incr z__three = z__four)).
idtac "Assumptions:".
Abort.
Print Assumptions test_incr_tern2.
Goal True.
idtac " ".

idtac "#> test_incr_tern3".
idtac "Possible points: 0.5".
check_type @test_incr_tern3 ((incr z__one = z__two)).
idtac "Assumptions:".
Abort.
Print Assumptions test_incr_tern3.
Goal True.
idtac " ".

idtac "#> test_incr_tern4".
idtac "Possible points: 0.5".
check_type @test_incr_tern4 ((incr z__negfour = z__negthree)).
idtac "Assumptions:".
Abort.
Print Assumptions test_incr_tern4.
Goal True.
idtac " ".

idtac "-------------------  rep_invariant  --------------------".
idtac " ".

idtac "#> test_incr_tern5".
idtac "Possible points: 1".
check_type @test_incr_tern5 ((incr z__negone = z__zero)).
idtac "Assumptions:".
Abort.
Print Assumptions test_incr_tern5.
Goal True.
idtac " ".

idtac "-------------------  convert_int_nat  --------------------".
idtac " ".

idtac "#> test_convert1".
idtac "Possible points: 1".
check_type @test_convert1 ((nat_of_int (int_of_nat 42) = 42)).
idtac "Assumptions:".
Abort.
Print Assumptions test_convert1.
Goal True.
idtac " ".

idtac "#> test_convert2".
idtac "Possible points: 1".
check_type @test_convert2 ((int_of_nat (nat_of_int z__zero) = z__zero)).
idtac "Assumptions:".
Abort.
Print Assumptions test_convert2.
Goal True.
idtac " ".

idtac "-------------------  nat_of_int_correct  --------------------".
idtac " ".

idtac "#> nat_of_int_correct_Z".
idtac "Possible points: 0.5".
check_type @nat_of_int_correct_Z ((nat_of_int Z = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions nat_of_int_correct_Z.
Goal True.
idtac " ".

idtac "#> nat_of_int_correct_T_zero".
idtac "Possible points: 0.5".
check_type @nat_of_int_correct_T_zero (
(forall (z : int) (n : nat),
 nat_of_int z = n -> nat_of_int (T_zero z) = 3 * n)).
idtac "Assumptions:".
Abort.
Print Assumptions nat_of_int_correct_T_zero.
Goal True.
idtac " ".

idtac "#> nat_of_int_correct_T_pos".
idtac "Possible points: 0.5".
check_type @nat_of_int_correct_T_pos (
(forall (z : int) (n : nat),
 nat_of_int z = n -> nat_of_int (T_pos z) = S (3 * n))).
idtac "Assumptions:".
Abort.
Print Assumptions nat_of_int_correct_T_pos.
Goal True.
idtac " ".

idtac "#> nat_of_int_correct_T_neg".
idtac "Possible points: 0.5".
check_type @nat_of_int_correct_T_neg (
(forall (z : int) (n : nat),
 nat_of_int z = n -> nat_of_int (T_neg z) = Nat.pred (3 * n))).
idtac "Assumptions:".
Abort.
Print Assumptions nat_of_int_correct_T_neg.
Goal True.
idtac " ".

idtac "-------------------  int_of_nat_hom  --------------------".
idtac " ".

idtac "#> int_of_nat_hom".
idtac "Possible points: 2".
check_type @int_of_nat_hom ((forall n : nat, incr (int_of_nat n) = int_of_nat (S n))).
idtac "Assumptions:".
Abort.
Print Assumptions int_of_nat_hom.
Goal True.
idtac " ".

idtac "-------------------  pos  --------------------".
idtac " ".

idtac "#> ex_pos1".
idtac "Possible points: 0.5".
check_type @ex_pos1 ((pos z__one)).
idtac "Assumptions:".
Abort.
Print Assumptions ex_pos1.
Goal True.
idtac " ".

idtac "#> ex_pos2".
idtac "Possible points: 0.5".
check_type @ex_pos2 ((pos z__two)).
idtac "Assumptions:".
Abort.
Print Assumptions ex_pos2.
Goal True.
idtac " ".

idtac "#> ex_pos3".
idtac "Possible points: 0.5".
check_type @ex_pos3 ((pos z__three)).
idtac "Assumptions:".
Abort.
Print Assumptions ex_pos3.
Goal True.
idtac " ".

idtac "#> ex_pos4".
idtac "Possible points: 0.5".
check_type @ex_pos4 ((pos z__four)).
idtac "Assumptions:".
Abort.
Print Assumptions ex_pos4.
Goal True.
idtac " ".

idtac "#> ex_pos5".
idtac "Possible points: 0.5".
check_type @ex_pos5 ((~ pos z__zero)).
idtac "Assumptions:".
Abort.
Print Assumptions ex_pos5.
Goal True.
idtac " ".

idtac "#> ex_pos6".
idtac "Possible points: 0.5".
check_type @ex_pos6 ((~ pos z__negone)).
idtac "Assumptions:".
Abort.
Print Assumptions ex_pos6.
Goal True.
idtac " ".

idtac "-------------------  incr_preserves_nonneg  --------------------".
idtac " ".

idtac "#> incr_preserves_nonneg".
idtac "Possible points: 3".
check_type @incr_preserves_nonneg ((forall z : int, nonneg z -> nonneg (incr z))).
idtac "Assumptions:".
Abort.
Print Assumptions incr_preserves_nonneg.
Goal True.
idtac " ".

idtac "-------------------  nat_of_int_hom  --------------------".
idtac " ".

idtac "#> nat_of_int_hom".
idtac "Possible points: 6".
check_type @nat_of_int_hom (
(forall n : int, nonneg n -> nat_of_int (incr n) = S (nat_of_int n))).
idtac "Assumptions:".
Abort.
Print Assumptions nat_of_int_hom.
Goal True.
idtac " ".

idtac "-------------------  nonneg_nat  --------------------".
idtac " ".

idtac "#> nonneg_nat".
idtac "Possible points: 2".
check_type @nonneg_nat ((forall n : nat, nonneg (int_of_nat n))).
idtac "Assumptions:".
Abort.
Print Assumptions nonneg_nat.
Goal True.
idtac " ".

idtac "-------------------  left_inverse  --------------------".
idtac " ".

idtac "#> left_inverse".
idtac "Possible points: 2".
check_type @left_inverse ((forall n : nat, nat_of_int (int_of_nat n) = n)).
idtac "Assumptions:".
Abort.
Print Assumptions left_inverse.
Goal True.
idtac " ".

idtac "-------------------  prop_warmup  --------------------".
idtac " ".

idtac "#> test_atom_in1".
idtac "Possible points: 0.5".
check_type @test_atom_in1 ((atom_in 42 test_prop = true)).
idtac "Assumptions:".
Abort.
Print Assumptions test_atom_in1.
Goal True.
idtac " ".

idtac "#> test_atom_in2".
idtac "Possible points: 0.5".
check_type @test_atom_in2 ((atom_in 0 test_prop = false)).
idtac "Assumptions:".
Abort.
Print Assumptions test_atom_in2.
Goal True.
idtac " ".

idtac "-------------------  provable1  --------------------".
idtac " ".

idtac "#> true_provable".
idtac "Possible points: 0.5".
check_type @true_provable ((provable (@nil prop) PTrue)).
idtac "Assumptions:".
Abort.
Print Assumptions true_provable.
Goal True.
idtac " ".

idtac "#> hyp_provable".
idtac "Possible points: 0.5".
check_type @hyp_provable ((forall p : prop, provable (p :: @nil prop) p)).
idtac "Assumptions:".
Abort.
Print Assumptions hyp_provable.
Goal True.
idtac " ".

idtac "-------------------  provable2  --------------------".
idtac " ".

idtac "#> mp_provable".
idtac "Possible points: 1".
check_type @mp_provable (
(forall p q : prop, provable (@nil prop) (PImp p (PImp (PImp p q) q)))).
idtac "Assumptions:".
Abort.
Print Assumptions mp_provable.
Goal True.
idtac " ".

idtac "#> ex_falso_provable".
idtac "Possible points: 0.5".
check_type @ex_falso_provable ((forall p : prop, provable (@nil prop) (PImp PFalse p))).
idtac "Assumptions:".
Abort.
Print Assumptions ex_falso_provable.
Goal True.
idtac " ".

idtac "#> false_not_provable".
idtac "Possible points: 0.5".
check_type @false_not_provable ((~ provable (@nil prop) PFalse)).
idtac "Assumptions:".
Abort.
Print Assumptions false_not_provable.
Goal True.
idtac " ".

idtac "-------------------  true_equiv  --------------------".
idtac " ".

idtac "#> true_equiv".
idtac "Possible points: 1".
check_type @true_equiv ((equiv True PTrue)).
idtac "Assumptions:".
Abort.
Print Assumptions true_equiv.
Goal True.
idtac " ".

idtac "-------------------  false_equiv  --------------------".
idtac " ".

idtac "#> false_equiv".
idtac "Possible points: 1".
check_type @false_equiv ((equiv False PFalse)).
idtac "Assumptions:".
Abort.
Print Assumptions false_equiv.
Goal True.
idtac " ".

idtac "-------------------  proj1_provable  --------------------".
idtac " ".

idtac "#> proj1_provable".
idtac "Possible points: 1".
check_type @proj1_provable (
(forall p q : prop, provable (@nil prop) (PImp (PAnd p q) p))).
idtac "Assumptions:".
Abort.
Print Assumptions proj1_provable.
Goal True.
idtac " ".

idtac "-------------------  and_equiv  --------------------".
idtac " ".

idtac "#> and_equiv".
idtac "Possible points: 2".
check_type @and_equiv (
(forall (P Q : Prop) (p q : prop),
 equiv P p -> equiv Q q -> equiv (P /\ Q) (PAnd p q))).
idtac "Assumptions:".
Abort.
Print Assumptions and_equiv.
Goal True.
idtac " ".

idtac "-------------------  injl_provable  --------------------".
idtac " ".

idtac "#> injl_provable".
idtac "Possible points: 1".
check_type @injl_provable ((forall p q : prop, provable (@nil prop) (PImp p (POr p q)))).
idtac "Assumptions:".
Abort.
Print Assumptions injl_provable.
Goal True.
idtac " ".

idtac "-------------------  or_equiv  --------------------".
idtac " ".

idtac "#> or_equiv".
idtac "Possible points: 3".
check_type @or_equiv (
(forall (P Q : Prop) (p q : prop),
 equiv P p -> equiv Q q -> equiv (P \/ Q) (POr p q))).
idtac "Assumptions:".
Abort.
Print Assumptions or_equiv.
Goal True.
idtac " ".

idtac "-------------------  imp_correct  --------------------".
idtac " ".

idtac "#> imp_correct".
idtac "Possible points: 2".
check_type @imp_correct (
(forall (P Q : Prop) (p q : prop),
 equiv P p -> equiv Q q -> provable (@nil prop) (PImp p q) -> P -> Q)).
idtac "Assumptions:".
Abort.
Print Assumptions imp_correct.
Goal True.
idtac " ".

idtac "-------------------  imp_complete  --------------------".
idtac " ".

idtac "#> imp_complete".
idtac "Possible points: 2".
check_type @imp_complete (
(forall (P Q : Prop) (p q : prop),
 equiv P p -> equiv Q q -> (P -> Q) -> provable (@nil prop) (PImp p q))).
idtac "Assumptions:".
Abort.
Print Assumptions imp_complete.
Goal True.
idtac " ".

idtac "-------------------  hours  --------------------".
idtac " ".

idtac "#> hours_spent_test".
idtac "Possible points: 1".
check_type @hours_spent_test ((Nat.ltb 0 hours_spent = true)).
idtac "Assumptions:".
Abort.
Print Assumptions hours_spent_test.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 43".
idtac "Max points - advanced: 43".
idtac "".
idtac "Allowed Axioms:".
idtac "pr_cut".
idtac "pr_distr_imp".
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
idtac "---------- test_incr_tern1 ---------".
Print Assumptions test_incr_tern1.
idtac "---------- test_incr_tern2 ---------".
Print Assumptions test_incr_tern2.
idtac "---------- test_incr_tern3 ---------".
Print Assumptions test_incr_tern3.
idtac "---------- test_incr_tern4 ---------".
Print Assumptions test_incr_tern4.
idtac "---------- test_incr_tern5 ---------".
Print Assumptions test_incr_tern5.
idtac "---------- test_convert1 ---------".
Print Assumptions test_convert1.
idtac "---------- test_convert2 ---------".
Print Assumptions test_convert2.
idtac "---------- nat_of_int_correct_Z ---------".
Print Assumptions nat_of_int_correct_Z.
idtac "---------- nat_of_int_correct_T_zero ---------".
Print Assumptions nat_of_int_correct_T_zero.
idtac "---------- nat_of_int_correct_T_pos ---------".
Print Assumptions nat_of_int_correct_T_pos.
idtac "---------- nat_of_int_correct_T_neg ---------".
Print Assumptions nat_of_int_correct_T_neg.
idtac "---------- int_of_nat_hom ---------".
Print Assumptions int_of_nat_hom.
idtac "---------- ex_pos1 ---------".
Print Assumptions ex_pos1.
idtac "---------- ex_pos2 ---------".
Print Assumptions ex_pos2.
idtac "---------- ex_pos3 ---------".
Print Assumptions ex_pos3.
idtac "---------- ex_pos4 ---------".
Print Assumptions ex_pos4.
idtac "---------- ex_pos5 ---------".
Print Assumptions ex_pos5.
idtac "---------- ex_pos6 ---------".
Print Assumptions ex_pos6.
idtac "---------- incr_preserves_nonneg ---------".
Print Assumptions incr_preserves_nonneg.
idtac "---------- nat_of_int_hom ---------".
Print Assumptions nat_of_int_hom.
idtac "---------- nonneg_nat ---------".
Print Assumptions nonneg_nat.
idtac "---------- left_inverse ---------".
Print Assumptions left_inverse.
idtac "---------- test_atom_in1 ---------".
Print Assumptions test_atom_in1.
idtac "---------- test_atom_in2 ---------".
Print Assumptions test_atom_in2.
idtac "---------- true_provable ---------".
Print Assumptions true_provable.
idtac "---------- hyp_provable ---------".
Print Assumptions hyp_provable.
idtac "---------- mp_provable ---------".
Print Assumptions mp_provable.
idtac "---------- ex_falso_provable ---------".
Print Assumptions ex_falso_provable.
idtac "---------- false_not_provable ---------".
Print Assumptions false_not_provable.
idtac "---------- true_equiv ---------".
Print Assumptions true_equiv.
idtac "---------- false_equiv ---------".
Print Assumptions false_equiv.
idtac "---------- proj1_provable ---------".
Print Assumptions proj1_provable.
idtac "---------- and_equiv ---------".
Print Assumptions and_equiv.
idtac "---------- injl_provable ---------".
Print Assumptions injl_provable.
idtac "---------- or_equiv ---------".
Print Assumptions or_equiv.
idtac "---------- imp_correct ---------".
Print Assumptions imp_correct.
idtac "---------- imp_complete ---------".
Print Assumptions imp_complete.
idtac "---------- hours_spent_test ---------".
Print Assumptions hours_spent_test.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 02 Mar 2020 *)

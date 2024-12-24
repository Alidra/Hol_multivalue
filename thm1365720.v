Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1365720_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm1365403_spec.
Require Import thm1365404_spec.
Require Import thm1365406_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1365412 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem1365413 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem1365412 n m h1)). Qed.
Lemma lem1365414 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem1365415 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem1365414 m n h1)). Qed.
Lemma lem1365416 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem1365413 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem1365415 m n h1)). Qed.
Lemma lem1365417 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem1365416 m n)). Qed.
Lemma lem1365418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1365419 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem1365418) (@lem1365417 m)). Qed.
Lemma lem1365420 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem1365419 m)). Qed.
Lemma lem1365421 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1365422 : term7 = term8.
Proof. exact (MK_COMB (@lem1365421) (@lem1365420)). Qed.
Lemma lem1365423 : term8.
Proof. exact (EQ_MP (@lem1365422) (@lem97961)). Qed.
Lemma lem1365424 (y : real) : term9 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1365425 (y : real) : (term9 y) = (term10 y).
Proof. exact (eq_refl (term9 y)). Qed.
Lemma lem1365426 (y : real) : term10 y.
Proof. exact (EQ_MP (@lem1365425 y) (@lem1365424 y)). Qed.
Lemma lem1365427 (y : real) (x : real) : term11 y x.
Proof. exact (@lem1365426 y x). Qed.
Lemma lem1365428 (y : real) (x : real) : (term11 y x) = ((real_lt x y) = (term12 y x)).
Proof. exact (eq_refl (term11 y x)). Qed.
Lemma lem1365430 (m : nat) : term13 m.
Proof. exact (@lem1365423 m). Qed.
Lemma lem1365431 (m : nat) : (term13 m) = (term4 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem1365432 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1365431 m) (@lem1365430 m)). Qed.
Lemma lem1365433 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem1365432 m n). Qed.
Lemma lem1365434 (m : nat) (n : nat) : (term14 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem1365439 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1365440 (m : nat) (n : nat) : ((term15 m n) = False) = (term16 m n).
Proof. exact (@lem1365439 (term15 m n)). Qed.
Lemma lem1365442 (y : real) (x : real) : (real_lt x y) = (term12 y x).
Proof. exact (EQ_MP (@lem1365428 y x) (@lem1365427 y x)). Qed.
Lemma lem1365443 (n : nat) (m : nat) : (term15 m n) = (term17 n m).
Proof. exact (@lem1365442 (term18 n) (real_of_num m)). Qed.
Lemma lem1365445 (m : nat) (n : nat) : (term19 m n) = True.
Proof. exact (proj1 (@lem1365403 m n)). Qed.
Lemma lem1365446 (n : nat) (m : nat) : (term19 n m) = True.
Proof. exact (@lem1365445 n m). Qed.
Lemma lem1365447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1365448 (n : nat) (m : nat) : (term17 n m) = (~ True).
Proof. exact (MK_COMB (@lem1365447) (@lem1365446 n m)). Qed.
Lemma lem1365450 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1365451 (n : nat) (m : nat) : (term17 n m) = False.
Proof. exact (TRANS (@lem1365448 n m) (@lem1365450)). Qed.
Lemma lem1365452 (m : nat) (n : nat) : (term15 m n) = False.
Proof. exact (TRANS (@lem1365443 n m) (@lem1365451 n m)). Qed.
Lemma lem1365453 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1365454 (m : nat) (n : nat) : (term16 m n) = (~ False).
Proof. exact (MK_COMB (@lem1365453) (@lem1365452 m n)). Qed.
Lemma lem1365456 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1365457 (m : nat) (n : nat) : (term16 m n) = True.
Proof. exact (TRANS (@lem1365454 m n) (@lem1365456)). Qed.
Lemma lem1365458 (m : nat) (n : nat) : ((term15 m n) = False) = True.
Proof. exact (TRANS (@lem1365440 m n) (@lem1365457 m n)). Qed.
Lemma lem1365459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365460 (m : nat) (n : nat) : (term20 m n) = (and True).
Proof. exact (MK_COMB (@lem1365459) (@lem1365458 m n)). Qed.
Lemma lem1365466 (y : real) (x : real) : (real_lt x y) = (term12 y x).
Proof. exact (EQ_MP (@lem1365428 y x) (@lem1365427 y x)). Qed.
Lemma lem1365467 (n : nat) (m : nat) : (term21 m n) = (term22 n m).
Proof. exact (@lem1365466 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1365469 (m : nat) (n : nat) : (term23 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem1365404 m n)). Qed.
Lemma lem1365470 (n : nat) (m : nat) : (term23 n m) = (Peano.le n m).
Proof. exact (@lem1365469 n m). Qed.
Lemma lem1365471 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1365472 (n : nat) (m : nat) : (term22 n m) = (term0 n m).
Proof. exact (MK_COMB (@lem1365471) (@lem1365470 n m)). Qed.
Lemma lem1365473 (n : nat) (m : nat) : (term21 m n) = (term0 n m).
Proof. exact (TRANS (@lem1365467 n m) (@lem1365472 n m)). Qed.
Lemma lem1365474 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365475 (n : nat) (m : nat) : (term24 m n) = (term25 n m).
Proof. exact (MK_COMB (@lem1365474) (@lem1365473 n m)). Qed.
Lemma lem1365477 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem1365434 m n) (@lem1365433 m n)). Qed.
Lemma lem1365478 (n : nat) (m : nat) : (Peano.lt m n) = (term0 n m).
Proof. exact (@lem1365477 n m). Qed.
Lemma lem1365479 (n : nat) (m : nat) : ((term21 m n) = (Peano.lt m n)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem1365475 n m) (@lem1365478 n m)). Qed.
Lemma lem1365481 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1365482 (x : Prop) : (x = x) = True.
Proof. exact (@lem1365481 Prop x). Qed.
Lemma lem1365483 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem1365482 (term0 n m)). Qed.
Lemma lem1365484 (m : nat) (n : nat) : ((term21 m n) = (Peano.lt m n)) = True.
Proof. exact (TRANS (@lem1365479 n m) (@lem1365483 n m)). Qed.
Lemma lem1365485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365486 (m : nat) (n : nat) : (term26 m n) = (and True).
Proof. exact (MK_COMB (@lem1365485) (@lem1365484 m n)). Qed.
Lemma lem1365492 (y : real) (x : real) : (real_lt x y) = (term12 y x).
Proof. exact (EQ_MP (@lem1365428 y x) (@lem1365427 y x)). Qed.
Lemma lem1365493 (n : nat) (m : nat) : (term27 m n) = (term28 n m).
Proof. exact (@lem1365492 (term18 n) (term18 m)). Qed.
Lemma lem1365495 (n : nat) (m : nat) : (term29 m n) = (Peano.le n m).
Proof. exact (proj1 (@lem1365406 m n)). Qed.
Lemma lem1365496 (m : nat) (n : nat) : (term29 n m) = (Peano.le m n).
Proof. exact (@lem1365495 m n). Qed.
Lemma lem1365497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1365498 (m : nat) (n : nat) : (term28 n m) = (term0 m n).
Proof. exact (MK_COMB (@lem1365497) (@lem1365496 m n)). Qed.
Lemma lem1365499 (m : nat) (n : nat) : (term27 m n) = (term0 m n).
Proof. exact (TRANS (@lem1365493 n m) (@lem1365498 m n)). Qed.
Lemma lem1365500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365501 (m : nat) (n : nat) : (term30 m n) = (term25 m n).
Proof. exact (MK_COMB (@lem1365500) (@lem1365499 m n)). Qed.
Lemma lem1365503 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem1365434 m n) (@lem1365433 m n)). Qed.
Lemma lem1365504 (m : nat) (n : nat) : ((term27 m n) = (Peano.lt n m)) = ((term0 m n) = (term0 m n)).
Proof. exact (MK_COMB (@lem1365501 m n) (@lem1365503 m n)). Qed.
Lemma lem1365506 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1365507 (x : Prop) : (x = x) = True.
Proof. exact (@lem1365506 Prop x). Qed.
Lemma lem1365508 (m : nat) (n : nat) : ((term0 m n) = (term0 m n)) = True.
Proof. exact (@lem1365507 (term0 m n)). Qed.
Lemma lem1365509 (n : nat) (m : nat) : ((term27 m n) = (Peano.lt n m)) = True.
Proof. exact (TRANS (@lem1365504 m n) (@lem1365508 m n)). Qed.
Lemma lem1365510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365511 (n : nat) (m : nat) : (term31 n m) = (and True).
Proof. exact (MK_COMB (@lem1365510) (@lem1365509 n m)). Qed.
Lemma lem1365515 (y : real) (x : real) : (real_lt x y) = (term12 y x).
Proof. exact (EQ_MP (@lem1365428 y x) (@lem1365427 y x)). Qed.
Lemma lem1365516 (n : nat) (m : nat) : (term32 m n) = (term33 n m).
Proof. exact (@lem1365515 (real_of_num n) (term18 m)). Qed.
Lemma lem1365518 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem1365519 (n : nat) (m : nat) : (term34 n m) = (term35 n m).
Proof. exact (@lem1365518 n m). Qed.
Lemma lem1365526 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1365527 (n : nat) (m : nat) : (term33 n m) = (term36 n m).
Proof. exact (MK_COMB (@lem1365526) (@lem1365519 n m)). Qed.
Lemma lem1365528 (n : nat) (m : nat) : (term32 m n) = (term36 n m).
Proof. exact (TRANS (@lem1365516 n m) (@lem1365527 n m)). Qed.
Lemma lem1365529 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365530 (n : nat) (m : nat) : (term37 m n) = (term38 n m).
Proof. exact (MK_COMB (@lem1365529) (@lem1365528 n m)). Qed.
Lemma lem1365537 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem1365538 (m : nat) (n : nat) : ((term32 m n) = (term36 m n)) = ((term36 n m) = (term36 m n)).
Proof. exact (MK_COMB (@lem1365530 n m) (@lem1365537 m n)). Qed.
Lemma lem1365541 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem1365511 n m) (@lem1365538 m n)). Qed.
Lemma lem1365543 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365544 (m : nat) (n : nat) : (term40 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (@lem1365543 ((term36 n m) = (term36 m n))). Qed.
Lemma lem1365559 (m : nat) (n : nat) : (term39 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (TRANS (@lem1365541 m n) (@lem1365544 m n)). Qed.
Lemma lem1365560 (m : nat) (n : nat) : (term41 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem1365486 m n) (@lem1365559 m n)). Qed.
Lemma lem1365562 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365563 (m : nat) (n : nat) : (term40 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (@lem1365562 ((term36 n m) = (term36 m n))). Qed.
Lemma lem1365578 (m : nat) (n : nat) : (term41 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (TRANS (@lem1365560 m n) (@lem1365563 m n)). Qed.
Lemma lem1365579 (m : nat) (n : nat) : (term42 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem1365460 m n) (@lem1365578 m n)). Qed.
Lemma lem1365581 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365582 (m : nat) (n : nat) : (term40 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (@lem1365581 ((term36 n m) = (term36 m n))). Qed.
Lemma lem1365597 (m : nat) (n : nat) : (term42 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (TRANS (@lem1365579 m n) (@lem1365582 m n)). Qed.
Lemma lem1365598 (m : nat) (n : nat) : ((term36 n m) = (term36 m n)) = (term42 m n).
Proof. exact (SYM (@lem1365597 m n)). Qed.
Lemma lem1365615 (n : nat) : term43 n.
Proof. exact (@lem9851 (n = (NUMERAL 0))). Qed.
Lemma lem1365616 (n : nat) : (term43 n) = (term44 n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem1365617 (n : nat) : term44 n.
Proof. exact (EQ_MP (@lem1365616 n) (@lem1365615 n)). Qed.
Lemma lem1365618 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem1365619 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem1365636 (m : nat) : (term45 m) = (term45 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem1365637 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term46 m n) = (term47 m).
Proof. exact (MK_COMB (@lem1365636 m) (@lem1365618 n h1)). Qed.
Lemma lem1365638 (m : nat) : (term47 m) = ((term48 m) = (term49 m)).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1365639 (m : nat) (n : nat) : (term50 m n) = (term50 m n).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem1365640 (n : nat) (m : nat) : ((term46 m n) = (term47 m)) = ((term46 m n) = ((term48 m) = (term49 m))).
Proof. exact (MK_COMB (@lem1365639 m n) (@lem1365638 m)). Qed.
Lemma lem1365641 (m : nat) (n : nat) : (term46 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem1365642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365643 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem1365642) (@lem1365641 m n)). Qed.
Lemma lem1365644 (m : nat) : ((term48 m) = (term49 m)) = ((term48 m) = (term49 m)).
Proof. exact (eq_refl ((term48 m) = (term49 m))). Qed.
Lemma lem1365645 (n : nat) (m : nat) : ((term46 m n) = ((term48 m) = (term49 m))) = (((term36 n m) = (term36 m n)) = ((term48 m) = (term49 m))).
Proof. exact (MK_COMB (@lem1365643 m n) (@lem1365644 m)). Qed.
Lemma lem1365646 (n : nat) (m : nat) : ((term46 m n) = (term47 m)) = (((term36 n m) = (term36 m n)) = ((term48 m) = (term49 m))).
Proof. exact (TRANS (@lem1365640 n m) (@lem1365645 n m)). Qed.
Lemma lem1365647 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term36 n m) = (term36 m n)) = ((term48 m) = (term49 m)).
Proof. exact (EQ_MP (@lem1365646 n m) (@lem1365637 m n h1)). Qed.
Lemma lem1365648 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term48 m) = (term49 m)) = ((term36 n m) = (term36 m n)).
Proof. exact (SYM (@lem1365647 m n h1)). Qed.
Lemma lem1365649 (m : nat) : (term45 m) = (term45 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem1365650 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term46 m n) = (term52 m).
Proof. exact (MK_COMB (@lem1365649 m) (@lem1365619 n h1)). Qed.
Lemma lem1365651 (m : nat) : (term52 m) = ((term53 m) = (term54 m)).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem1365652 (m : nat) (n : nat) : (term50 m n) = (term50 m n).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem1365653 (n : nat) (m : nat) : ((term46 m n) = (term52 m)) = ((term46 m n) = ((term53 m) = (term54 m))).
Proof. exact (MK_COMB (@lem1365652 m n) (@lem1365651 m)). Qed.
Lemma lem1365654 (m : nat) (n : nat) : (term46 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem1365655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365656 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem1365655) (@lem1365654 m n)). Qed.
Lemma lem1365657 (m : nat) : ((term53 m) = (term54 m)) = ((term53 m) = (term54 m)).
Proof. exact (eq_refl ((term53 m) = (term54 m))). Qed.
Lemma lem1365658 (n : nat) (m : nat) : ((term46 m n) = ((term53 m) = (term54 m))) = (((term36 n m) = (term36 m n)) = ((term53 m) = (term54 m))).
Proof. exact (MK_COMB (@lem1365656 m n) (@lem1365657 m)). Qed.
Lemma lem1365659 (n : nat) (m : nat) : ((term46 m n) = (term52 m)) = (((term36 n m) = (term36 m n)) = ((term53 m) = (term54 m))).
Proof. exact (TRANS (@lem1365653 n m) (@lem1365658 n m)). Qed.
Lemma lem1365660 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term36 n m) = (term36 m n)) = ((term53 m) = (term54 m)).
Proof. exact (EQ_MP (@lem1365659 n m) (@lem1365650 m n h1)). Qed.
Lemma lem1365661 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term53 m) = (term54 m)) = ((term36 n m) = (term36 m n)).
Proof. exact (SYM (@lem1365660 m n h1)). Qed.
Lemma lem1365665 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365666 (m : nat) : (term55 m) = (m = (NUMERAL 0)).
Proof. exact (@lem1365665 (m = (NUMERAL 0))). Qed.
Lemma lem1365669 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1365670 (m : nat) : (term48 m) = (term56 m).
Proof. exact (MK_COMB (@lem1365669) (@lem1365666 m)). Qed.
Lemma lem1365671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365672 (m : nat) : (term57 m) = (term58 m).
Proof. exact (MK_COMB (@lem1365671) (@lem1365670 m)). Qed.
Lemma lem1365674 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1365675 (m : nat) : (term59 m) = (m = (NUMERAL 0)).
Proof. exact (@lem1365674 (m = (NUMERAL 0))). Qed.
Lemma lem1365678 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1365679 (m : nat) : (term49 m) = (term56 m).
Proof. exact (MK_COMB (@lem1365678) (@lem1365675 m)). Qed.
Lemma lem1365680 (m : nat) : ((term48 m) = (term49 m)) = ((term56 m) = (term56 m)).
Proof. exact (MK_COMB (@lem1365672 m) (@lem1365679 m)). Qed.
Lemma lem1365682 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1365683 (x : Prop) : (x = x) = True.
Proof. exact (@lem1365682 Prop x). Qed.
Lemma lem1365684 (m : nat) : ((term56 m) = (term56 m)) = True.
Proof. exact (@lem1365683 (term56 m)). Qed.
Lemma lem1365685 (m : nat) : ((term48 m) = (term49 m)) = True.
Proof. exact (TRANS (@lem1365680 m) (@lem1365684 m)). Qed.
Lemma lem1365686 (m : nat) : True = ((term48 m) = (term49 m)).
Proof. exact (SYM (@lem1365685 m)). Qed.
Lemma lem1365687 (m : nat) : (term48 m) = (term49 m).
Proof. exact (EQ_MP (@lem1365686 m) (@lem0)). Qed.
Lemma lem1365691 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1365692 (m : nat) : (term60 m) = False.
Proof. exact (@lem1365691 (m = (NUMERAL 0))). Qed.
Lemma lem1365693 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1365694 (m : nat) : (term53 m) = (~ False).
Proof. exact (MK_COMB (@lem1365693) (@lem1365692 m)). Qed.
Lemma lem1365696 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1365697 (m : nat) : (term53 m) = True.
Proof. exact (TRANS (@lem1365694 m) (@lem1365696)). Qed.
Lemma lem1365698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365699 (m : nat) : (term61 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1365698) (@lem1365697 m)). Qed.
Lemma lem1365701 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1365702 (m : nat) : (term62 m) = False.
Proof. exact (@lem1365701 (m = (NUMERAL 0))). Qed.
Lemma lem1365703 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1365704 (m : nat) : (term54 m) = (~ False).
Proof. exact (MK_COMB (@lem1365703) (@lem1365702 m)). Qed.
Lemma lem1365706 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1365707 (m : nat) : (term54 m) = True.
Proof. exact (TRANS (@lem1365704 m) (@lem1365706)). Qed.
Lemma lem1365708 (m : nat) : ((term53 m) = (term54 m)) = (True = True).
Proof. exact (MK_COMB (@lem1365699 m) (@lem1365707 m)). Qed.
Lemma lem1365710 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1365711 : (True = True) = True.
Proof. exact (@lem1365710 True). Qed.
Lemma lem1365712 (m : nat) : ((term53 m) = (term54 m)) = True.
Proof. exact (TRANS (@lem1365708 m) (@lem1365711)). Qed.
Lemma lem1365713 (m : nat) : True = ((term53 m) = (term54 m)).
Proof. exact (SYM (@lem1365712 m)). Qed.
Lemma lem1365714 (m : nat) : (term53 m) = (term54 m).
Proof. exact (EQ_MP (@lem1365713 m) (@lem0)). Qed.
Lemma lem1365715 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term36 n m) = (term36 m n).
Proof. exact (EQ_MP (@lem1365661 m n h1) (@lem1365714 m)). Qed.
Lemma lem1365716 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term36 n m) = (term36 m n).
Proof. exact (EQ_MP (@lem1365648 m n h1) (@lem1365687 m)). Qed.
Lemma lem1365719 (m : nat) (n : nat) : (term36 n m) = (term36 m n).
Proof. exact (or_elim (@lem1365617 n) (fun h0 : (n = (NUMERAL 0)) = True => @lem1365716 m n h0) (fun h0 : (n = (NUMERAL 0)) = False => @lem1365715 m n h0)). Qed.
Lemma lem1365720 (m : nat) (n : nat) : term42 m n.
Proof. exact (EQ_MP (@lem1365598 m n) (@lem1365719 m n)). Qed.

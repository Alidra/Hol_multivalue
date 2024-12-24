Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2405756_term_abbrevs.
Require Import INT_MUL_LNEG_spec.
Require Import INT_MUL_RNEG_spec.
Require Import INT_NEG_NEG_spec.
Require Import INT_OF_NUM_MUL_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2405622 (m : nat) : term0 m.
Proof. exact (@lem2307381 m). Qed.
Lemma lem2405623 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2405624 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2405623 m) (@lem2405622 m)). Qed.
Lemma lem2405625 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2405624 m n). Qed.
Lemma lem2405626 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2405628 (x : int) : term5 x.
Proof. exact (@lem2306663 x). Qed.
Lemma lem2405629 (x : int) : (term5 x) = ((term6 x) = x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2405631 (x : int) : term7 x.
Proof. exact (@lem2306266 x). Qed.
Lemma lem2405632 (x : int) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2405633 (x : int) : term8 x.
Proof. exact (EQ_MP (@lem2405632 x) (@lem2405631 x)). Qed.
Lemma lem2405634 (x : int) (y : int) : term9 x y.
Proof. exact (@lem2405633 x y). Qed.
Lemma lem2405635 (x : int) (y : int) : (term9 x y) = ((term10 x y) = (term11 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem2405637 (x : int) : term12 x.
Proof. exact (@lem2306015 x). Qed.
Lemma lem2405638 (x : int) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2405639 (x : int) : term13 x.
Proof. exact (EQ_MP (@lem2405638 x) (@lem2405637 x)). Qed.
Lemma lem2405640 (x : int) (y : int) : term14 x y.
Proof. exact (@lem2405639 x y). Qed.
Lemma lem2405641 (x : int) (y : int) : (term14 x y) = ((term15 x y) = (term11 x y)).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem2405652 (x : int) (y : int) : (term15 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2405641 x y) (@lem2405640 x y)). Qed.
Lemma lem2405653 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (@lem2405652 (int_of_num m) (term18 n)). Qed.
Lemma lem2405655 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2405635 x y) (@lem2405634 x y)). Qed.
Lemma lem2405656 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (@lem2405655 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2405657 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem2405658 (m : nat) (n : nat) : (term17 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem2405657) (@lem2405656 m n)). Qed.
Lemma lem2405660 (x : int) : (term6 x) = x.
Proof. exact (EQ_MP (@lem2405629 x) (@lem2405628 x)). Qed.
Lemma lem2405661 (m : nat) (n : nat) : (term21 m n) = (term3 m n).
Proof. exact (@lem2405660 (term3 m n)). Qed.
Lemma lem2405662 (m : nat) (n : nat) : (term17 m n) = (term3 m n).
Proof. exact (TRANS (@lem2405658 m n) (@lem2405661 m n)). Qed.
Lemma lem2405663 (m : nat) (n : nat) : (term16 m n) = (term3 m n).
Proof. exact (TRANS (@lem2405653 m n) (@lem2405662 m n)). Qed.
Lemma lem2405664 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405665 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem2405664) (@lem2405663 m n)). Qed.
Lemma lem2405666 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem2405667 (m : nat) (n : nat) : ((term16 m n) = (term4 m n)) = ((term3 m n) = (term4 m n)).
Proof. exact (MK_COMB (@lem2405665 m n) (@lem2405666 m n)). Qed.
Lemma lem2405670 (m : nat) (n : nat) : (term24 m n) = (term24 m n).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem2405671 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (MK_COMB (@lem2405670 m n) (@lem2405667 m n)). Qed.
Lemma lem2405673 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem2405674 (m : nat) (n : nat) : (term26 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (@lem2405673 ((term3 m n) = (term4 m n))). Qed.
Lemma lem2405677 (m : nat) (n : nat) : (term25 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (TRANS (@lem2405671 m n) (@lem2405674 m n)). Qed.
Lemma lem2405678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405679 (m : nat) (n : nat) : (term27 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem2405678) (@lem2405677 m n)). Qed.
Lemma lem2405685 (x : int) (y : int) : (term15 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2405641 x y) (@lem2405640 x y)). Qed.
Lemma lem2405686 (m : nat) (n : nat) : (term28 m n) = (term20 m n).
Proof. exact (@lem2405685 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2405687 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405688 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem2405687) (@lem2405686 m n)). Qed.
Lemma lem2405689 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem2405690 (m : nat) (n : nat) : ((term28 m n) = (term31 m n)) = ((term20 m n) = (term31 m n)).
Proof. exact (MK_COMB (@lem2405688 m n) (@lem2405689 m n)). Qed.
Lemma lem2405693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405694 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (MK_COMB (@lem2405693) (@lem2405690 m n)). Qed.
Lemma lem2405698 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2405635 x y) (@lem2405634 x y)). Qed.
Lemma lem2405699 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (@lem2405698 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2405700 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405701 (m : nat) (n : nat) : (term34 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem2405700) (@lem2405699 m n)). Qed.
Lemma lem2405702 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem2405703 (m : nat) (n : nat) : ((term19 m n) = (term31 m n)) = ((term20 m n) = (term31 m n)).
Proof. exact (MK_COMB (@lem2405701 m n) (@lem2405702 m n)). Qed.
Lemma lem2405706 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem2405694 m n) (@lem2405703 m n)). Qed.
Lemma lem2405708 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem2405709 (m : nat) (n : nat) : (term36 m n) = ((term20 m n) = (term31 m n)).
Proof. exact (@lem2405708 ((term20 m n) = (term31 m n))). Qed.
Lemma lem2405712 (m : nat) (n : nat) : (term35 m n) = ((term20 m n) = (term31 m n)).
Proof. exact (TRANS (@lem2405706 m n) (@lem2405709 m n)). Qed.
Lemma lem2405713 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem2405679 m n) (@lem2405712 m n)). Qed.
Lemma lem2405716 (m : nat) (n : nat) : (term38 m n) = (term37 m n).
Proof. exact (SYM (@lem2405713 m n)). Qed.
Lemma lem2405722 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2405626 m n) (@lem2405625 m n)). Qed.
Lemma lem2405723 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405724 (m : nat) (n : nat) : (term23 m n) = (term39 m n).
Proof. exact (MK_COMB (@lem2405723) (@lem2405722 m n)). Qed.
Lemma lem2405725 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem2405726 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term4 m n) = (term4 m n)).
Proof. exact (MK_COMB (@lem2405724 m n) (@lem2405725 m n)). Qed.
Lemma lem2405728 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405729 (x : int) : (x = x) = True.
Proof. exact (@lem2405728 int x). Qed.
Lemma lem2405730 (m : nat) (n : nat) : ((term4 m n) = (term4 m n)) = True.
Proof. exact (@lem2405729 (term4 m n)). Qed.
Lemma lem2405731 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = True.
Proof. exact (TRANS (@lem2405726 m n) (@lem2405730 m n)). Qed.
Lemma lem2405732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405733 (m : nat) (n : nat) : (term24 m n) = (and True).
Proof. exact (MK_COMB (@lem2405732) (@lem2405731 m n)). Qed.
Lemma lem2405737 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2405626 m n) (@lem2405625 m n)). Qed.
Lemma lem2405738 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem2405739 (m : nat) (n : nat) : (term20 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem2405738) (@lem2405737 m n)). Qed.
Lemma lem2405740 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405741 (m : nat) (n : nat) : (term30 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem2405740) (@lem2405739 m n)). Qed.
Lemma lem2405742 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem2405743 (m : nat) (n : nat) : ((term20 m n) = (term31 m n)) = ((term31 m n) = (term31 m n)).
Proof. exact (MK_COMB (@lem2405741 m n) (@lem2405742 m n)). Qed.
Lemma lem2405745 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405746 (x : int) : (x = x) = True.
Proof. exact (@lem2405745 int x). Qed.
Lemma lem2405747 (m : nat) (n : nat) : ((term31 m n) = (term31 m n)) = True.
Proof. exact (@lem2405746 (term31 m n)). Qed.
Lemma lem2405748 (m : nat) (n : nat) : ((term20 m n) = (term31 m n)) = True.
Proof. exact (TRANS (@lem2405743 m n) (@lem2405747 m n)). Qed.
Lemma lem2405749 (m : nat) (n : nat) : (term38 m n) = (True /\ True).
Proof. exact (MK_COMB (@lem2405733 m n) (@lem2405748 m n)). Qed.
Lemma lem2405751 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2405752 : (True /\ True) = True.
Proof. exact (@lem2405751 True). Qed.
Lemma lem2405753 (m : nat) (n : nat) : (term38 m n) = True.
Proof. exact (TRANS (@lem2405749 m n) (@lem2405752)). Qed.
Lemma lem2405754 (m : nat) (n : nat) : True = (term38 m n).
Proof. exact (SYM (@lem2405753 m n)). Qed.
Lemma lem2405755 (m : nat) (n : nat) : term38 m n.
Proof. exact (EQ_MP (@lem2405754 m n) (@lem0)). Qed.
Lemma lem2405756 (m : nat) (n : nat) : term37 m n.
Proof. exact (EQ_MP (@lem2405716 m n) (@lem2405755 m n)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_ADD_term_abbrevs.
Require Import REAL_LT_ADD_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2303652 (x : int) : term0 x.
Proof. exact (@lem1382497 (real_of_int x)). Qed.
Lemma lem2303653 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303654 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303653 x) (@lem2303652 x)). Qed.
Lemma lem2303655 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303654 x (real_of_int y)). Qed.
Lemma lem2303656 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303657 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303656 x y) (@lem2303655 x y)). Qed.
Lemma lem2303659 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303660 : term5 = term6.
Proof. exact (@lem2303659 (NUMERAL 0)). Qed.
Lemma lem2303661 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303662 : term7 = term8.
Proof. exact (MK_COMB (@lem2303661) (@lem2303660)). Qed.
Lemma lem2303663 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2303664 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2303662) (@lem2303663 x)). Qed.
Lemma lem2303666 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303667 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2303666 term13 x). Qed.
Lemma lem2303668 (x : int) : (term9 x) = (term12 x).
Proof. exact (TRANS (@lem2303664 x) (@lem2303667 x)). Qed.
Lemma lem2303669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2303670 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2303669) (@lem2303668 x)). Qed.
Lemma lem2303672 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303673 : term5 = term6.
Proof. exact (@lem2303672 (NUMERAL 0)). Qed.
Lemma lem2303674 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303675 : term7 = term8.
Proof. exact (MK_COMB (@lem2303674) (@lem2303673)). Qed.
Lemma lem2303676 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2303677 (y : int) : (term9 y) = (term10 y).
Proof. exact (MK_COMB (@lem2303675) (@lem2303676 y)). Qed.
Lemma lem2303679 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303680 (y : int) : (term10 y) = (term12 y).
Proof. exact (@lem2303679 term13 y). Qed.
Lemma lem2303681 (y : int) : (term9 y) = (term12 y).
Proof. exact (TRANS (@lem2303677 y) (@lem2303680 y)). Qed.
Lemma lem2303682 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2303670 x) (@lem2303681 y)). Qed.
Lemma lem2303683 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2303684 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem2303683) (@lem2303682 x y)). Qed.
Lemma lem2303686 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303687 : term5 = term6.
Proof. exact (@lem2303686 (NUMERAL 0)). Qed.
Lemma lem2303688 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303689 : term7 = term8.
Proof. exact (MK_COMB (@lem2303688) (@lem2303687)). Qed.
Lemma lem2303691 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303692 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem2303689) (@lem2303691 x y)). Qed.
Lemma lem2303694 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303695 (x : int) (y : int) : (term23 x y) = (term24 x y).
Proof. exact (@lem2303694 term13 (int_add x y)). Qed.
Lemma lem2303696 (x : int) (y : int) : (term22 x y) = (term24 x y).
Proof. exact (TRANS (@lem2303692 x y) (@lem2303695 x y)). Qed.
Lemma lem2303697 (x : int) (y : int) : (term3 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem2303684 x y) (@lem2303696 x y)). Qed.
Lemma lem2303698 (x : int) (y : int) : term25 x y.
Proof. exact (EQ_MP (@lem2303697 x y) (@lem2303657 x y)). Qed.
Lemma lem2303699 (x : int) : term26 x.
Proof. exact (fun y : int => @lem2303698 x y). Qed.
Lemma lem2303700 : term27.
Proof. exact (fun x : int => @lem2303699 x). Qed.

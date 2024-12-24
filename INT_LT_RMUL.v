Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_RMUL_term_abbrevs.
Require Import REAL_LT_RMUL_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304779 (x : int) : term0 x.
Proof. exact (@lem1585785 (real_of_int x)). Qed.
Lemma lem2304780 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304781 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304780 x) (@lem2304779 x)). Qed.
Lemma lem2304782 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304781 x (real_of_int y)). Qed.
Lemma lem2304783 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304784 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304783 x y) (@lem2304782 x y)). Qed.
Lemma lem2304785 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2304784 x y (real_of_int z)). Qed.
Lemma lem2304786 (x : int) (y : int) (z : int) : (term4 x y z) = (term5 x y z).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2304787 (x : int) (y : int) (z : int) : term5 x y z.
Proof. exact (EQ_MP (@lem2304786 x y z) (@lem2304785 x y z)). Qed.
Lemma lem2304789 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2304791 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2304790) (@lem2304789 x y)). Qed.
Lemma lem2304793 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304794 : term10 = term11.
Proof. exact (@lem2304793 (NUMERAL 0)). Qed.
Lemma lem2304795 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304796 : term12 = term13.
Proof. exact (MK_COMB (@lem2304795) (@lem2304794)). Qed.
Lemma lem2304797 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2304798 (z : int) : (term14 z) = (term15 z).
Proof. exact (MK_COMB (@lem2304796) (@lem2304797 z)). Qed.
Lemma lem2304800 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304801 (z : int) : (term15 z) = (term16 z).
Proof. exact (@lem2304800 term17 z). Qed.
Lemma lem2304802 (z : int) : (term14 z) = (term16 z).
Proof. exact (TRANS (@lem2304798 z) (@lem2304801 z)). Qed.
Lemma lem2304803 (x : int) (y : int) (z : int) : (term18 x y z) = (term19 x y z).
Proof. exact (MK_COMB (@lem2304791 x y) (@lem2304802 z)). Qed.
Lemma lem2304804 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304805 (x : int) (y : int) (z : int) : (term20 x y z) = (term21 x y z).
Proof. exact (MK_COMB (@lem2304804) (@lem2304803 x y z)). Qed.
Lemma lem2304807 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304808 (x : int) (z : int) : (term22 x z) = (term23 x z).
Proof. exact (@lem2304807 x z). Qed.
Lemma lem2304809 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304810 (x : int) (z : int) : (term24 x z) = (term25 x z).
Proof. exact (MK_COMB (@lem2304809) (@lem2304808 x z)). Qed.
Lemma lem2304812 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304813 (y : int) (z : int) : (term22 y z) = (term23 y z).
Proof. exact (@lem2304812 y z). Qed.
Lemma lem2304814 (x : int) (y : int) (z : int) : (term26 x y z) = (term27 x y z).
Proof. exact (MK_COMB (@lem2304810 x z) (@lem2304813 y z)). Qed.
Lemma lem2304816 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304817 (x : int) (y : int) (z : int) : (term27 x y z) = (term28 x y z).
Proof. exact (@lem2304816 (int_mul x z) (int_mul y z)). Qed.
Lemma lem2304818 (x : int) (y : int) (z : int) : (term26 x y z) = (term28 x y z).
Proof. exact (TRANS (@lem2304814 x y z) (@lem2304817 x y z)). Qed.
Lemma lem2304819 (x : int) (y : int) (z : int) : (term5 x y z) = (term29 x y z).
Proof. exact (MK_COMB (@lem2304805 x y z) (@lem2304818 x y z)). Qed.
Lemma lem2304820 (x : int) (y : int) (z : int) : term29 x y z.
Proof. exact (EQ_MP (@lem2304819 x y z) (@lem2304787 x y z)). Qed.
Lemma lem2304821 (x : int) (y : int) : term30 x y.
Proof. exact (fun z : int => @lem2304820 x y z). Qed.
Lemma lem2304822 (x : int) : term31 x.
Proof. exact (fun y : int => @lem2304821 x y). Qed.
Lemma lem2304823 : term32.
Proof. exact (fun x : int => @lem2304822 x). Qed.

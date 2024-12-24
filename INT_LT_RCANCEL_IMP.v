Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_RCANCEL_IMP_term_abbrevs.
Require Import REAL_LT_RCANCEL_IMP_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304724 (x : int) : term0 x.
Proof. exact (@lem1598629 (real_of_int x)). Qed.
Lemma lem2304725 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304726 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304725 x) (@lem2304724 x)). Qed.
Lemma lem2304727 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304726 x (real_of_int y)). Qed.
Lemma lem2304728 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304729 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304728 x y) (@lem2304727 x y)). Qed.
Lemma lem2304730 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2304729 x y (real_of_int z)). Qed.
Lemma lem2304731 (z : int) (x : int) (y : int) : (term4 x y z) = (term5 z x y).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2304732 (z : int) (x : int) (y : int) : term5 z x y.
Proof. exact (EQ_MP (@lem2304731 z x y) (@lem2304730 x y z)). Qed.
Lemma lem2304734 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304735 : term7 = term8.
Proof. exact (@lem2304734 (NUMERAL 0)). Qed.
Lemma lem2304736 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304737 : term9 = term10.
Proof. exact (MK_COMB (@lem2304736) (@lem2304735)). Qed.
Lemma lem2304738 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2304739 (z : int) : (term11 z) = (term12 z).
Proof. exact (MK_COMB (@lem2304737) (@lem2304738 z)). Qed.
Lemma lem2304741 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304742 (z : int) : (term12 z) = (term14 z).
Proof. exact (@lem2304741 term15 z). Qed.
Lemma lem2304743 (z : int) : (term11 z) = (term14 z).
Proof. exact (TRANS (@lem2304739 z) (@lem2304742 z)). Qed.
Lemma lem2304744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2304745 (z : int) : (term16 z) = (term17 z).
Proof. exact (MK_COMB (@lem2304744) (@lem2304743 z)). Qed.
Lemma lem2304747 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304748 (x : int) (z : int) : (term18 x z) = (term19 x z).
Proof. exact (@lem2304747 x z). Qed.
Lemma lem2304749 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304750 (x : int) (z : int) : (term20 x z) = (term21 x z).
Proof. exact (MK_COMB (@lem2304749) (@lem2304748 x z)). Qed.
Lemma lem2304752 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304753 (y : int) (z : int) : (term18 y z) = (term19 y z).
Proof. exact (@lem2304752 y z). Qed.
Lemma lem2304754 (x : int) (y : int) (z : int) : (term22 x y z) = (term23 x y z).
Proof. exact (MK_COMB (@lem2304750 x z) (@lem2304753 y z)). Qed.
Lemma lem2304756 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304757 (x : int) (y : int) (z : int) : (term23 x y z) = (term24 x y z).
Proof. exact (@lem2304756 (int_mul x z) (int_mul y z)). Qed.
Lemma lem2304758 (x : int) (y : int) (z : int) : (term22 x y z) = (term24 x y z).
Proof. exact (TRANS (@lem2304754 x y z) (@lem2304757 x y z)). Qed.
Lemma lem2304759 (x : int) (y : int) (z : int) : (term25 x y z) = (term26 x y z).
Proof. exact (MK_COMB (@lem2304745 z) (@lem2304758 x y z)). Qed.
Lemma lem2304760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304761 (x : int) (y : int) (z : int) : (term27 x y z) = (term28 x y z).
Proof. exact (MK_COMB (@lem2304760) (@lem2304759 x y z)). Qed.
Lemma lem2304763 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304764 (z : int) (x : int) (y : int) : (term5 z x y) = (term29 z x y).
Proof. exact (MK_COMB (@lem2304761 x y z) (@lem2304763 x y)). Qed.
Lemma lem2304765 (z : int) (x : int) (y : int) : term29 z x y.
Proof. exact (EQ_MP (@lem2304764 z x y) (@lem2304732 z x y)). Qed.
Lemma lem2304766 (x : int) (y : int) : term30 x y.
Proof. exact (fun z : int => @lem2304765 z x y). Qed.
Lemma lem2304767 (x : int) : term31 x.
Proof. exact (fun y : int => @lem2304766 x y). Qed.
Lemma lem2304768 : term32.
Proof. exact (fun x : int => @lem2304767 x). Qed.

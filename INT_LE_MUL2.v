Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_MUL2_term_abbrevs.
Require Import REAL_LE_MUL2_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302747 (w : int) : term0 w.
Proof. exact (@lem1630540 (real_of_int w)). Qed.
Lemma lem2302748 (w : int) : (term0 w) = (term1 w).
Proof. exact (eq_refl (term0 w)). Qed.
Lemma lem2302749 (w : int) : term1 w.
Proof. exact (EQ_MP (@lem2302748 w) (@lem2302747 w)). Qed.
Lemma lem2302750 (w : int) (x : int) : term2 w x.
Proof. exact (@lem2302749 w (real_of_int x)). Qed.
Lemma lem2302751 (w : int) (x : int) : (term2 w x) = (term3 w x).
Proof. exact (eq_refl (term2 w x)). Qed.
Lemma lem2302752 (w : int) (x : int) : term3 w x.
Proof. exact (EQ_MP (@lem2302751 w x) (@lem2302750 w x)). Qed.
Lemma lem2302753 (w : int) (x : int) (y : int) : term4 w x y.
Proof. exact (@lem2302752 w x (real_of_int y)). Qed.
Lemma lem2302754 (w : int) (y : int) (x : int) : (term4 w x y) = (term5 w y x).
Proof. exact (eq_refl (term4 w x y)). Qed.
Lemma lem2302755 (w : int) (y : int) (x : int) : term5 w y x.
Proof. exact (EQ_MP (@lem2302754 w y x) (@lem2302753 w x y)). Qed.
Lemma lem2302756 (w : int) (y : int) (x : int) (z : int) : term6 w y x z.
Proof. exact (@lem2302755 w y x (real_of_int z)). Qed.
Lemma lem2302757 (w : int) (y : int) (x : int) (z : int) : (term6 w y x z) = (term7 w y x z).
Proof. exact (eq_refl (term6 w y x z)). Qed.
Lemma lem2302758 (w : int) (y : int) (x : int) (z : int) : term7 w y x z.
Proof. exact (EQ_MP (@lem2302757 w y x z) (@lem2302756 w y x z)). Qed.
Lemma lem2302760 (n : nat) : (real_of_num n) = (term8 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302761 : term9 = term10.
Proof. exact (@lem2302760 (NUMERAL 0)). Qed.
Lemma lem2302762 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302763 : term11 = term12.
Proof. exact (MK_COMB (@lem2302762) (@lem2302761)). Qed.
Lemma lem2302764 (w : int) : (real_of_int w) = (real_of_int w).
Proof. exact (eq_refl (real_of_int w)). Qed.
Lemma lem2302765 (w : int) : (term13 w) = (term14 w).
Proof. exact (MK_COMB (@lem2302763) (@lem2302764 w)). Qed.
Lemma lem2302767 (x : int) (y : int) : (term15 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302768 (w : int) : (term14 w) = (term16 w).
Proof. exact (@lem2302767 term17 w). Qed.
Lemma lem2302769 (w : int) : (term13 w) = (term16 w).
Proof. exact (TRANS (@lem2302765 w) (@lem2302768 w)). Qed.
Lemma lem2302770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302771 (w : int) : (term18 w) = (term19 w).
Proof. exact (MK_COMB (@lem2302770) (@lem2302769 w)). Qed.
Lemma lem2302773 (x : int) (y : int) : (term15 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302774 (w : int) (x : int) : (term15 w x) = (int_le w x).
Proof. exact (@lem2302773 w x). Qed.
Lemma lem2302775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302776 (w : int) (x : int) : (term20 w x) = (term21 w x).
Proof. exact (MK_COMB (@lem2302775) (@lem2302774 w x)). Qed.
Lemma lem2302778 (n : nat) : (real_of_num n) = (term8 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302779 : term9 = term10.
Proof. exact (@lem2302778 (NUMERAL 0)). Qed.
Lemma lem2302780 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302781 : term11 = term12.
Proof. exact (MK_COMB (@lem2302780) (@lem2302779)). Qed.
Lemma lem2302782 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2302783 (y : int) : (term13 y) = (term14 y).
Proof. exact (MK_COMB (@lem2302781) (@lem2302782 y)). Qed.
Lemma lem2302785 (x : int) (y : int) : (term15 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302786 (y : int) : (term14 y) = (term16 y).
Proof. exact (@lem2302785 term17 y). Qed.
Lemma lem2302787 (y : int) : (term13 y) = (term16 y).
Proof. exact (TRANS (@lem2302783 y) (@lem2302786 y)). Qed.
Lemma lem2302788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302789 (y : int) : (term18 y) = (term19 y).
Proof. exact (MK_COMB (@lem2302788) (@lem2302787 y)). Qed.
Lemma lem2302791 (x : int) (y : int) : (term15 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302792 (y : int) (z : int) : (term15 y z) = (int_le y z).
Proof. exact (@lem2302791 y z). Qed.
Lemma lem2302793 (y : int) (z : int) : (term22 y z) = (term23 y z).
Proof. exact (MK_COMB (@lem2302789 y) (@lem2302792 y z)). Qed.
Lemma lem2302794 (w : int) (x : int) (y : int) (z : int) : (term24 w x y z) = (term25 w x y z).
Proof. exact (MK_COMB (@lem2302776 w x) (@lem2302793 y z)). Qed.
Lemma lem2302795 (w : int) (x : int) (y : int) (z : int) : (term26 w x y z) = (term27 w x y z).
Proof. exact (MK_COMB (@lem2302771 w) (@lem2302794 w x y z)). Qed.
Lemma lem2302796 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302797 (w : int) (x : int) (y : int) (z : int) : (term28 w x y z) = (term29 w x y z).
Proof. exact (MK_COMB (@lem2302796) (@lem2302795 w x y z)). Qed.
Lemma lem2302799 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2302800 (w : int) (y : int) : (term30 w y) = (term31 w y).
Proof. exact (@lem2302799 w y). Qed.
Lemma lem2302801 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302802 (w : int) (y : int) : (term32 w y) = (term33 w y).
Proof. exact (MK_COMB (@lem2302801) (@lem2302800 w y)). Qed.
Lemma lem2302804 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2302805 (x : int) (z : int) : (term30 x z) = (term31 x z).
Proof. exact (@lem2302804 x z). Qed.
Lemma lem2302806 (w : int) (y : int) (x : int) (z : int) : (term34 w y x z) = (term35 w y x z).
Proof. exact (MK_COMB (@lem2302802 w y) (@lem2302805 x z)). Qed.
Lemma lem2302808 (x : int) (y : int) : (term15 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302809 (w : int) (y : int) (x : int) (z : int) : (term35 w y x z) = (term36 w y x z).
Proof. exact (@lem2302808 (int_mul w y) (int_mul x z)). Qed.
Lemma lem2302810 (w : int) (y : int) (x : int) (z : int) : (term34 w y x z) = (term36 w y x z).
Proof. exact (TRANS (@lem2302806 w y x z) (@lem2302809 w y x z)). Qed.
Lemma lem2302811 (w : int) (y : int) (x : int) (z : int) : (term7 w y x z) = (term37 w y x z).
Proof. exact (MK_COMB (@lem2302797 w x y z) (@lem2302810 w y x z)). Qed.
Lemma lem2302812 (w : int) (y : int) (x : int) (z : int) : term37 w y x z.
Proof. exact (EQ_MP (@lem2302811 w y x z) (@lem2302758 w y x z)). Qed.
Lemma lem2302813 (w : int) (y : int) (x : int) : term38 w y x.
Proof. exact (fun z : int => @lem2302812 w y x z). Qed.
Lemma lem2302814 (w : int) (x : int) : term39 w x.
Proof. exact (fun y : int => @lem2302813 w y x). Qed.
Lemma lem2302815 (w : int) : term40 w.
Proof. exact (fun x : int => @lem2302814 w x). Qed.
Lemma lem2302816 : term41.
Proof. exact (fun w : int => @lem2302815 w). Qed.

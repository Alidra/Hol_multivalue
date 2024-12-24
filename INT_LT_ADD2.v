Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_ADD2_term_abbrevs.
Require Import REAL_LT_ADD2_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2303730 (w : int) : term0 w.
Proof. exact (@lem1501615 (real_of_int w)). Qed.
Lemma lem2303731 (w : int) : (term0 w) = (term1 w).
Proof. exact (eq_refl (term0 w)). Qed.
Lemma lem2303732 (w : int) : term1 w.
Proof. exact (EQ_MP (@lem2303731 w) (@lem2303730 w)). Qed.
Lemma lem2303733 (w : int) (x : int) : term2 w x.
Proof. exact (@lem2303732 w (real_of_int x)). Qed.
Lemma lem2303734 (w : int) (x : int) : (term2 w x) = (term3 w x).
Proof. exact (eq_refl (term2 w x)). Qed.
Lemma lem2303735 (w : int) (x : int) : term3 w x.
Proof. exact (EQ_MP (@lem2303734 w x) (@lem2303733 w x)). Qed.
Lemma lem2303736 (w : int) (x : int) (y : int) : term4 w x y.
Proof. exact (@lem2303735 w x (real_of_int y)). Qed.
Lemma lem2303737 (w : int) (y : int) (x : int) : (term4 w x y) = (term5 w y x).
Proof. exact (eq_refl (term4 w x y)). Qed.
Lemma lem2303738 (w : int) (y : int) (x : int) : term5 w y x.
Proof. exact (EQ_MP (@lem2303737 w y x) (@lem2303736 w x y)). Qed.
Lemma lem2303739 (w : int) (y : int) (x : int) (z : int) : term6 w y x z.
Proof. exact (@lem2303738 w y x (real_of_int z)). Qed.
Lemma lem2303740 (w : int) (y : int) (x : int) (z : int) : (term6 w y x z) = (term7 w y x z).
Proof. exact (eq_refl (term6 w y x z)). Qed.
Lemma lem2303741 (w : int) (y : int) (x : int) (z : int) : term7 w y x z.
Proof. exact (EQ_MP (@lem2303740 w y x z) (@lem2303739 w y x z)). Qed.
Lemma lem2303743 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303744 (w : int) (x : int) : (term8 w x) = (int_lt w x).
Proof. exact (@lem2303743 w x). Qed.
Lemma lem2303745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2303746 (w : int) (x : int) : (term9 w x) = (term10 w x).
Proof. exact (MK_COMB (@lem2303745) (@lem2303744 w x)). Qed.
Lemma lem2303748 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303749 (y : int) (z : int) : (term8 y z) = (int_lt y z).
Proof. exact (@lem2303748 y z). Qed.
Lemma lem2303750 (w : int) (x : int) (y : int) (z : int) : (term11 w x y z) = (term12 w x y z).
Proof. exact (MK_COMB (@lem2303746 w x) (@lem2303749 y z)). Qed.
Lemma lem2303751 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2303752 (w : int) (x : int) (y : int) (z : int) : (term13 w x y z) = (term14 w x y z).
Proof. exact (MK_COMB (@lem2303751) (@lem2303750 w x y z)). Qed.
Lemma lem2303754 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303755 (w : int) (y : int) : (term15 w y) = (term16 w y).
Proof. exact (@lem2303754 w y). Qed.
Lemma lem2303756 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303757 (w : int) (y : int) : (term17 w y) = (term18 w y).
Proof. exact (MK_COMB (@lem2303756) (@lem2303755 w y)). Qed.
Lemma lem2303759 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303760 (x : int) (z : int) : (term15 x z) = (term16 x z).
Proof. exact (@lem2303759 x z). Qed.
Lemma lem2303761 (w : int) (y : int) (x : int) (z : int) : (term19 w y x z) = (term20 w y x z).
Proof. exact (MK_COMB (@lem2303757 w y) (@lem2303760 x z)). Qed.
Lemma lem2303763 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303764 (w : int) (y : int) (x : int) (z : int) : (term20 w y x z) = (term21 w y x z).
Proof. exact (@lem2303763 (int_add w y) (int_add x z)). Qed.
Lemma lem2303765 (w : int) (y : int) (x : int) (z : int) : (term19 w y x z) = (term21 w y x z).
Proof. exact (TRANS (@lem2303761 w y x z) (@lem2303764 w y x z)). Qed.
Lemma lem2303766 (w : int) (y : int) (x : int) (z : int) : (term7 w y x z) = (term22 w y x z).
Proof. exact (MK_COMB (@lem2303752 w x y z) (@lem2303765 w y x z)). Qed.
Lemma lem2303767 (w : int) (y : int) (x : int) (z : int) : term22 w y x z.
Proof. exact (EQ_MP (@lem2303766 w y x z) (@lem2303741 w y x z)). Qed.
Lemma lem2303768 (w : int) (y : int) (x : int) : term23 w y x.
Proof. exact (fun z : int => @lem2303767 w y x z). Qed.
Lemma lem2303769 (w : int) (x : int) : term24 w x.
Proof. exact (fun y : int => @lem2303768 w y x). Qed.
Lemma lem2303770 (w : int) : term25 w.
Proof. exact (fun x : int => @lem2303769 w x). Qed.
Lemma lem2303771 : term26.
Proof. exact (fun w : int => @lem2303770 w). Qed.

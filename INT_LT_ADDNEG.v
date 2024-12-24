Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_ADDNEG_term_abbrevs.
Require Import REAL_LT_ADDNEG_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2303803 (x : int) : term0 x.
Proof. exact (@lem1503294 (real_of_int x)). Qed.
Lemma lem2303804 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303805 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303804 x) (@lem2303803 x)). Qed.
Lemma lem2303806 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303805 x (real_of_int y)). Qed.
Lemma lem2303807 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303808 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2303807 y x) (@lem2303806 x y)). Qed.
Lemma lem2303809 (y : int) (x : int) (z : int) : term4 y x z.
Proof. exact (@lem2303808 y x (real_of_int z)). Qed.
Lemma lem2303810 (y : int) (z : int) (x : int) : (term4 y x z) = ((term5 y x z) = (term6 y z x)).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem2303811 (y : int) (z : int) (x : int) : (term5 y x z) = (term6 y z x).
Proof. exact (EQ_MP (@lem2303810 y z x) (@lem2303809 y x z)). Qed.
Lemma lem2303813 (x : int) : (term7 x) = (term8 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2303814 (z : int) : (term7 z) = (term8 z).
Proof. exact (@lem2303813 z). Qed.
Lemma lem2303815 (x : int) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2303816 (x : int) (z : int) : (term10 x z) = (term11 x z).
Proof. exact (MK_COMB (@lem2303815 x) (@lem2303814 z)). Qed.
Lemma lem2303818 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303819 (x : int) (z : int) : (term11 x z) = (term14 x z).
Proof. exact (@lem2303818 x (int_neg z)). Qed.
Lemma lem2303820 (x : int) (z : int) : (term10 x z) = (term14 x z).
Proof. exact (TRANS (@lem2303816 x z) (@lem2303819 x z)). Qed.
Lemma lem2303821 (y : int) : (term15 y) = (term15 y).
Proof. exact (eq_refl (term15 y)). Qed.
Lemma lem2303822 (y : int) (x : int) (z : int) : (term5 y x z) = (term16 y x z).
Proof. exact (MK_COMB (@lem2303821 y) (@lem2303820 x z)). Qed.
Lemma lem2303824 (x : int) (y : int) : (term17 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303825 (y : int) (x : int) (z : int) : (term16 y x z) = (term18 y x z).
Proof. exact (@lem2303824 y (term19 x z)). Qed.
Lemma lem2303826 (y : int) (x : int) (z : int) : (term5 y x z) = (term18 y x z).
Proof. exact (TRANS (@lem2303822 y x z) (@lem2303825 y x z)). Qed.
Lemma lem2303827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303828 (y : int) (x : int) (z : int) : (term20 y x z) = (term21 y x z).
Proof. exact (MK_COMB (@lem2303827) (@lem2303826 y x z)). Qed.
Lemma lem2303830 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303831 (y : int) (z : int) : (term12 y z) = (term13 y z).
Proof. exact (@lem2303830 y z). Qed.
Lemma lem2303832 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303833 (y : int) (z : int) : (term22 y z) = (term23 y z).
Proof. exact (MK_COMB (@lem2303832) (@lem2303831 y z)). Qed.
Lemma lem2303834 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2303835 (y : int) (z : int) (x : int) : (term6 y z x) = (term24 y z x).
Proof. exact (MK_COMB (@lem2303833 y z) (@lem2303834 x)). Qed.
Lemma lem2303837 (x : int) (y : int) : (term17 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303838 (y : int) (z : int) (x : int) : (term24 y z x) = (term25 y z x).
Proof. exact (@lem2303837 (int_add y z) x). Qed.
Lemma lem2303839 (y : int) (z : int) (x : int) : (term6 y z x) = (term25 y z x).
Proof. exact (TRANS (@lem2303835 y z x) (@lem2303838 y z x)). Qed.
Lemma lem2303840 (y : int) (z : int) (x : int) : ((term5 y x z) = (term6 y z x)) = ((term18 y x z) = (term25 y z x)).
Proof. exact (MK_COMB (@lem2303828 y x z) (@lem2303839 y z x)). Qed.
Lemma lem2303841 (y : int) (z : int) (x : int) : (term18 y x z) = (term25 y z x).
Proof. exact (EQ_MP (@lem2303840 y z x) (@lem2303811 y z x)). Qed.
Lemma lem2303842 (y : int) (x : int) : term26 y x.
Proof. exact (fun z : int => @lem2303841 y z x). Qed.
Lemma lem2303843 (x : int) : term27 x.
Proof. exact (fun y : int => @lem2303842 y x). Qed.
Lemma lem2303844 : term28.
Proof. exact (fun x : int => @lem2303843 x). Qed.

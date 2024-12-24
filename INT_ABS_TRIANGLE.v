Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_TRIANGLE_term_abbrevs.
Require Import REAL_ABS_TRIANGLE_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2300808 (x : int) : term0 x.
Proof. exact (@lem1529646 (real_of_int x)). Qed.
Lemma lem2300809 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300810 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300809 x) (@lem2300808 x)). Qed.
Lemma lem2300811 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2300810 x (real_of_int y)). Qed.
Lemma lem2300812 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2300813 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2300812 x y) (@lem2300811 x y)). Qed.
Lemma lem2300815 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300816 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300817 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2300816) (@lem2300815 x y)). Qed.
Lemma lem2300819 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300820 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (@lem2300819 (int_add x y)). Qed.
Lemma lem2300821 (x : int) (y : int) : (term6 x y) = (term10 x y).
Proof. exact (TRANS (@lem2300817 x y) (@lem2300820 x y)). Qed.
Lemma lem2300822 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2300823 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2300822) (@lem2300821 x y)). Qed.
Lemma lem2300825 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300826 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2300827 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2300826) (@lem2300825 x)). Qed.
Lemma lem2300829 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300830 (y : int) : (term8 y) = (term9 y).
Proof. exact (@lem2300829 y). Qed.
Lemma lem2300831 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2300827 x) (@lem2300830 y)). Qed.
Lemma lem2300833 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300834 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (@lem2300833 (int_abs x) (int_abs y)). Qed.
Lemma lem2300835 (x : int) (y : int) : (term15 x y) = (term17 x y).
Proof. exact (TRANS (@lem2300831 x y) (@lem2300834 x y)). Qed.
Lemma lem2300836 (x : int) (y : int) : (term3 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem2300823 x y) (@lem2300835 x y)). Qed.
Lemma lem2300838 (x : int) (y : int) : (term19 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2300839 (x : int) (y : int) : (term18 x y) = (term20 x y).
Proof. exact (@lem2300838 (term21 x y) (term22 x y)). Qed.
Lemma lem2300840 (x : int) (y : int) : (term3 x y) = (term20 x y).
Proof. exact (TRANS (@lem2300836 x y) (@lem2300839 x y)). Qed.
Lemma lem2300841 (x : int) (y : int) : term20 x y.
Proof. exact (EQ_MP (@lem2300840 x y) (@lem2300813 x y)). Qed.
Lemma lem2300842 (x : int) : term23 x.
Proof. exact (fun y : int => @lem2300841 x y). Qed.
Lemma lem2300843 : term24.
Proof. exact (fun x : int => @lem2300842 x). Qed.

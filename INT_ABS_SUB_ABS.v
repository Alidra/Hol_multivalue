Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_SUB_ABS_term_abbrevs.
Require Import REAL_ABS_SUB_ABS_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2300766 (x : int) : term0 x.
Proof. exact (@lem1547976 (real_of_int x)). Qed.
Lemma lem2300767 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300768 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300767 x) (@lem2300766 x)). Qed.
Lemma lem2300769 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2300768 x (real_of_int y)). Qed.
Lemma lem2300770 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2300771 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2300770 x y) (@lem2300769 x y)). Qed.
Lemma lem2300773 (x : int) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300774 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2300775 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2300774) (@lem2300773 x)). Qed.
Lemma lem2300777 (x : int) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300778 (y : int) : (term4 y) = (term5 y).
Proof. exact (@lem2300777 y). Qed.
Lemma lem2300779 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2300775 x) (@lem2300778 y)). Qed.
Lemma lem2300781 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300782 (x : int) (y : int) : (term9 x y) = (term12 x y).
Proof. exact (@lem2300781 (int_abs x) (int_abs y)). Qed.
Lemma lem2300783 (x : int) (y : int) : (term8 x y) = (term12 x y).
Proof. exact (TRANS (@lem2300779 x y) (@lem2300782 x y)). Qed.
Lemma lem2300784 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300785 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem2300784) (@lem2300783 x y)). Qed.
Lemma lem2300787 (x : int) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300788 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (@lem2300787 (term16 x y)). Qed.
Lemma lem2300789 (x : int) (y : int) : (term13 x y) = (term15 x y).
Proof. exact (TRANS (@lem2300785 x y) (@lem2300788 x y)). Qed.
Lemma lem2300790 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2300791 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem2300790) (@lem2300789 x y)). Qed.
Lemma lem2300793 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300794 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300795 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem2300794) (@lem2300793 x y)). Qed.
Lemma lem2300797 (x : int) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300798 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (@lem2300797 (int_sub x y)). Qed.
Lemma lem2300799 (x : int) (y : int) : (term19 x y) = (term21 x y).
Proof. exact (TRANS (@lem2300795 x y) (@lem2300798 x y)). Qed.
Lemma lem2300800 (x : int) (y : int) : (term3 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem2300791 x y) (@lem2300799 x y)). Qed.
Lemma lem2300802 (x : int) (y : int) : (term23 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2300803 (x : int) (y : int) : (term22 x y) = (term24 x y).
Proof. exact (@lem2300802 (term25 x y) (term26 x y)). Qed.
Lemma lem2300804 (x : int) (y : int) : (term3 x y) = (term24 x y).
Proof. exact (TRANS (@lem2300800 x y) (@lem2300803 x y)). Qed.
Lemma lem2300805 (x : int) (y : int) : term24 x y.
Proof. exact (EQ_MP (@lem2300804 x y) (@lem2300771 x y)). Qed.
Lemma lem2300806 (x : int) : term27 x.
Proof. exact (fun y : int => @lem2300805 x y). Qed.
Lemma lem2300807 : term28.
Proof. exact (fun x : int => @lem2300806 x). Qed.

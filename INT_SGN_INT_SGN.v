Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_INT_SGN_term_abbrevs.
Require Import REAL_SGN_REAL_SGN_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309833 (x : int) : term0 x.
Proof. exact (@lem1772290 (real_of_int x)). Qed.
Lemma lem2309834 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309835 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2309834 x) (@lem2309833 x)). Qed.
Lemma lem2309837 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309838 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem2309839 (x : int) : (term1 x) = (term4 x).
Proof. exact (MK_COMB (@lem2309838) (@lem2309837 x)). Qed.
Lemma lem2309841 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309842 (x : int) : (term4 x) = (term5 x).
Proof. exact (@lem2309841 (int_sgn x)). Qed.
Lemma lem2309843 (x : int) : (term1 x) = (term5 x).
Proof. exact (TRANS (@lem2309839 x) (@lem2309842 x)). Qed.
Lemma lem2309844 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309845 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2309844) (@lem2309843 x)). Qed.
Lemma lem2309847 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309848 (x : int) : ((term1 x) = (term2 x)) = ((term5 x) = (term3 x)).
Proof. exact (MK_COMB (@lem2309845 x) (@lem2309847 x)). Qed.
Lemma lem2309850 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309851 (x : int) : ((term5 x) = (term3 x)) = ((term8 x) = (int_sgn x)).
Proof. exact (@lem2309850 (term8 x) (int_sgn x)). Qed.
Lemma lem2309852 (x : int) : ((term1 x) = (term2 x)) = ((term8 x) = (int_sgn x)).
Proof. exact (TRANS (@lem2309848 x) (@lem2309851 x)). Qed.
Lemma lem2309853 (x : int) : (term8 x) = (int_sgn x).
Proof. exact (EQ_MP (@lem2309852 x) (@lem2309835 x)). Qed.
Lemma lem2309854 : term9.
Proof. exact (fun x : int => @lem2309853 x). Qed.

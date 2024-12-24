Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_NEG_term_abbrevs.
Require Import REAL_SGN_NEG_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309891 (x : int) : term0 x.
Proof. exact (@lem1715400 (real_of_int x)). Qed.
Lemma lem2309892 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309893 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2309892 x) (@lem2309891 x)). Qed.
Lemma lem2309895 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2309896 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem2309897 (x : int) : (term1 x) = (term5 x).
Proof. exact (MK_COMB (@lem2309896) (@lem2309895 x)). Qed.
Lemma lem2309899 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309900 (x : int) : (term5 x) = (term8 x).
Proof. exact (@lem2309899 (int_neg x)). Qed.
Lemma lem2309901 (x : int) : (term1 x) = (term8 x).
Proof. exact (TRANS (@lem2309897 x) (@lem2309900 x)). Qed.
Lemma lem2309902 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309903 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2309902) (@lem2309901 x)). Qed.
Lemma lem2309905 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309906 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2309907 (x : int) : (term2 x) = (term11 x).
Proof. exact (MK_COMB (@lem2309906) (@lem2309905 x)). Qed.
Lemma lem2309909 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2309910 (x : int) : (term11 x) = (term12 x).
Proof. exact (@lem2309909 (int_sgn x)). Qed.
Lemma lem2309911 (x : int) : (term2 x) = (term12 x).
Proof. exact (TRANS (@lem2309907 x) (@lem2309910 x)). Qed.
Lemma lem2309912 (x : int) : ((term1 x) = (term2 x)) = ((term8 x) = (term12 x)).
Proof. exact (MK_COMB (@lem2309903 x) (@lem2309911 x)). Qed.
Lemma lem2309914 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309915 (x : int) : ((term8 x) = (term12 x)) = ((term13 x) = (term14 x)).
Proof. exact (@lem2309914 (term13 x) (term14 x)). Qed.
Lemma lem2309916 (x : int) : ((term1 x) = (term2 x)) = ((term13 x) = (term14 x)).
Proof. exact (TRANS (@lem2309912 x) (@lem2309915 x)). Qed.
Lemma lem2309917 (x : int) : (term13 x) = (term14 x).
Proof. exact (EQ_MP (@lem2309916 x) (@lem2309893 x)). Qed.
Lemma lem2309918 : term15.
Proof. exact (fun x : int => @lem2309917 x). Qed.

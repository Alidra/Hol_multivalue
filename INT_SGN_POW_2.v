Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_POW_2_term_abbrevs.
Require Import REAL_SGN_POW_2_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309953 (x : int) : term0 x.
Proof. exact (@lem1760046 (real_of_int x)). Qed.
Lemma lem2309954 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309955 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2309954 x) (@lem2309953 x)). Qed.
Lemma lem2309957 (x : int) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2309958 (x : int) : (term5 x) = (term6 x).
Proof. exact (@lem2309957 x term7). Qed.
Lemma lem2309959 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem2309960 (x : int) : (term1 x) = (term8 x).
Proof. exact (MK_COMB (@lem2309959) (@lem2309958 x)). Qed.
Lemma lem2309962 (x : int) : (term9 x) = (term10 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309963 (x : int) : (term8 x) = (term11 x).
Proof. exact (@lem2309962 (term12 x)). Qed.
Lemma lem2309964 (x : int) : (term1 x) = (term11 x).
Proof. exact (TRANS (@lem2309960 x) (@lem2309963 x)). Qed.
Lemma lem2309965 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309966 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2309965) (@lem2309964 x)). Qed.
Lemma lem2309968 (x : int) : (term15 x) = (term16 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2309969 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem2309970 (x : int) : (term2 x) = (term17 x).
Proof. exact (MK_COMB (@lem2309969) (@lem2309968 x)). Qed.
Lemma lem2309972 (x : int) : (term9 x) = (term10 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309973 (x : int) : (term17 x) = (term18 x).
Proof. exact (@lem2309972 (int_abs x)). Qed.
Lemma lem2309974 (x : int) : (term2 x) = (term18 x).
Proof. exact (TRANS (@lem2309970 x) (@lem2309973 x)). Qed.
Lemma lem2309975 (x : int) : ((term1 x) = (term2 x)) = ((term11 x) = (term18 x)).
Proof. exact (MK_COMB (@lem2309966 x) (@lem2309974 x)). Qed.
Lemma lem2309977 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309978 (x : int) : ((term11 x) = (term18 x)) = ((term19 x) = (term20 x)).
Proof. exact (@lem2309977 (term19 x) (term20 x)). Qed.
Lemma lem2309979 (x : int) : ((term1 x) = (term2 x)) = ((term19 x) = (term20 x)).
Proof. exact (TRANS (@lem2309975 x) (@lem2309978 x)). Qed.
Lemma lem2309980 (x : int) : (term19 x) = (term20 x).
Proof. exact (EQ_MP (@lem2309979 x) (@lem2309955 x)). Qed.
Lemma lem2309981 : term21.
Proof. exact (fun x : int => @lem2309980 x). Qed.

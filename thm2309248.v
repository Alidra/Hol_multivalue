Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2309248_term_abbrevs.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309231 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309232 : term1 = term2.
Proof. exact (@lem2309231 (NUMERAL 0)). Qed.
Lemma lem2309233 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem2309234 : term3 = term4.
Proof. exact (MK_COMB (@lem2309233) (@lem2309232)). Qed.
Lemma lem2309236 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309237 : term4 = term7.
Proof. exact (@lem2309236 term8). Qed.
Lemma lem2309238 : term3 = term7.
Proof. exact (TRANS (@lem2309234) (@lem2309237)). Qed.
Lemma lem2309239 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309240 : term9 = term10.
Proof. exact (MK_COMB (@lem2309239) (@lem2309238)). Qed.
Lemma lem2309242 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309243 : term1 = term2.
Proof. exact (@lem2309242 (NUMERAL 0)). Qed.
Lemma lem2309244 : (term3 = term1) = (term7 = term2).
Proof. exact (MK_COMB (@lem2309240) (@lem2309243)). Qed.
Lemma lem2309246 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309247 : (term7 = term2) = (term11 = term8).
Proof. exact (@lem2309246 term11 term8). Qed.
Lemma lem2309248 : (term3 = term1) = (term11 = term8).
Proof. exact (TRANS (@lem2309244) (@lem2309247)). Qed.

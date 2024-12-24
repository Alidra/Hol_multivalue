Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306330_term_abbrevs.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306313 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306314 : term1 = term2.
Proof. exact (@lem2306313 (NUMERAL 0)). Qed.
Lemma lem2306315 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2306316 : term3 = term4.
Proof. exact (MK_COMB (@lem2306315) (@lem2306314)). Qed.
Lemma lem2306318 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306319 : term4 = term7.
Proof. exact (@lem2306318 term8). Qed.
Lemma lem2306320 : term3 = term7.
Proof. exact (TRANS (@lem2306316) (@lem2306319)). Qed.
Lemma lem2306321 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306322 : term9 = term10.
Proof. exact (MK_COMB (@lem2306321) (@lem2306320)). Qed.
Lemma lem2306324 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306325 : term1 = term2.
Proof. exact (@lem2306324 (NUMERAL 0)). Qed.
Lemma lem2306326 : (term3 = term1) = (term7 = term2).
Proof. exact (MK_COMB (@lem2306322) (@lem2306325)). Qed.
Lemma lem2306328 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306329 : (term7 = term2) = (term11 = term8).
Proof. exact (@lem2306328 term11 term8). Qed.
Lemma lem2306330 : (term3 = term1) = (term11 = term8).
Proof. exact (TRANS (@lem2306326) (@lem2306329)). Qed.

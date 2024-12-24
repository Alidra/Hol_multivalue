Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_1_term_abbrevs.
Require Import REAL_ABS_1_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2299972 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2299973 : term1 = term2.
Proof. exact (@lem2299972 term3). Qed.
Lemma lem2299974 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2299975 : term4 = term5.
Proof. exact (MK_COMB (@lem2299974) (@lem2299973)). Qed.
Lemma lem2299977 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2299978 : term5 = term8.
Proof. exact (@lem2299977 term9). Qed.
Lemma lem2299979 : term4 = term8.
Proof. exact (TRANS (@lem2299975) (@lem2299978)). Qed.
Lemma lem2299980 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2299981 : term10 = term11.
Proof. exact (MK_COMB (@lem2299980) (@lem2299979)). Qed.
Lemma lem2299983 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2299984 : term1 = term2.
Proof. exact (@lem2299983 term3). Qed.
Lemma lem2299985 : (term4 = term1) = (term8 = term2).
Proof. exact (MK_COMB (@lem2299981) (@lem2299984)). Qed.
Lemma lem2299987 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2299988 : (term8 = term2) = (term12 = term9).
Proof. exact (@lem2299987 term12 term9). Qed.
Lemma lem2299989 : (term4 = term1) = (term12 = term9).
Proof. exact (TRANS (@lem2299985) (@lem2299988)). Qed.
Lemma lem2299990 : term12 = term9.
Proof. exact (EQ_MP (@lem2299989) (@lem1528532)). Qed.

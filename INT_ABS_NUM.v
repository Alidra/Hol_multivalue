Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_NUM_term_abbrevs.
Require Import REAL_ABS_NUM_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300453 (n : nat) : term0 n.
Proof. exact (@lem1362923 n). Qed.
Lemma lem2300454 (n : nat) : (term0 n) = ((term1 n) = (real_of_num n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2300455 (n : nat) : (term1 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2300454 n) (@lem2300453 n)). Qed.
Lemma lem2300457 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300458 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300459 (n : nat) : (term1 n) = (term3 n).
Proof. exact (MK_COMB (@lem2300458) (@lem2300457 n)). Qed.
Lemma lem2300461 (x : int) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300462 (n : nat) : (term3 n) = (term6 n).
Proof. exact (@lem2300461 (int_of_num n)). Qed.
Lemma lem2300463 (n : nat) : (term1 n) = (term6 n).
Proof. exact (TRANS (@lem2300459 n) (@lem2300462 n)). Qed.
Lemma lem2300464 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300465 (n : nat) : (term7 n) = (term8 n).
Proof. exact (MK_COMB (@lem2300464) (@lem2300463 n)). Qed.
Lemma lem2300467 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300468 (n : nat) : ((term1 n) = (real_of_num n)) = ((term6 n) = (term2 n)).
Proof. exact (MK_COMB (@lem2300465 n) (@lem2300467 n)). Qed.
Lemma lem2300470 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300471 (n : nat) : ((term6 n) = (term2 n)) = ((term9 n) = (int_of_num n)).
Proof. exact (@lem2300470 (term9 n) (int_of_num n)). Qed.
Lemma lem2300472 (n : nat) : ((term1 n) = (real_of_num n)) = ((term9 n) = (int_of_num n)).
Proof. exact (TRANS (@lem2300468 n) (@lem2300471 n)). Qed.
Lemma lem2300473 (n : nat) : (term9 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2300472 n) (@lem2300455 n)). Qed.
Lemma lem2300474 : term10.
Proof. exact (fun n : nat => @lem2300473 n). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_POW_term_abbrevs.
Require Import REAL_ABS_POW_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300523 (x : int) : term0 x.
Proof. exact (@lem1582667 (real_of_int x)). Qed.
Lemma lem2300524 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300525 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300524 x) (@lem2300523 x)). Qed.
Lemma lem2300526 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2300525 x n). Qed.
Lemma lem2300527 (x : int) (n : nat) : (term2 x n) = ((term3 x n) = (term4 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2300528 (x : int) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem2300527 x n) (@lem2300526 x n)). Qed.
Lemma lem2300530 (x : int) (n : nat) : (term5 x n) = (term6 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2300531 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300532 (x : int) (n : nat) : (term3 x n) = (term7 x n).
Proof. exact (MK_COMB (@lem2300531) (@lem2300530 x n)). Qed.
Lemma lem2300534 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300535 (x : int) (n : nat) : (term7 x n) = (term10 x n).
Proof. exact (@lem2300534 (int_pow x n)). Qed.
Lemma lem2300536 (x : int) (n : nat) : (term3 x n) = (term10 x n).
Proof. exact (TRANS (@lem2300532 x n) (@lem2300535 x n)). Qed.
Lemma lem2300537 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300538 (x : int) (n : nat) : (term11 x n) = (term12 x n).
Proof. exact (MK_COMB (@lem2300537) (@lem2300536 x n)). Qed.
Lemma lem2300540 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300541 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2300542 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2300541) (@lem2300540 x)). Qed.
Lemma lem2300543 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2300544 (x : int) (n : nat) : (term4 x n) = (term15 x n).
Proof. exact (MK_COMB (@lem2300542 x) (@lem2300543 n)). Qed.
Lemma lem2300546 (x : int) (n : nat) : (term5 x n) = (term6 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2300547 (x : int) (n : nat) : (term15 x n) = (term16 x n).
Proof. exact (@lem2300546 (int_abs x) n). Qed.
Lemma lem2300548 (x : int) (n : nat) : (term4 x n) = (term16 x n).
Proof. exact (TRANS (@lem2300544 x n) (@lem2300547 x n)). Qed.
Lemma lem2300549 (x : int) (n : nat) : ((term3 x n) = (term4 x n)) = ((term10 x n) = (term16 x n)).
Proof. exact (MK_COMB (@lem2300538 x n) (@lem2300548 x n)). Qed.
Lemma lem2300551 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300552 (x : int) (n : nat) : ((term10 x n) = (term16 x n)) = ((term17 x n) = (term18 x n)).
Proof. exact (@lem2300551 (term17 x n) (term18 x n)). Qed.
Lemma lem2300553 (x : int) (n : nat) : ((term3 x n) = (term4 x n)) = ((term17 x n) = (term18 x n)).
Proof. exact (TRANS (@lem2300549 x n) (@lem2300552 x n)). Qed.
Lemma lem2300554 (x : int) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem2300553 x n) (@lem2300528 x n)). Qed.
Lemma lem2300555 (x : int) : term19 x.
Proof. exact (fun n : nat => @lem2300554 x n). Qed.
Lemma lem2300556 : term20.
Proof. exact (fun x : int => @lem2300555 x). Qed.

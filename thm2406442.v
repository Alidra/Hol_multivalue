Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2406442_term_abbrevs.
Require Import INT_ABS_NEG_spec.
Require Import INT_ABS_NUM_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2406394 (n : nat) : term0 n.
Proof. exact (@lem2300474 n). Qed.
Lemma lem2406395 (n : nat) : (term0 n) = ((term1 n) = (int_of_num n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2406397 (x : int) : term2 x.
Proof. exact (@lem2300452 x). Qed.
Lemma lem2406398 (x : int) : (term2 x) = ((term3 x) = (int_abs x)).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem2406405 (x : int) : (term3 x) = (int_abs x).
Proof. exact (EQ_MP (@lem2406398 x) (@lem2406397 x)). Qed.
Lemma lem2406406 (x : nat) : (term4 x) = (term1 x).
Proof. exact (@lem2406405 (int_of_num x)). Qed.
Lemma lem2406408 (n : nat) : (term1 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2406395 n) (@lem2406394 n)). Qed.
Lemma lem2406409 (x : nat) : (term1 x) = (int_of_num x).
Proof. exact (@lem2406408 x). Qed.
Lemma lem2406410 (x : nat) : (term4 x) = (int_of_num x).
Proof. exact (TRANS (@lem2406406 x) (@lem2406409 x)). Qed.
Lemma lem2406411 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406412 (x : nat) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem2406411) (@lem2406410 x)). Qed.
Lemma lem2406413 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem2406414 (x : nat) : ((term4 x) = (int_of_num x)) = ((int_of_num x) = (int_of_num x)).
Proof. exact (MK_COMB (@lem2406412 x) (@lem2406413 x)). Qed.
Lemma lem2406416 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2406417 (x : int) : (x = x) = True.
Proof. exact (@lem2406416 int x). Qed.
Lemma lem2406418 (x : nat) : ((int_of_num x) = (int_of_num x)) = True.
Proof. exact (@lem2406417 (int_of_num x)). Qed.
Lemma lem2406419 (x : nat) : ((term4 x) = (int_of_num x)) = True.
Proof. exact (TRANS (@lem2406414 x) (@lem2406418 x)). Qed.
Lemma lem2406420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2406421 (x : nat) : (term7 x) = (and True).
Proof. exact (MK_COMB (@lem2406420) (@lem2406419 x)). Qed.
Lemma lem2406425 (n : nat) : (term1 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2406395 n) (@lem2406394 n)). Qed.
Lemma lem2406426 (x : nat) : (term1 x) = (int_of_num x).
Proof. exact (@lem2406425 x). Qed.
Lemma lem2406427 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406428 (x : nat) : (term8 x) = (term6 x).
Proof. exact (MK_COMB (@lem2406427) (@lem2406426 x)). Qed.
Lemma lem2406429 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem2406430 (x : nat) : ((term1 x) = (int_of_num x)) = ((int_of_num x) = (int_of_num x)).
Proof. exact (MK_COMB (@lem2406428 x) (@lem2406429 x)). Qed.
Lemma lem2406432 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2406433 (x : int) : (x = x) = True.
Proof. exact (@lem2406432 int x). Qed.
Lemma lem2406434 (x : nat) : ((int_of_num x) = (int_of_num x)) = True.
Proof. exact (@lem2406433 (int_of_num x)). Qed.
Lemma lem2406435 (x : nat) : ((term1 x) = (int_of_num x)) = True.
Proof. exact (TRANS (@lem2406430 x) (@lem2406434 x)). Qed.
Lemma lem2406436 (x : nat) : (term9 x) = (True /\ True).
Proof. exact (MK_COMB (@lem2406421 x) (@lem2406435 x)). Qed.
Lemma lem2406438 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2406439 : (True /\ True) = True.
Proof. exact (@lem2406438 True). Qed.
Lemma lem2406440 (x : nat) : (term9 x) = True.
Proof. exact (TRANS (@lem2406436 x) (@lem2406439)). Qed.
Lemma lem2406441 (x : nat) : True = (term9 x).
Proof. exact (SYM (@lem2406440 x)). Qed.
Lemma lem2406442 (x : nat) : term9 x.
Proof. exact (EQ_MP (@lem2406441 x) (@lem0)). Qed.

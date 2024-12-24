Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm159435_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DIV_ZERO_spec.
Require Import MOD_ZERO_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem159347 : term0.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem159348 (n : nat) : term1 n.
Proof. exact (@lem159347 n). Qed.
Lemma lem159349 (n : nat) : (term1 n) = ((term2 n) = n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem159381 : term3.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem159382 (n : nat) : term4 n.
Proof. exact (@lem159381 n). Qed.
Lemma lem159383 (n : nat) : (term4 n) = ((term5 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem159385 (n : nat) : term6 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem159386 (n : nat) : (term6 n) = ((term7 n) = n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem159388 (n : nat) : term8 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem159389 (n : nat) : (term8 n) = ((term9 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem159394 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem159395 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem159396 (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n) = term10.
Proof. exact (MK_COMB (@lem159395) (@lem159394 n h1)). Qed.
Lemma lem159398 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem159399 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem159400 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (term9 m).
Proof. exact (MK_COMB (@lem159399 m) (@lem159398 n h1)). Qed.
Lemma lem159402 (n : nat) : (term9 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem159389 n) (@lem159388 n)). Qed.
Lemma lem159403 (m : nat) : (term9 m) = (NUMERAL 0).
Proof. exact (@lem159402 m). Qed.
Lemma lem159404 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem159400 m n h1) (@lem159403 m)). Qed.
Lemma lem159405 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term11 m n) = term12.
Proof. exact (MK_COMB (@lem159396 n h1) (@lem159404 m n h1)). Qed.
Lemma lem159407 (n : nat) : (term5 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem159383 n) (@lem159382 n)). Qed.
Lemma lem159408 : term12 = (NUMERAL 0).
Proof. exact (@lem159407 (NUMERAL 0)). Qed.
Lemma lem159409 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term11 m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem159405 m n h1) (@lem159408)). Qed.
Lemma lem159410 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem159411 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term13 m n) = term14.
Proof. exact (MK_COMB (@lem159410) (@lem159409 m n h1)). Qed.
Lemma lem159413 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem159414 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem159415 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term7 m).
Proof. exact (MK_COMB (@lem159414 m) (@lem159413 n h1)). Qed.
Lemma lem159417 (n : nat) : (term7 n) = n.
Proof. exact (EQ_MP (@lem159386 n) (@lem159385 n)). Qed.
Lemma lem159418 (m : nat) : (term7 m) = m.
Proof. exact (@lem159417 m). Qed.
Lemma lem159419 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = m.
Proof. exact (TRANS (@lem159415 m n h1) (@lem159418 m)). Qed.
Lemma lem159420 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term15 m n) = (term2 m).
Proof. exact (MK_COMB (@lem159411 m n h1) (@lem159419 m n h1)). Qed.
Lemma lem159422 (n : nat) : (term2 n) = n.
Proof. exact (EQ_MP (@lem159349 n) (@lem159348 n)). Qed.
Lemma lem159423 (m : nat) : (term2 m) = m.
Proof. exact (@lem159422 m). Qed.
Lemma lem159424 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term15 m n) = m.
Proof. exact (TRANS (@lem159420 m n h1) (@lem159423 m)). Qed.
Lemma lem159425 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem159426 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term16 m n) = (@eq nat m).
Proof. exact (MK_COMB (@lem159425) (@lem159424 m n h1)). Qed.
Lemma lem159427 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem159428 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term15 m n) = m) = (m = m).
Proof. exact (MK_COMB (@lem159426 m n h1) (@lem159427 m)). Qed.
Lemma lem159430 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem159431 (x : nat) : (x = x) = True.
Proof. exact (@lem159430 nat x). Qed.
Lemma lem159432 (m : nat) : (m = m) = True.
Proof. exact (@lem159431 m). Qed.
Lemma lem159433 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term15 m n) = m) = True.
Proof. exact (TRANS (@lem159428 m n h1) (@lem159432 m)). Qed.
Lemma lem159434 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term15 m n) = m).
Proof. exact (SYM (@lem159433 m n h1)). Qed.
Lemma lem159435 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term15 m n) = m.
Proof. exact (EQ_MP (@lem159434 m n h1) (@lem0)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POS_term_abbrevs.
Require Import REAL_POS_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2307519 (n : nat) : term0 n.
Proof. exact (@lem1384343 n). Qed.
Lemma lem2307520 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2307521 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2307520 n) (@lem2307519 n)). Qed.
Lemma lem2307523 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307524 : term3 = term4.
Proof. exact (@lem2307523 (NUMERAL 0)). Qed.
Lemma lem2307525 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2307526 : term5 = term6.
Proof. exact (MK_COMB (@lem2307525) (@lem2307524)). Qed.
Lemma lem2307528 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307529 (n : nat) : (term1 n) = (term7 n).
Proof. exact (MK_COMB (@lem2307526) (@lem2307528 n)). Qed.
Lemma lem2307531 (x : int) (y : int) : (term8 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2307532 (n : nat) : (term7 n) = (term9 n).
Proof. exact (@lem2307531 term10 (int_of_num n)). Qed.
Lemma lem2307533 (n : nat) : (term1 n) = (term9 n).
Proof. exact (TRANS (@lem2307529 n) (@lem2307532 n)). Qed.
Lemma lem2307534 (n : nat) : term9 n.
Proof. exact (EQ_MP (@lem2307533 n) (@lem2307521 n)). Qed.
Lemma lem2307535 : term11.
Proof. exact (fun n : nat => @lem2307534 n). Qed.

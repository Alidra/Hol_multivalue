Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_01_term_abbrevs.
Require Import REAL_LT_01_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2303639 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303640 : term1 = term2.
Proof. exact (@lem2303639 (NUMERAL 0)). Qed.
Lemma lem2303641 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303642 : term3 = term4.
Proof. exact (MK_COMB (@lem2303641) (@lem2303640)). Qed.
Lemma lem2303644 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303645 : term5 = term6.
Proof. exact (@lem2303644 term7). Qed.
Lemma lem2303646 : term8 = term9.
Proof. exact (MK_COMB (@lem2303642) (@lem2303645)). Qed.
Lemma lem2303648 (x : int) (y : int) : (term10 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303649 : term9 = term11.
Proof. exact (@lem2303648 term12 term13). Qed.
Lemma lem2303650 : term8 = term11.
Proof. exact (TRANS (@lem2303646) (@lem2303649)). Qed.
Lemma lem2303651 : term11.
Proof. exact (EQ_MP (@lem2303650) (@lem1499399)). Qed.

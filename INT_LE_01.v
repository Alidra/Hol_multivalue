Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_01_term_abbrevs.
Require Import REAL_LE_01_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302160 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302161 : term1 = term2.
Proof. exact (@lem2302160 (NUMERAL 0)). Qed.
Lemma lem2302162 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302163 : term3 = term4.
Proof. exact (MK_COMB (@lem2302162) (@lem2302161)). Qed.
Lemma lem2302165 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302166 : term5 = term6.
Proof. exact (@lem2302165 term7). Qed.
Lemma lem2302167 : term8 = term9.
Proof. exact (MK_COMB (@lem2302163) (@lem2302166)). Qed.
Lemma lem2302169 (x : int) (y : int) : (term10 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302170 : term9 = term11.
Proof. exact (@lem2302169 term12 term13). Qed.
Lemma lem2302171 : term8 = term11.
Proof. exact (TRANS (@lem2302167) (@lem2302170)). Qed.
Lemma lem2302172 : term11.
Proof. exact (EQ_MP (@lem2302171) (@lem1499322)). Qed.

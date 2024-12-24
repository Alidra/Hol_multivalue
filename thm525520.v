Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm525520_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem525459 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem525460 : term1.
Proof. exact (proj2 (@lem525459)). Qed.
Lemma lem525461 : term2.
Proof. exact (proj2 (@lem525460)). Qed.
Lemma lem525503 : term3.
Proof. exact (proj1 (@lem525461)). Qed.
Lemma lem525504 (n : nat) : term4 n.
Proof. exact (@lem525503 n). Qed.
Lemma lem525505 (n : nat) : (term4 n) = ((term5 n) = (BIT1 n)).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem525520 (n : nat) : (term5 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem525505 n) (@lem525504 n)). Qed.

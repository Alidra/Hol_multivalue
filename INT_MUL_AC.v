Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_AC_term_abbrevs.
Require Import thm2305894_spec.
Require Import thm2305903_spec.
Require Import thm2305916_spec.
Lemma lem2305917 (n : int) (m : int) : (int_mul m n) = (int_mul n m).
Proof. exact (EQ_MP (@lem2305916 n m) (@lem2305903 n m)). Qed.
Lemma lem2305918 (n : int) (m : int) (p : int) : term0 n m p.
Proof. exact (conj (@lem2305917 n m) (@lem2305894 n m p)). Qed.

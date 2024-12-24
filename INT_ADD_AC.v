Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD_AC_term_abbrevs.
Require Import thm2301004_spec.
Require Import thm2301013_spec.
Require Import thm2301026_spec.
Lemma lem2301027 (n : int) (m : int) : (int_add m n) = (int_add n m).
Proof. exact (EQ_MP (@lem2301026 n m) (@lem2301013 n m)). Qed.
Lemma lem2301028 (n : int) (m : int) (p : int) : term0 n m p.
Proof. exact (conj (@lem2301027 n m) (@lem2301004 n m p)). Qed.

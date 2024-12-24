Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2406277_term_abbrevs.
Require Import thm2406274_spec.
Lemma lem2406277 (m : nat) (n : nat) : (term0 n m) = (term1 n).
Proof. exact (proj1 (@lem2406274 m n)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367771_term_abbrevs.
Require Import thm1367768_spec.
Lemma lem1367771 (m : nat) (n : nat) : (term0 m n) = (term1 n).
Proof. exact (proj1 (@lem1367768 m n)). Qed.

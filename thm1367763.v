Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367763_term_abbrevs.
Require Import thm1367761_spec.
Lemma lem1367763 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (proj1 (@lem1367761 m n)). Qed.

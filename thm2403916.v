Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2403916_term_abbrevs.
Require Import thm2403914_spec.
Lemma lem2403916 (m : nat) (n : nat) : term0 m n.
Proof. exact (proj2 (@lem2403914 m n)). Qed.
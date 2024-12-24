Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2406272_term_abbrevs.
Require Import thm2406271_spec.
Lemma lem2406272 (m : nat) (n : nat) : term0 m n.
Proof. exact (proj2 (@lem2406271 m n)). Qed.

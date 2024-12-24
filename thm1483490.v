Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483490_term_abbrevs.
Require Import thm1483487_spec.
Lemma lem1483490 (a : real) (c : real) (d : real) : (term0 a c d) = (term1 a c d).
Proof. exact (proj1 (@lem1483487 a c d (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

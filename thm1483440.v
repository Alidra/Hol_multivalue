Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483440_term_abbrevs.
Require Import thm1483437_spec.
Lemma lem1483440 (a : real) (m : real) : (term0 a m) = (term1 a m).
Proof. exact (proj1 (@lem1483437 m (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483436_term_abbrevs.
Require Import thm1483434_spec.
Lemma lem1483436 (x : real) : (term0 x) = x.
Proof. exact (proj1 (@lem1483434 (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) x (@el nat))). Qed.

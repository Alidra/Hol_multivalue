Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483458_term_abbrevs.
Require Import thm1483455_spec.
Lemma lem1483458 (a : real) : (term0 a) = term1.
Proof. exact (proj1 (@lem1483455 (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

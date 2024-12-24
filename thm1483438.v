Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483438_term_abbrevs.
Require Import thm1483435_spec.
Lemma lem1483438 (a : real) (b : real) (m : real) : (term0 a b m) = (term1 a b m).
Proof. exact (proj1 (@lem1483435 m (@el real) (@el real) (@el real) (@el real) b a (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

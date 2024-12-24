Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483450_term_abbrevs.
Require Import thm1483447_spec.
Lemma lem1483450 (a : real) : (term0 a) = a.
Proof. exact (proj1 (@lem1483447 (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982777_term_abbrevs.
Require Import thm1982774_spec.
Lemma lem1982777 (x : real) : (term0 x) = term1.
Proof. exact (proj1 (@lem1982774 (@el real) (@el real) x (@el nat))). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982719_term_abbrevs.
Require Import thm1982716_spec.
Lemma lem1982719 (m : real) : (term0 m) = term1.
Proof. exact (proj1 (@lem1982716 m (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

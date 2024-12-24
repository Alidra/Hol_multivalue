Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982743_term_abbrevs.
Require Import thm1982740_spec.
Lemma lem1982743 (lx : real) (rx : real) (ly : real) : (term0 lx ly rx) = (term0 lx rx ly).
Proof. exact (proj1 (@lem1982740 ly rx lx (@el real) (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

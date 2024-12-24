Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483476_term_abbrevs.
Require Import thm1483473_spec.
Lemma lem1483476 (lx : real) (rx : real) (ry : real) : (term0 lx rx ry) = (term1 lx rx ry).
Proof. exact (proj1 (@lem1483473 rx lx ry (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

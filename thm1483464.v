Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483464_term_abbrevs.
Require Import thm1483461_spec.
Lemma lem1483464 (lx : real) (rx : real) (ly : real) (ry : real) : (term0 lx ly rx ry) = (term0 lx rx ly ry).
Proof. exact (proj1 (@lem1483461 ly rx lx ry (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

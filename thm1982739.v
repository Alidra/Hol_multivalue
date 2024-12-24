Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982739_term_abbrevs.
Require Import thm1982736_spec.
Lemma lem1982739 (lx : real) (ly : real) (rx : real) (ry : real) : (term0 lx ly rx ry) = (term1 lx ly rx ry).
Proof. exact (proj1 (@lem1982736 ly rx lx ry (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

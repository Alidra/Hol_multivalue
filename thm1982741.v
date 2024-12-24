Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982741_term_abbrevs.
Require Import thm1982738_spec.
Lemma lem1982741 (rx : real) (lx : real) (ly : real) (ry : real) : (term0 lx ly rx ry) = (term1 rx lx ly ry).
Proof. exact (proj1 (@lem1982738 ly rx lx ry (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

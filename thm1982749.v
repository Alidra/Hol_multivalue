Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982749_term_abbrevs.
Require Import thm1982746_spec.
Lemma lem1982749 (lx : real) (rx : real) (ry : real) : (term0 lx rx ry) = (term1 lx rx ry).
Proof. exact (proj1 (@lem1982746 rx lx ry (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

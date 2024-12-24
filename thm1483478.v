Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483478_term_abbrevs.
Require Import thm1483475_spec.
Lemma lem1483478 (rx : real) (lx : real) (ry : real) : (term0 lx rx ry) = (term0 rx lx ry).
Proof. exact (proj1 (@lem1483475 rx lx ry (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

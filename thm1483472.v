Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483472_term_abbrevs.
Require Import thm1483469_spec.
Lemma lem1483472 (lx : real) (ly : real) (rx : real) : (term0 lx ly rx) = (term1 lx ly rx).
Proof. exact (proj1 (@lem1483469 ly rx lx (@el real) (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

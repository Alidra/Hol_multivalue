Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982758_spec.
Lemma lem1982761 (c : real) (a : real) : (real_add a c) = (real_add c a).
Proof. exact (proj1 (@lem1982758 a c (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.
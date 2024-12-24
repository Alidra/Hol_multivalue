Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483446_term_abbrevs.
Require Import thm1483443_spec.
Lemma lem1483446 (m : real) : (term0 m) = term1.
Proof. exact (proj1 (@lem1483443 m (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

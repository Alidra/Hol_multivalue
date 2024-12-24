Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982744_spec.
Lemma lem1982747 (rx : real) (lx : real) : (real_mul lx rx) = (real_mul rx lx).
Proof. exact (proj1 (@lem1982744 rx lx (@el real) (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

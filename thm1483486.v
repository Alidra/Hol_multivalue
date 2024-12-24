Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483486_term_abbrevs.
Require Import thm1483483_spec.
Lemma lem1483486 (a : real) (c : real) (b : real) : (term0 a b c) = (term0 a c b).
Proof. exact (proj1 (@lem1483483 b a c (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982759_term_abbrevs.
Require Import thm1982756_spec.
Lemma lem1982759 (a : real) (c : real) (b : real) : (term0 a b c) = (term0 a c b).
Proof. exact (proj1 (@lem1982756 b a c (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483480_term_abbrevs.
Require Import thm1483477_spec.
Lemma lem1483480 (a : real) (c : real) (b : real) (d : real) : (term0 a b c d) = (term0 a c b d).
Proof. exact (proj1 (@lem1483477 b a c d (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

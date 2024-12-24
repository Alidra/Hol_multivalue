Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483484_term_abbrevs.
Require Import thm1483481_spec.
Lemma lem1483484 (c : real) (a : real) (d : real) : (term0 a c d) = (term0 c a d).
Proof. exact (proj1 (@lem1483481 (@el real) a c d (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

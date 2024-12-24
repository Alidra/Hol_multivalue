Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483506_term_abbrevs.
Require Import thm1483503_spec.
Lemma lem1483506 (x : real) : (term0 x) = x.
Proof. exact (proj1 (@lem1483503 (@el real) (@el real) x (@el nat))). Qed.

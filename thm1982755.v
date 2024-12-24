Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982755_term_abbrevs.
Require Import thm1982752_spec.
Lemma lem1982755 (a : real) (b : real) (c : real) : (term0 a b c) = (term1 a b c).
Proof. exact (proj1 (@lem1982752 b a c (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

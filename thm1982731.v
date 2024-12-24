Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982731_term_abbrevs.
Require Import thm1982728_spec.
Lemma lem1982731 (a : real) : (term0 a) = term1.
Proof. exact (proj1 (@lem1982728 (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.

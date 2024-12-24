Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1344312_term_abbrevs.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Lemma lem1344312 (x : real) : (term0 x) = term1.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.

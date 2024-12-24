Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337484_term_abbrevs.
Lemma lem1337484 (a : real) : (term0 a) = a.
Proof. exact (@axiom_23 a). Qed.

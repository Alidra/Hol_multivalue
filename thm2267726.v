Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2267726_term_abbrevs.
Lemma lem2267726 (a : int) : (term0 a) = a.
Proof. exact (@axiom_25 a). Qed.

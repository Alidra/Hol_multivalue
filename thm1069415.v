Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069415_term_abbrevs.
Lemma lem1069415 {A : Type'} (r : recspace A) : (term0 A r) = ((term1 A r) = r).
Proof. exact (@axiom_14 A r). Qed.

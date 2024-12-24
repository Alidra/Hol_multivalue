Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7925131_term_abbrevs.
Lemma lem7925131 {A : Type'} (r : type1676 A) : (term0 A r) = ((term1 A r) = r).
Proof. exact (@axiom_38 A r). Qed.

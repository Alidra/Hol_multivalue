Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7928450_term_abbrevs.
Lemma lem7928450 {A : Type'} (r : type1675 A) : (term0 A r) = ((term1 A r) = r).
Proof. exact (@axiom_40 A r). Qed.

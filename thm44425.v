Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm44425_term_abbrevs.
Lemma lem44425 {A B : Type'} (a : prod A B) : (term0 A B a) = a.
Proof. exact (@axiom_4 A B a). Qed.

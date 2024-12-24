Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066989_term_abbrevs.
Lemma lem1066989 {A B : Type'} (r : type1677 A B) : (term0 A B r) = ((term1 A B r) = r).
Proof. exact (@axiom_12 A B r). Qed.

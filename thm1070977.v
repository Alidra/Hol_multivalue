Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1070977_term_abbrevs.
Lemma lem1070977 {A : Type'} (a : list A) : (term0 A a) = a.
Proof. exact (@axiom_15 A a). Qed.

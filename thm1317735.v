Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1317735_term_abbrevs.
Lemma lem1317735 (a : hreal) : (term0 a) = a.
Proof. exact (@axiom_21 a). Qed.

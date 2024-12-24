Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm707013_term_abbrevs.
Require Import thm534523_spec.
Require Import thm534539_spec.
Lemma lem707013 : term0 = term1.
Proof. exact (TRANS (@lem534523) (@lem534539)). Qed.

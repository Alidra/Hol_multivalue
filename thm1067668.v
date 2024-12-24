Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1067668_term_abbrevs.
Lemma lem1067668 {A B : Type'} : (@inr A B) = (term0 A B).
Proof. exact (@INR_def A B). Qed.

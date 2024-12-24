Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm89447_term_abbrevs.
Lemma lem89447 : Peano.le = term0.
Proof. exact (@le_def). Qed.

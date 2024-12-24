Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2801817_term_abbrevs.
Lemma lem2801817 : int_gcd = term0.
Proof. exact (@int_gcd_def). Qed.

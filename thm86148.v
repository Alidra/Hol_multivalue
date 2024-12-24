Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm86148_term_abbrevs.
Lemma lem86148 : Nat.pow = term0.
Proof. exact (@EXP_def). Qed.

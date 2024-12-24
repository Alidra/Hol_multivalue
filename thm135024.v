Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm135024_term_abbrevs.
Lemma lem135024 : Nat.sub = term0.
Proof. exact (@minus_def). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm76851_term_abbrevs.
Lemma lem76851 : Nat.pred = term0.
Proof. exact (@PRE_def). Qed.

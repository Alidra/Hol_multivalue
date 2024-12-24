Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm155860_term_abbrevs.
Lemma lem155860 : Nat.modulo = term0.
Proof. exact (@MOD_def). Qed.

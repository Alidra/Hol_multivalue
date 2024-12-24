Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm155534_term_abbrevs.
Lemma lem155534 : Nat.div = term0.
Proof. exact (@DIV_def). Qed.

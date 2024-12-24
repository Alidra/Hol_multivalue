Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm77187_term_abbrevs.
Lemma lem77187 : Nat.add = term0.
Proof. exact (@add_def). Qed.

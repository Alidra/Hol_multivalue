Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm759207_term_abbrevs.
Require Import thm759205_spec.
Lemma lem759206 : term0.
Proof. exact (proj2 (@lem759205)). Qed.
Lemma lem759207 (n : nat) : term1 n.
Proof. exact (@lem759206 n). Qed.

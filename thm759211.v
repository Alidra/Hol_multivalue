Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm759211_term_abbrevs.
Require Import thm759205_spec.
Lemma lem759210 : term0.
Proof. exact (proj1 (@lem759205)). Qed.
Lemma lem759211 (n : nat) : term1 n.
Proof. exact (@lem759210 n). Qed.

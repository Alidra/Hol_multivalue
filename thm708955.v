Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm708955_term_abbrevs.
Require Import thm708953_spec.
Lemma lem708954 : term0.
Proof. exact (proj2 (@lem708953)). Qed.
Lemma lem708955 (n : nat) : term1 n.
Proof. exact (@lem708954 n). Qed.

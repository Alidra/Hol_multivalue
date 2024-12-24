Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528240_term_abbrevs.
Require Import thm528197_spec.
Lemma lem528239 : term0.
Proof. exact (proj1 (@lem528197)). Qed.
Lemma lem528240 (n : nat) : term1 n.
Proof. exact (@lem528239 n). Qed.

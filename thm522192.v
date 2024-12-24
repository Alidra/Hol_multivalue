Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522192_term_abbrevs.
Require Import thm522176_spec.
Lemma lem522192 (n : nat) : term0 n.
Proof. exact (@lem522176 n). Qed.

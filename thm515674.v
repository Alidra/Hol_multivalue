Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515674_term_abbrevs.
Require Import thm515614_spec.
Lemma lem515673 : term0.
Proof. exact (proj1 (@lem515614)). Qed.
Lemma lem515674 (n : nat) : term1 n.
Proof. exact (@lem515673 n). Qed.

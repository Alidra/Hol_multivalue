Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367768_term_abbrevs.
Require Import thm1367766_spec.
Lemma lem1367768 (m : nat) (n : nat) : term0 m n.
Proof. exact (proj2 (@lem1367766 m n)). Qed.

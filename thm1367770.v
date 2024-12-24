Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367770_term_abbrevs.
Require Import thm1367768_spec.
Lemma lem1367770 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (proj2 (@lem1367768 m n)). Qed.

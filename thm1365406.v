Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1365406_term_abbrevs.
Require Import thm1365404_spec.
Lemma lem1365406 (m : nat) (n : nat) : term0 m n.
Proof. exact (proj2 (@lem1365404 m n)). Qed.

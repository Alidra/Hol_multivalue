Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2406278_term_abbrevs.
Require Import thm2406276_spec.
Lemma lem2406278 (m : nat) (n : nat) : term0 m n.
Proof. exact (proj2 (@lem2406276 m n)). Qed.
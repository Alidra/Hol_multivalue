Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm996237_term_abbrevs.
Require Import thm996236_spec.
Lemma lem996237 (m : nat) : (term0 m) = m.
Proof. exact (proj2 (@lem996236 (@el nat) m)). Qed.

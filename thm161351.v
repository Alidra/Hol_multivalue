Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm161351_term_abbrevs.
Require Import thm159520_spec.
Require Import thm160343_spec.
Lemma lem161351 (m : nat) (n : nat) (h1 : term0 n) : (term1 m n) = m.
Proof. exact (EQ_MP (@lem159520 n m) (@lem160343 m n h1)). Qed.

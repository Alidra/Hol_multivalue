Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import is_int_term_abbrevs.
Require Import thm2259383_spec.
Require Import thm2267613_spec.
Lemma lem2267614 (x : real) : (integer x) = (term0 x).
Proof. exact (EQ_MP (@lem2259383 x) (@lem2267613 x)). Qed.

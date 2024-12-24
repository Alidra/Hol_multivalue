Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2530574_term_abbrevs.
Require Import thm2528731_spec.
Require Import thm2530572_spec.
Lemma lem2530574 (n : int) (m : int) (p : int) : (term0 m n p) = (rem m p).
Proof. exact (EQ_MP (@lem2528731 n m p) (@lem2530572 n m p)). Qed.

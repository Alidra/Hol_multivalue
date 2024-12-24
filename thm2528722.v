Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2528722_term_abbrevs.
Lemma lem2528722 (m : int) (n : int) (p : int) : (term0 m n p) = (((rem m p) = (rem n p)) = (term1 m n p)).
Proof. exact (eq_refl (term0 m n p)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2427015_term_abbrevs.
Lemma lem2427015 (a : int) (d : int) (b : int) (c : int) : (term0 a b c d) = ((term1 a b c d) = (term2 a d b c)).
Proof. exact (eq_refl (term0 a b c d)). Qed.

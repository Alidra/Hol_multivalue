Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2406288_term_abbrevs.
Lemma lem2406288 (x : int) (y : int) : (term0 x y) = ((int_sub x y) = (term1 x y)).
Proof. exact (eq_refl (term0 x y)). Qed.

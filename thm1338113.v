Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338113_term_abbrevs.
Lemma lem1338113 (x : prod hreal hreal) (y : prod hreal hreal) : (term0 x y) = ((treal_eq x y) = ((term1 x) = (term1 y))).
Proof. exact (eq_refl (term0 x y)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318767_term_abbrevs.
Lemma lem1318767 (x : nadd) (y : nadd) : (term0 x y) = ((nadd_eq x y) = ((term1 x) = (term1 y))).
Proof. exact (eq_refl (term0 x y)). Qed.
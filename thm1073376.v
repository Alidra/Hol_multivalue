Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1073376_term_abbrevs.
Lemma lem1073376 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term0 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term1 A B x a y b)).
Proof. exact (eq_refl (term0 A B x a y b)). Qed.

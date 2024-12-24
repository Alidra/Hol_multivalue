Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211693_term_abbrevs.
Lemma lem3211693 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term0 A y x s) = ((term1 A x y s) = (term2 A y x s)).
Proof. exact (eq_refl (term0 A y x s)). Qed.

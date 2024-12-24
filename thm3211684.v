Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211684_term_abbrevs.
Lemma lem3211684 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term0 A s x y) = ((term1 A x s y) = (term2 A s x y)).
Proof. exact (eq_refl (term0 A s x y)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3791010_term_abbrevs.
Lemma lem3791010 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term0 A B f s a b) = ((term1 A B f b s a) = (term2 A B s a b)).
Proof. exact (eq_refl (term0 A B f s a b)). Qed.

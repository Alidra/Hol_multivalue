Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3791025_term_abbrevs.
Lemma lem3791025 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term0 A B b s n a f) = ((term1 A B f b s a n) = (term2 A B b s n a f)).
Proof. exact (eq_refl (term0 A B b s n a f)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm48806_term_abbrevs.
Lemma lem48806 {A : Type'} (a : A) (b : A) : (term0 A a b) = ((a = b) = (@GEQ A a b)).
Proof. exact (eq_refl (term0 A a b)). Qed.

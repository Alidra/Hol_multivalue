Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1810_term_abbrevs.
Lemma lem1810 {A B : Type'} (f : A -> B) (y : A) : (term0 A B f y) = ((term1 A B f y) = (f y)).
Proof. exact (eq_refl (term0 A B f y)). Qed.

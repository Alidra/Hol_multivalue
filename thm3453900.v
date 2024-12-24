Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3453900_term_abbrevs.
Lemma lem3453900 {A : Type'} (s : type686 A) (x : A) : (term0 A s x) = ((term1 A x s) = (term2 A s x)).
Proof. exact (eq_refl (term0 A s x)). Qed.

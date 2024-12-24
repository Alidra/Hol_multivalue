Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20662_term_abbrevs.
Lemma lem20662 {A B : Type'} (f : A -> B) (x : A) : (term0 A B f x) = ((f x) = (@I (A -> B) f x)).
Proof. exact (eq_refl (term0 A B f x)). Qed.

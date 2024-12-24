Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17977_term_abbrevs.
Lemma lem17977 {A B : Type'} (t : A -> B) : (term0 A B t) = (t = (term1 A B t)).
Proof. exact (eq_refl (term0 A B t)). Qed.

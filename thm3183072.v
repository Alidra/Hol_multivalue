Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183072_term_abbrevs.
Lemma lem3183072 {A B : Type'} (f : A -> B) (g : A -> B) : (term0 A B f g) = ((f = g) = (term1 A B f g)).
Proof. exact (eq_refl (term0 A B f g)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm57692_term_abbrevs.
Lemma lem57692 {A B : Type'} (f : A -> B) (x : A) : (term0 A B f x) = ((@LET A B f x) = (f x)).
Proof. exact (eq_refl (term0 A B f x)). Qed.

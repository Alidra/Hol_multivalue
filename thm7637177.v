Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7637177_term_abbrevs.
Lemma lem7637177 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term0 A B f s n) = (term1 A B f s n).
Proof. exact (eq_refl (term0 A B f s n)). Qed.

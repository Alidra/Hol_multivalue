Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066569_term_abbrevs.
Lemma lem1066569 {A : Type'} (f : nat -> A) (a : A) : (term0 A a f) = ((term1 A a f) = a).
Proof. exact (eq_refl (term0 A a f)). Qed.

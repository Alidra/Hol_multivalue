Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066562_term_abbrevs.
Lemma lem1066562 {A : Type'} (a : A) (f : nat -> A) (n : nat) : (term0 A a f n) = ((term1 A a f n) = (f n)).
Proof. exact (eq_refl (term0 A a f n)). Qed.

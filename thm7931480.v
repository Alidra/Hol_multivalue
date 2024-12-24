Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7931480_term_abbrevs.
Lemma lem7931480 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) : (term0 A a a') = (((@mktybit0 A a) = (@mktybit0 A a')) = (a = a')).
Proof. exact (eq_refl (term0 A a a')). Qed.

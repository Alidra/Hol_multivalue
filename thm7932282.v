Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932282_term_abbrevs.
Lemma lem7932282 {A : Type'} (a : type6 A) (a' : type6 A) : (term0 A a a') = (((@mktybit1 A a) = (@mktybit1 A a')) = (a = a')).
Proof. exact (eq_refl (term0 A a a')). Qed.

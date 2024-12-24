Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7931479_term_abbrevs.
Require Import thm7928129_spec.
Lemma lem7931476 {A : Type'} (a : finite_sum A A) : term0 A a.
Proof. exact (@lem7928129 A a). Qed.
Lemma lem7931477 {A : Type'} (a : finite_sum A A) : (term0 A a) = (term1 A a).
Proof. exact (eq_refl (term0 A a)). Qed.
Lemma lem7931478 {A : Type'} (a : finite_sum A A) : term1 A a.
Proof. exact (EQ_MP (@lem7931477 A a) (@lem7931476 A a)). Qed.
Lemma lem7931479 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) : term2 A a a'.
Proof. exact (@lem7931478 A a a'). Qed.

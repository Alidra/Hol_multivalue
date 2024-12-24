Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932281_term_abbrevs.
Require Import thm7931456_spec.
Lemma lem7932278 {A : Type'} (a : type6 A) : term0 A a.
Proof. exact (@lem7931456 A a). Qed.
Lemma lem7932279 {A : Type'} (a : type6 A) : (term0 A a) = (term1 A a).
Proof. exact (eq_refl (term0 A a)). Qed.
Lemma lem7932280 {A : Type'} (a : type6 A) : term1 A a.
Proof. exact (EQ_MP (@lem7932279 A a) (@lem7932278 A a)). Qed.
Lemma lem7932281 {A : Type'} (a : type6 A) (a' : type6 A) : term2 A a a'.
Proof. exact (@lem7932280 A a a'). Qed.

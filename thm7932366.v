Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932366_term_abbrevs.
Require Import IN_UNIV_spec.
Lemma lem7932364 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem7932365 {A : Type'} (x : A) : (term0 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem7932366 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem7932365 A x) (@lem7932364 A x)). Qed.

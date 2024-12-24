Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1096523_term_abbrevs.
Require Import thm1096518_spec.
Lemma lem1096520 {A : Type'} (l : list A) : term0 A l.
Proof. exact (@lem1096518 A l). Qed.
Lemma lem1096521 {A : Type'} (l : list A) : (term0 A l) = (term1 A l).
Proof. exact (eq_refl (term0 A l)). Qed.
Lemma lem1096522 {A : Type'} (l : list A) : term1 A l.
Proof. exact (EQ_MP (@lem1096521 A l) (@lem1096520 A l)). Qed.
Lemma lem1096523 {A : Type'} (l : list A) (x : A) : term2 A l x.
Proof. exact (@lem1096522 A l x). Qed.

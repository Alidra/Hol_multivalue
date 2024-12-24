Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REVERSE_term_abbrevs.
Require Import thm1096519_spec.
Require Import thm1096523_spec.
Require Import thm1096524_spec.
Lemma lem1096525 {A : Type'} (l : list A) (x : A) : (term0 A x l) = (term1 A l x).
Proof. exact (EQ_MP (@lem1096524 A l x) (@lem1096523 A l x)). Qed.
Lemma lem1096526 {A : Type'} (l : list A) (x : A) : term2 A l x.
Proof. exact (conj (@lem1096519 A) (@lem1096525 A l x)). Qed.

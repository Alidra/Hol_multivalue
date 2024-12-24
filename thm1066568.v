Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066568_term_abbrevs.
Require Import thm1066089_spec.
Lemma lem1066564 {A : Type'} : term0 A.
Proof. exact (proj1 (@lem1066089 A)). Qed.
Lemma lem1066565 {A : Type'} (a : A) : term1 A a.
Proof. exact (@lem1066564 A a). Qed.
Lemma lem1066566 {A : Type'} (a : A) : (term1 A a) = (term2 A a).
Proof. exact (eq_refl (term1 A a)). Qed.
Lemma lem1066567 {A : Type'} (a : A) : term2 A a.
Proof. exact (EQ_MP (@lem1066566 A a) (@lem1066565 A a)). Qed.
Lemma lem1066568 {A : Type'} (a : A) (f : nat -> A) : term3 A a f.
Proof. exact (@lem1066567 A a f). Qed.

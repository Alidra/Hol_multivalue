Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066561_term_abbrevs.
Require Import thm1066089_spec.
Lemma lem1066554 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem1066089 A)). Qed.
Lemma lem1066555 {A : Type'} (a : A) : term1 A a.
Proof. exact (@lem1066554 A a). Qed.
Lemma lem1066556 {A : Type'} (a : A) : (term1 A a) = (term2 A a).
Proof. exact (eq_refl (term1 A a)). Qed.
Lemma lem1066557 {A : Type'} (a : A) : term2 A a.
Proof. exact (EQ_MP (@lem1066556 A a) (@lem1066555 A a)). Qed.
Lemma lem1066558 {A : Type'} (a : A) (f : nat -> A) : term3 A a f.
Proof. exact (@lem1066557 A a f). Qed.
Lemma lem1066559 {A : Type'} (a : A) (f : nat -> A) : (term3 A a f) = (term4 A a f).
Proof. exact (eq_refl (term3 A a f)). Qed.
Lemma lem1066560 {A : Type'} (a : A) (f : nat -> A) : term4 A a f.
Proof. exact (EQ_MP (@lem1066559 A a f) (@lem1066558 A a f)). Qed.
Lemma lem1066561 {A : Type'} (a : A) (f : nat -> A) (n : nat) : term5 A a f n.
Proof. exact (@lem1066560 A a f n). Qed.
